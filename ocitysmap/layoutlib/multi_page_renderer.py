# -*- coding: utf-8 -*-

# ocitysmap, city map and street index generator from OpenStreetMap data
# Copyright (C) 2012  David Mentré
# Copyright (C) 2012  Thomas Petazzoni
# Copyright (C) 2012  Gaël Utard
# Copyright (C) 2012  Étienne Loks

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of the
# License, or any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.

# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import cairo
import datetime
from itertools import groupby
import locale
import logging
import mapnik
assert mapnik.mapnik_version() >= 300000, \
    "Mapnik module version %s is too old, see ocitysmap's INSTALL " \
    "for more details." % mapnik.mapnik_version_string()
import math
import os
import gi
gi.require_version('Rsvg', '2.0')
gi.require_version('Pango', '1.0')
gi.require_version('PangoCairo', '1.0')
from gi.repository import Rsvg, Pango, PangoCairo
import shapely.wkt
import sys
from string import Template
from functools import cmp_to_key
from copy import copy

import ocitysmap
import coords
from . import commons
from ocitysmap.layoutlib.abstract_renderer import Renderer
from ocitysmap.indexlib.commons import StreetIndexCategory
from ocitysmap.indexlib.indexer import StreetIndex
from ocitysmap.indexlib.multi_page_renderer import MultiPageStreetIndexRenderer
from ocitysmap import draw_utils, maplib
from ocitysmap.maplib.map_canvas import MapCanvas
from ocitysmap.maplib.grid import Grid
from ocitysmap.maplib.overview_grid import OverviewGrid
from ocitysmap.stylelib import GpxStylesheet, UmapStylesheet

LOG = logging.getLogger('ocitysmap')

class MultiPageRenderer(Renderer):
    """
    This Renderer creates a multi-pages map, with all the classic overlayed
    features and no index page.
    """

    name = 'multi_page'
    description = 'A multi-page layout.'
    multipages = True

    GRAYED_MARGIN_TOP_BOTTOM_MM = 10
    GRAYED_MARGIN_INSIDE_MM = 3.3 + 15 # 3.3mm für Klebebindung + 15mm Abstand zum "Text" / zur Karte
    GRAYED_MARGIN_OUTSIDE_MM = 10

    OVERLAP_MARGIN_HOR_MM = 0
    OVERLAP_MARGIN_VERT_MM = 0

    MARKER_SIZE_MM = 25

    def __init__(self, db, rc, tmpdir, dpi, file_prefix):
        Renderer.__init__(self, db, rc, tmpdir, dpi)

        self._grid_legend_margin_pt = \
            min(Renderer.GRID_LEGEND_MARGIN_RATIO * self.paper_width_pt,
                Renderer.GRID_LEGEND_MARGIN_RATIO * self.paper_height_pt)

        overlap_margin_hor_pt = commons.convert_mm_to_pt(MultiPageRenderer.OVERLAP_MARGIN_HOR_MM)
        overlap_margin_vert_pt = commons.convert_mm_to_pt(MultiPageRenderer.OVERLAP_MARGIN_VERT_MM)

        self.grayed_margin_top_bottom_mm = MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM
        self.grayed_margin_top_bottom_pt = commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM)
        self.grayed_margin_inside_mm = MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM
        self.grayed_margin_inside_pt = commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM)
        self.grayed_margin_outside_mm = MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM
        self.grayed_margin_outside_pt = commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM)

        self.print_bleed_mm = commons.convert_pt_to_mm(Renderer.PRINT_BLEED_PT)
        self.print_bleed_pt = Renderer.PRINT_BLEED_PT

        self.marker_size_pt = commons.convert_mm_to_pt(MultiPageRenderer.MARKER_SIZE_MM)

        # Compute the usable area for the map per page
        self._usable_map_area_width_pt = self.paper_width_pt
        self._usable_map_area_height_pt = self.paper_height_pt

        self._visible_map_area_width_pt = self.paper_width_pt - 2*self.print_bleed_pt - self.grayed_margin_inside_pt - self.grayed_margin_outside_pt
        self._visible_map_area_height_pt = self.paper_height_pt - 2*self.print_bleed_pt - 2*self.grayed_margin_top_bottom_pt

        #self._map_coords = ( Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT,
        #                     Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT,
        #                     self._usable_map_area_width_pt,
        #                     self._usable_map_area_height_pt) 

        scale_denom = Renderer.DEFAULT_MULTIPAGE_SCALE

        # offset to the first map page number
        # there are currently three header pages
        # making the first actual map detail page number 4
        self._first_map_page_number = 4

        # the mapnik scale depends on the latitude. However we are
        # always using Mapnik conversion functions (lat,lon <->
        # mercator_meters) so we don't need to take into account
        # latitude in following computations

        # by convention, mapnik uses 90 ppi whereas cairo uses 72 ppi
        scale_denom *= float(72) / 90

        # Debug: show original bounding box as JS code
        print(self.rc.bounding_box.as_javascript("original", "#00ff00"))

        # Convert the original Bounding box into Mercator meters
        self._proj = mapnik.Projection(coords._MAPNIK_PROJECTION)
        orig_envelope = self._project_envelope(self.rc.bounding_box)

        while True:
            # Extend the bounding box to take into account the lost outer
            # margin
            off_x  = orig_envelope.minx #- (self.print_bleed_mm + ((MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM + MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM) / 2)) * 9.6
            off_y  = orig_envelope.miny #- MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM * 9.6
            width  = orig_envelope.width() #+ (MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM + MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM + 2*self.print_bleed_mm) * 9.6
            height = orig_envelope.height() #+ (2*MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM) * 9.6
            #print("orig_envelope.minx", orig_envelope.minx, "orign_envelope.miny", orig_envelope.miny, "orig_envelope.width", orig_envelope.width(), "orig_envelope.height", orig_envelope.height())
            # Calculate the total width and height of paper needed to
            # render the geographical area at the current scale.
            #print("needed papersize in mm", float(width) * 1000 / scale_denom, float(height) * 1000 / scale_denom)
            total_width_pt   = commons.convert_mm_to_pt(float(width) * 1000 / scale_denom)
            total_height_pt  = commons.convert_mm_to_pt(float(height) * 1000 / scale_denom)

            # Calculate the number of pages needed in both directions
            if total_width_pt < self._visible_map_area_width_pt:
                nb_pages_width = 1
            else:
                nb_pages_width = float(total_width_pt) / self._visible_map_area_width_pt
#                nb_pages_width = \
#                    (float(total_width_pt - self._visible_map_area_width_pt) / \
#                         (self._visible_map_area_width_pt - overlap_margin_hor_pt)) + 1

            if total_height_pt < self._visible_map_area_height_pt:
                nb_pages_height = 1
            else:
                nb_pages_height = \
                    (float(total_height_pt - self._visible_map_area_height_pt) / \
                         (self._visible_map_area_height_pt - overlap_margin_vert_pt)) + 1

            print("total size: ", total_width_pt, total_height_pt)
            print("page size: ", self._visible_map_area_width_pt, self._visible_map_area_height_pt)
            print("needed pages: ", nb_pages_width, nb_pages_height)

            # Round up the number of pages needed so that we have integer
            # number of pages
            self.nb_pages_width = int(math.ceil(nb_pages_width))
            self.nb_pages_height = int(math.ceil(nb_pages_height))
            print("needed pages: ", self.nb_pages_width, self.nb_pages_height)

            total_pages = self.nb_pages_width * self.nb_pages_height

            if Renderer.MAX_MULTIPAGE_MAPPAGES and \
               total_pages < Renderer.MAX_MULTIPAGE_MAPPAGES:
                break

            new_scale_denom = scale_denom * 1.41

            if new_scale_denom > Renderer.DEFAULT_SCALE:
                break

            scale_denom = new_scale_denom

        # Calculate the entire paper area available
        total_width_pt_after_extension = self._visible_map_area_width_pt + \
            (self._visible_map_area_width_pt - overlap_margin_hor_pt) * (self.nb_pages_width - 1)
        total_height_pt_after_extension = self._visible_map_area_height_pt + \
            (self._visible_map_area_height_pt - overlap_margin_vert_pt) * (self.nb_pages_height - 1)

        # Convert this paper area available in the number of Mercator
        # meters that can be rendered on the map
        total_width_merc = \
            commons.convert_pt_to_mm(total_width_pt_after_extension) * scale_denom / 1000
        total_height_merc = \
            commons.convert_pt_to_mm(total_height_pt_after_extension) * scale_denom / 1000

        # Extend the geographical boundaries so that we completely
        # fill the available paper size. We are careful to extend the
        # boundaries evenly on all directions (so the center of the
        # previous boundaries remain the same as the new one)
        off_x -= (total_width_merc - width) / 2
        width = total_width_merc
        off_y -= (total_height_merc - height) / 2
        height = total_height_merc

        envelope = mapnik.Box2d(off_x, off_y, off_x + width, off_y + height)

        self._geo_bbox = self._inverse_envelope(envelope)

        # Debug: show transformed bounding box as JS code
        print(self._geo_bbox.as_javascript("extended", "#0f0f0f"))

        # Convert the usable area on each sheet of paper into the
        # amount of Mercator meters we can render in this area.
        usable_area_merc_m_width  = commons.convert_pt_to_mm(self._usable_map_area_width_pt) * scale_denom / 1000
        usable_area_merc_m_height = commons.convert_pt_to_mm(self._usable_map_area_height_pt) * scale_denom / 1000

        grayed_margin_top_bottom_merc_m = (self.grayed_margin_top_bottom_mm * scale_denom) / 1000
        grayed_margin_inside_merc_m = (MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM * scale_denom) / 1000
        grayed_margin_outside_merc_m = (MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM * scale_denom) / 1000

        print_bleed_merc_m = (self.print_bleed_mm * scale_denom) / 1000

        overlap_margin_hor_merc_m = (MultiPageRenderer.OVERLAP_MARGIN_HOR_MM * scale_denom) / 1000
        overlap_margin_vert_merc_m = (MultiPageRenderer.OVERLAP_MARGIN_VERT_MM * scale_denom) / 1000

        # Calculate all the bounding boxes that correspond to the
        # geographical area that will be rendered on each sheet of
        # paper.
        area_polygon = shapely.wkt.loads(self.rc.polygon_wkt)
        bboxes = []
        self.page_disposition, map_number = {}, 0
        for j in reversed(range(0, self.nb_pages_height)):
            row = self.nb_pages_height - j - 1
            self.page_disposition[row] = []
            for i in range(0, self.nb_pages_width):
                cur_x = off_x + \
                    i * (usable_area_merc_m_width - 2*print_bleed_merc_m - grayed_margin_inside_merc_m - grayed_margin_outside_merc_m) \
                    - print_bleed_merc_m - grayed_margin_inside_merc_m - grayed_margin_outside_merc_m \
                    + (grayed_margin_outside_merc_m if (map_number + self._first_map_page_number) % 2 else grayed_margin_inside_merc_m)
                cur_y = off_y + \
                    j * (usable_area_merc_m_height - 2*print_bleed_merc_m - 2*grayed_margin_top_bottom_merc_m) \
                    - print_bleed_merc_m - grayed_margin_top_bottom_merc_m
                #print("page", (self._first_map_page_number + map_number), row, "col", i, "row", j, "{:10.4f}".format(cur_x), "{:10.4f}".format(cur_x - off_x), "{:10.4f}".format(cur_y), "{:10.4f}".format(cur_y - off_y))
                envelope = mapnik.Box2d(cur_x, cur_y,
                                        cur_x+usable_area_merc_m_width,
                                        cur_y+usable_area_merc_m_height)

                envelope_inner = mapnik.Box2d(cur_x + print_bleed_merc_m + (grayed_margin_inside_merc_m if (self._first_map_page_number + map_number) % 2 else grayed_margin_outside_merc_m),
                                              cur_y + print_bleed_merc_m + grayed_margin_top_bottom_merc_m,
                                              cur_x + usable_area_merc_m_width - print_bleed_merc_m - (grayed_margin_outside_merc_m if (map_number + self._first_map_page_number) % 2 else grayed_margin_inside_merc_m),
                                              cur_y + usable_area_merc_m_height - print_bleed_merc_m - grayed_margin_top_bottom_merc_m)
                inner_bb = self._inverse_envelope(envelope_inner)
                if not area_polygon.disjoint(shapely.wkt.loads(inner_bb.as_wkt())):
                    self.page_disposition[row].append(map_number)
                    map_number += 1
                    bboxes.append((self._inverse_envelope(envelope), inner_bb))
                else:
                    self.page_disposition[row].append(None)

        # Debug: show per-page bounding boxes as JS code
        for i, (bb, bb_inner) in enumerate(bboxes):
           print(bb_inner.as_javascript(name="p%d" % i))

        self.pages = []

        overview_topleft = self._geo_bbox.get_top_left()
        overview_bottomright = self._geo_bbox.get_bottom_right()
        overview_lat_abs = math.fabs(overview_topleft[0]-overview_bottomright[0])
        overview_lng_abs = math.fabs(overview_topleft[1]-overview_bottomright[1])
        print("topleft", overview_topleft, "bottomright", overview_bottomright, "lat_abs", overview_lat_abs, "1ng_abs", overview_lng_abs)
        overview_left_pad = overview_lat_abs/self._usable_map_area_width_pt * (self.grayed_margin_inside_pt + self.print_bleed_pt)
        overview_right_pad = overview_lat_abs/self._usable_map_area_width_pt * (self.grayed_margin_outside_pt + self.print_bleed_pt)
        overview_topbottom_pad = overview_lng_abs/self._usable_map_area_width_pt * (self.grayed_margin_top_bottom_pt + self.print_bleed_pt)
        print(overview_left_pad, overview_right_pad, overview_topbottom_pad)
        
        # Create an overview map (top, left, bottom, right)
        overview_bb = self._geo_bbox.create_expanded2(overview_topbottom_pad, overview_left_pad, overview_topbottom_pad, overview_right_pad)
        print(overview_bb.as_javascript("overview", "#f0c003"))
        # Create the overview grid
        self.overview_grid = OverviewGrid(overview_bb,
                     [bb_inner for bb, bb_inner in bboxes], self.rc.i18n.isrtl())

        grid_shape = self.overview_grid.generate_shape_file(
                    os.path.join(self.tmpdir, 'grid_overview.shp'))

        # Create a canvas for the overview page
        self.overview_canvas = MapCanvas(self.rc.stylesheet,
                               overview_bb, self._usable_map_area_width_pt,
                               self._usable_map_area_height_pt, dpi,
                               extend_bbox_to_ratio=True)

        # Create the gray shape around the overview map
        exterior = shapely.wkt.loads(self.overview_canvas.get_actual_bounding_box()\
                                                                .as_wkt())
        interior = shapely.wkt.loads(self.rc.polygon_wkt)
        #DEBUG: print whole city als wkt-string
        #print("WktString('%s', 'whole-shape')" % interior)

        shade_wkt = exterior.difference(interior).wkt
        shade = maplib.shapes.PolyShapeFile(self.rc.bounding_box,
                os.path.join(self.tmpdir, 'shape_overview.shp'),
                             'shade-overview')
        shade.add_shade_from_wkt(shade_wkt)

        if self.rc.osmids != None:
            self.overview_canvas.add_shape_file(shade)
        self.overview_canvas.add_shape_file(grid_shape,
                                  self.rc.stylesheet.grid_line_color, 1,
                                  self.rc.stylesheet.grid_line_width)

        self.overview_canvas.render()

        self._overlays = copy(self.rc.overlays)
        
        # generate style file for GPX file
        if self.rc.gpx_file:
            self._overlays.append(GpxStylesheet(self.rc.gpx_file, self.tmpdir))

        # denormalize UMAP json to geojson, then create style for it
        if self.rc.umap_file:
            self._overlays.append(UmapStylesheet(self.rc.umap_file, self.tmpdir))

        self.overview_overlay_canvases = []
        self.overview_overlay_effects = []
        
        for overlay in self._overlays:
            path = overlay.path.strip()
            if path.startswith('internal:'):
                self.overview_overlay_effects.append(path.lstrip('internal:'))
            else:
                ov_canvas = MapCanvas(overlay,
                                      overview_bb,
                                      self._usable_map_area_width_pt,
                                      self._usable_map_area_height_pt,
                                      dpi,
                                      extend_bbox_to_ratio=True)
                ov_canvas.render()
                self.overview_overlay_canvases.append(ov_canvas)

        # Create the map canvas for each page
        indexes = dict()
        #LOG.debug(self.rc.name_to_polygon)
        if self.rc.name_to_polygon:
            for name in self.rc.name_to_polygon:
                indexes[name] = []
        else:
            indexes['none'] = []

        for i, (bb, bb_inner) in enumerate(bboxes):
            # print(bb.as_javascript(name="p%d - bb" % i))
            # print(bb_inner.as_javascript(name="p%d - bb_inner" % i))

            # Create the gray shape around the map
            exterior = shapely.wkt.loads(bb.as_wkt())
            interior = shapely.wkt.loads(bb_inner.as_wkt())
            shade_wkt = exterior.difference(interior).wkt
            shade = maplib.shapes.PolyShapeFile(
                bb, os.path.join(self.tmpdir, 'shade%d.shp' % i),
                'shade%d' % i)
            shade.add_shade_from_wkt(shade_wkt)

            # Create the contour shade

            # Area to keep visible
            interior_contour = shapely.wkt.loads(self.rc.polygon_wkt)
            # Determine the shade WKT
            shade_contour_wkt = interior.difference(interior_contour).wkt
            # Prepare the shade SHP
            shade_contour = maplib.shapes.PolyShapeFile(bb,
                os.path.join(self.tmpdir, 'shade_contour%d.shp' % i),
                'shade_contour%d' % i)
            shade_contour.add_shade_from_wkt(shade_contour_wkt)


            # Create one canvas for the current page
            map_canvas = MapCanvas(self.rc.stylesheet,
                                   bb, self._usable_map_area_width_pt,
                                   self._usable_map_area_height_pt, dpi,
                                   extend_bbox_to_ratio=False)

            # Create canvas for overlay on current page
            overlay_canvases = []
            overlay_effects  = []
            for overlay in self._overlays:
                path = overlay.path.strip()
                if path.startswith('internal:'):
                    overlay_effects.append(path.lstrip('internal:'))
                else:
                    overlay_canvases.append(MapCanvas(overlay,
                                               bb, self._usable_map_area_width_pt,
                                               self._usable_map_area_height_pt, dpi,
                                               extend_bbox_to_ratio=False))

            # Create the grid
            map_grid = Grid(bb_inner, map_canvas.get_actual_scale(), self.rc.i18n.isrtl())
            grid_shape = map_grid.generate_shape_file(
                os.path.join(self.tmpdir, 'grid%d.shp' % i))

            map_canvas.add_shape_file(shade)
            if self.rc.osmids != None:
                map_canvas.add_shape_file(shade_contour,
                                          self.rc.stylesheet.shade_color_2,
                                          self.rc.stylesheet.shade_alpha_2)
            map_canvas.add_shape_file(grid_shape,
                                      self.rc.stylesheet.grid_line_color,
                                      self.rc.stylesheet.grid_line_alpha,
                                      self.rc.stylesheet.grid_line_width)

            map_canvas.render()

            for overlay_canvas in overlay_canvases:
                overlay_canvas.render()

            self.pages.append((map_canvas, map_grid, overlay_canvases, overlay_effects))

            if self.rc.name_to_polygon:
                for name in self.rc.name_to_polygon:
                    inside_contour_wkt = interior_contour.intersection(interior).intersection(self.rc.name_to_polygon[name])
                    if not inside_contour_wkt.is_empty:
                        # Create the index for the current page
                        # inside_contour_wkt = interior_contour.intersection(interior).wkt
                        #LOG.debug("WktString('%s', 'inside_contour_wkt %d')" % (inside_contour_wkt, i) )

                        index = StreetIndex(self.db,
                                        inside_contour_wkt,
                                        self.rc.i18n, page_number=(i + self._first_map_page_number))

                        index.apply_grid(map_grid)
                        indexes[name].append(index)

        # Merge all indexes
        self.index_categories = dict()
        if self.rc.name_to_polygon:
            for name in self.rc.name_to_polygon:
                self.index_categories[name] = self._merge_page_indexes(indexes[name])

        # Prepare the small map for the front page
        self._prepare_front_page_map(dpi)

    def _merge_page_indexes(self, indexes):
        # First, we split street categories and "other" categories,
        # because we sort them and we don't want to have the "other"
        # categories intermixed with the street categories. This
        # sorting is required for the groupby Python operator to work
        # properly.
        all_categories_streets = []
        all_categories_others  = []
        for page_number, idx in enumerate(indexes):
            for cat in idx.categories:
                # Split in two lists depending on the category type
                # (street or other)
                if cat.is_street:
                    all_categories_streets.append(cat)
                else:
                    all_categories_others.append(cat)

        all_categories_streets_merged = \
            self._merge_index_same_categories(all_categories_streets, is_street=True)
        all_categories_others_merged = \
            self._merge_index_same_categories(all_categories_others, is_street=False)

        all_categories_merged = \
            all_categories_streets_merged + all_categories_others_merged

        return all_categories_merged

    def _my_cmp(self, x, y):
        return locale.strcoll(x.label, y.label)

    def _merge_index_same_categories(self, categories, is_street=True):
        # Sort by categories. Now we may have several consecutive
        # categories with the same name (i.e category for letter 'A'
        # from page 1, category for letter 'A' from page 3).
        categories.sort(key=lambda s:s.name)

        categories_merged = []
        for category_name,grouped_categories in groupby(categories,
                                                        key=lambda s:s.name):

            # Group the different IndexItem from categories having the
            # same name. The groupby() function guarantees us that
            # categories with the same name are grouped together in
            # grouped_categories[].

            grouped_items = []
            for cat in grouped_categories:
                grouped_items.extend(cat.items)

            # Re-sort alphabetically all the IndexItem according to
            # the street name.

            prev_locale = locale.getlocale(locale.LC_COLLATE)
            try:
                locale.setlocale(locale.LC_COLLATE, self.rc.i18n.language_code())
            except Exception:
                l.warning('error while setting LC_COLLATE to "%s"' % self._i18n.language_code())

            try:
                grouped_items_sorted = \
                    sorted(grouped_items, key = cmp_to_key(self._my_cmp))        
            finally:
                locale.setlocale(locale.LC_COLLATE, prev_locale)

            self._blank_duplicated_names(grouped_items_sorted)

            # Rebuild a IndexCategory object with the list of merged
            # and sorted IndexItem
            categories_merged.append(
                StreetIndexCategory(category_name, grouped_items_sorted, is_street))

        return categories_merged

    # We set the label to empty string in case of duplicated item. In
    # multi-page renderer we won't draw the dots in that case
    def _blank_duplicated_names(self, grouped_items_sorted):
        prev_label = ''
        for item in grouped_items_sorted:
            if prev_label == item.label:
                item.label = ''
            else:
                prev_label = item.label

    def _project_envelope(self, bbox):
        """Project the given bounding box into the rendering projection."""
        envelope = mapnik.Box2d(bbox.get_top_left()[1],
                                bbox.get_top_left()[0],
                                bbox.get_bottom_right()[1],
                                bbox.get_bottom_right()[0])
        c0 = self._proj.forward(mapnik.Coord(envelope.minx, envelope.miny))
        c1 = self._proj.forward(mapnik.Coord(envelope.maxx, envelope.maxy))
        return mapnik.Box2d(c0.x, c0.y, c1.x, c1.y)

    def _inverse_envelope(self, envelope):
        """Inverse the given cartesian envelope (in 3587) back to a 4326
        bounding box."""
        c0 = self._proj.inverse(mapnik.Coord(envelope.minx, envelope.miny))
        c1 = self._proj.inverse(mapnik.Coord(envelope.maxx, envelope.maxy))
        return coords.BoundingBox(c0.y, c0.x, c1.y, c1.x)

    def _prepare_front_page_map(self, dpi):
        front_page_map_w = \
            self._usable_map_area_width_pt - 2 * Renderer.LAYOUT_MARGIN_PT
        front_page_map_h = \
            (self._usable_map_area_height_pt - 2 * Renderer.LAYOUT_MARGIN_PT) / 2

        # Create the nice small map
        front_page_map = \
            MapCanvas(self.rc.stylesheet,
                      self.rc.bounding_box,
                      front_page_map_w,
                      front_page_map_h,
                      dpi,
                      extend_bbox_to_ratio=True)

        # Add the shape that greys out everything that is outside of
        # the administrative boundary.
        exterior = shapely.wkt.loads(front_page_map.get_actual_bounding_box().as_wkt())
        interior = shapely.wkt.loads(self.rc.polygon_wkt)
        shade_wkt = exterior.difference(interior).wkt
        shade = maplib.shapes.PolyShapeFile(self.rc.bounding_box,
                os.path.join(self.tmpdir, 'shape_overview_cover.shp'),
                             'shade-overview-cover')
        shade.add_shade_from_wkt(shade_wkt)
        front_page_map.add_shape_file(shade)
        front_page_map.render()
        self._front_page_map = front_page_map

        self._frontpage_overlay_canvases = []
        self._frontpage_overlay_effects  = []
        for overlay in self._overlays:
            path = overlay.path.strip()
            if path.startswith('internal:'):
                self._frontpage_overlay_effects.append(path.lstrip('internal:'))
            else:
                ov_canvas = MapCanvas(overlay,
                                      self.rc.bounding_box,
                                      front_page_map_w,
                                      front_page_map_h,
                                      dpi,
                                      extend_bbox_to_ratio=True)
                ov_canvas.render()
                self._frontpage_overlay_canvases.append(ov_canvas)

    def _render_front_page_header(self, ctx, w, h):
        # Draw a grey blue block which will contain the name of the
        # city being rendered.
        ctx.save()
        blue_w = w
        blue_h = 0.3 * h
        ctx.set_source_rgb(.80,.80,.80)
        ctx.rectangle(0, 0, blue_w, blue_h)
        ctx.fill()
        draw_utils.draw_text_adjusted(ctx, self.rc.title, blue_w/2, blue_h/2,
                 blue_w, blue_h)
        ctx.restore()

    def _render_front_page_map(self, ctx, dpi, w, h):
        # We will render the map slightly below the title
        ctx.save()
        ctx.translate(0, 0.3 * h + Renderer.LAYOUT_MARGIN_PT)

        # prevent map background from filling the full canvas
        ctx.rectangle(0, 0, w, h / 2)
        ctx.clip()

        # Render the map !
        mapnik.render(self._front_page_map.get_rendered_map(), ctx)
        
        for ov_canvas in self._frontpage_overlay_canvases:
            rendered_map = ov_canvas.get_rendered_map()
            mapnik.render(rendered_map, ctx)

        # apply effect overlays
        ctx.save()
        # we have to undo border adjustments here
        ctx.translate(0, -(0.3 * h + Renderer.LAYOUT_MARGIN_PT))
        self._map_canvas = self._front_page_map;
        for effect in self._frontpage_overlay_effects:
            self.render_plugin(effect, ctx)
        ctx.restore()

        ctx.restore()

    def _render_front_page_footer(self, ctx, w, h, osm_date):
        ctx.save()

        # Draw the footer
        ctx.translate(0, 0.8 * h + 2 * Renderer.LAYOUT_MARGIN_PT)

        # Display a nice grey rectangle as the background of the
        # footer
        footer_w = w
        footer_h = 0.2 * h - 2 * Renderer.LAYOUT_MARGIN_PT
        ctx.set_source_rgb(.80,.80,.80)
        ctx.rectangle(0, 0, footer_w, footer_h)
        ctx.fill()

        # Draw the OpenStreetMap logo to the right of the footer
        logo_height = footer_h / 2
        grp, logo_width = self._get_osm_logo(ctx, logo_height)
        if grp:
            ctx.save()
            ctx.translate(w - logo_width - Renderer.LAYOUT_MARGIN_PT,
                          logo_height / 2)
            ctx.set_source(grp)
            ctx.paint_with_alpha(1)
            ctx.restore()

        # Prepare the text for the left of the footer
        today = datetime.date.today()
        notice = _(u'Copyright © %(year)d MapOSMatic/OCitySMap developers.')
        notice+= '\n\n\n'
        notice+= _(u'Map data © %(year)d OpenStreetMap contributors (see http://osm.org/copyright)')
        notice+= '\n'
        annotations = []

        if self.rc.stylesheet.annotation != '':
            annotations.append(self.rc.stylesheet.annotation)
            for overlay in self._overlays:
                if overlay.annotation != '':
                    annotations.append(overlay.annotation)
        if len(annotations) > 0:
            notice+= _(u'Map styles:')
            notice+= ' ' + '; '.join(annotations) + '\n'

        notice+= _(u'Map rendered on: %(date)s. OSM data updated on: %(osmdate)s.')
        notice+= '\n'
        notice+= _(u'The map may be incomplete or inaccurate.')

        # We need the correct locale to be set for strftime().
        prev_locale = locale.getlocale(locale.LC_TIME)
        locale.setlocale(locale.LC_TIME, self.rc.i18n.language_code())
        try:
            if osm_date is None:
                osm_date_str = _(u'unknown')
            else:
                osm_date_str = osm_date.strftime("%d.%m.%y %H:%M")

            notice = notice % {'year': today.year,
                               'date': today.strftime("%d.%m.%y"),
                               'osmdate': osm_date_str}
        finally:
            locale.setlocale(locale.LC_TIME, prev_locale)

        draw_utils.draw_text_adjusted(ctx, notice,
                Renderer.LAYOUT_MARGIN_PT, footer_h/2, footer_w - logo_width - 3*Renderer.LAYOUT_MARGIN_PT,
                footer_h, align=Pango.Alignment.LEFT, width_adjust=1, height_adjust=0.8)
        ctx.restore()

    def _render_front_page(self, ctx, cairo_surface, dpi, osm_date):
        # Draw a nice grey rectangle covering the whole page
        ctx.save()
        ctx.set_source_rgb(.95,.95,.95)
        ctx.rectangle(0, 0, self.paper_width_pt, self.paper_height_pt)
        ctx.fill()
        ctx.restore()

        # Translate into the working area, taking 
        # LAYOUT_MARGIN_PT inside the grey area.
        ctx.save()
        ctx.translate(Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT + Renderer.LAYOUT_MARGIN_PT,
                      Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT + Renderer.LAYOUT_MARGIN_PT)
        w = self.paper_width_pt - 2 * Renderer.LAYOUT_MARGIN_PT - 2 * Renderer.PRINT_BLEED_PT
        h = self.paper_height_pt - 2 * Renderer.LAYOUT_MARGIN_PT - 2 * Renderer.PRINT_BLEED_PT

        self._render_front_page_map(ctx, dpi, w, h)
        self._render_front_page_header(ctx, w, h)
        self._render_front_page_footer(ctx, w, h, osm_date)

        ctx.restore()

        cairo_surface.set_page_label('Front page')
        cairo_surface.show_page()

    def _render_blank_page(self, ctx, cairo_surface, dpi, page):
        """
        Render a blank page with a nice "intentionally blank" notice
        """
        ctx.save()
        ctx.translate(
                commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT),
                commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT))

        # temp: show area without bleed-difference
        ctx.save()
        ctx.set_source_rgb(.95,.95,.95)
        ctx.rectangle(
            Renderer.PRINT_BLEED_PT + Renderer.PRINT_SAFE_MARGIN_PT,
            Renderer.PRINT_BLEED_PT + Renderer.PRINT_SAFE_MARGIN_PT,
            self.paper_width_pt - 2*Renderer.PRINT_BLEED_PT - 2*Renderer.PRINT_SAFE_MARGIN_PT,
            self.paper_height_pt - 2*Renderer.PRINT_BLEED_PT - 2*Renderer.PRINT_SAFE_MARGIN_PT)
        ctx.fill()
        ctx.restore()

        # temp: show content-area (inside grayed margin)
        ctx.save()
        ctx.set_source_rgb(.85,.85,.85)
        ctx.rectangle(
            Renderer.PRINT_BLEED_PT + Renderer.PRINT_SAFE_MARGIN_PT + commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM if page % 2 else MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM),
            Renderer.PRINT_BLEED_PT + Renderer.PRINT_SAFE_MARGIN_PT + commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM),
            self.paper_width_pt - 2*Renderer.PRINT_BLEED_PT - 2*Renderer.PRINT_SAFE_MARGIN_PT - commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM + MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM),
            self.paper_height_pt - 2*Renderer.PRINT_BLEED_PT - 2*Renderer.PRINT_SAFE_MARGIN_PT - 2*commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM))
        ctx.fill()
        ctx.restore()

        # footer notice
        content_width = self.paper_width_pt - 2*Renderer.PRINT_BLEED_PT - commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM + MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM)
        x = Renderer.PRINT_BLEED_PT + commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM if page % 2 else MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM) + (content_width/2)
        y = self.paper_height_pt - Renderer.PRINT_BLEED_PT - Renderer.PRINT_SAFE_MARGIN_PT - commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM/2)
        ctx.set_source_rgb(.6,.6,.6)
        draw_utils.draw_simpletext_center(ctx, _('This page is intentionally left '\
                                            'blank.'), x, y)
        draw_utils.render_page_number(ctx, page,
                                      self.paper_width_pt,
                                      self.paper_height_pt,
                                      transparent_background=False,
                                      margin_inside_pt = self.grayed_margin_inside_pt,
                                      margin_outside_pt = self.grayed_margin_outside_pt,
                                      margin_top_bottom_pt = self.grayed_margin_top_bottom_pt,
                                      print_bleed_pt = self.print_bleed_pt)
        cairo_surface.set_page_label('Blank')
        cairo_surface.show_page()
        ctx.restore()

    def _render_overview_page(self, ctx, cairo_surface, dpi):
        rendered_map = self.overview_canvas.get_rendered_map()

        ctx.save()

        #ctx.translate(
        #   commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT + MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM),
        #   commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT))
        #ctx.rectangle(0, 0, self._usable_map_area_width_pt, self._usable_map_area_height_pt)
        #ctx.clip()
        
        mapnik.render(rendered_map, ctx)

        for ov_canvas in self.overview_overlay_canvases:
            rendered_map = ov_canvas.get_rendered_map()
            mapnik.render(rendered_map, ctx)

        # apply effect overlays
        ctx.save()
        # we have to undo border adjustments here
        #ctx.translate(
        #        -commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT + Renderer.BINDING_MARGIN_PT),
        #        -commons.convert_pt_to_dots(Renderer.PRINT_SAFE_MARGIN_PT + Renderer.PRINT_BLEED_PT))

        self._map_canvas = self.overview_canvas;
        for effect in self.overview_overlay_effects:
            self.render_plugin(effect, ctx)
        ctx.restore()

        # draw pages numbers
        self._draw_overview_labels(ctx, self.overview_canvas, self.overview_grid,
              commons.convert_pt_to_dots(self._usable_map_area_width_pt),
              commons.convert_pt_to_dots(self._usable_map_area_height_pt))
        # Render the page number
        draw_utils.render_page_number(ctx, 3,
                                      self._usable_map_area_width_pt,
                                      self._usable_map_area_height_pt,
                                      self.grayed_margin_inside_pt,
                                      self.grayed_margin_outside_pt,
                                      self.grayed_margin_top_bottom_pt,
                                      self.print_bleed_pt,
                                      transparent_background = True)

        ctx.restore()
        cairo_surface.set_page_label('Overview')
        cairo_surface.show_page()

    def _draw_arrow(self, ctx, cairo_surface, number, max_digit_number, rotate_text = 0):
        arrow_edge = self.marker_size_pt*0.3
        ctx.save()
        ctx.set_source_rgb(0, 0, 0)
        ctx.translate(-arrow_edge/2, -arrow_edge*0.45)

        dest_name = "mypage%d" % number
        draw_utils.begin_internal_link(ctx, dest_name)

        ctx.line_to(0, 0)
        ctx.line_to(0, arrow_edge)
        ctx.line_to(arrow_edge, arrow_edge)
        ctx.line_to(arrow_edge, 0)
        ctx.line_to(arrow_edge/2, -arrow_edge*.25)
        ctx.close_path()
        ctx.fill()
        draw_utils.end_link(ctx)
        ctx.restore()

        ctx.save()
        ctx.rotate(rotate_text)
        draw_utils.begin_internal_link(ctx, dest_name)
        draw_utils.draw_text_adjusted(ctx, str(number), 0, 0, arrow_edge,
                        arrow_edge, max_char_number=max_digit_number,
                        text_color=(1, 1, 1, 1), width_adjust=0.85,
                        height_adjust=0.9)
        draw_utils.end_link(ctx)
        ctx.restore()

    def _render_neighbour_arrows(self, ctx, cairo_surface, map_number,
                                 max_digit_number):
        current_line, current_col = None, None
        for line_nb in range(self.nb_pages_height):
            if map_number in self.page_disposition[line_nb]:
                current_line = line_nb
                current_col = self.page_disposition[line_nb].index(map_number)
                break
        if current_line == None:
            # page not referenced
            return

        innerbb_width = self.paper_width_pt - commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM + MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM) - 2*Renderer.PRINT_BLEED_PT
        horizontal_center = Renderer.PRINT_BLEED_PT + commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM if map_number % 2 else MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM) + (innerbb_width/2)

        # north arrow
        for line_nb in reversed(range(current_line)):
            if self.page_disposition[line_nb][current_col] != None:
                north_arrow = self.page_disposition[line_nb][current_col]
                ctx.save()
                ctx.translate(horizontal_center,
                    Renderer.PRINT_BLEED_PT + commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM) - self.marker_size_pt*0.3*0.5)
                self._draw_arrow(ctx, cairo_surface,
                              north_arrow + self._first_map_page_number, max_digit_number)
                ctx.restore()
                break

        # south arrow
        for line_nb in range(current_line + 1, self.nb_pages_height):
            if self.page_disposition[line_nb][current_col] != None:
                south_arrow = self.page_disposition[line_nb][current_col]
                ctx.save()
                ctx.translate(horizontal_center,
                     self._usable_map_area_height_pt \
                      - Renderer.PRINT_BLEED_PT \
                      - commons.convert_mm_to_pt(MultiPageRenderer.GRAYED_MARGIN_TOP_BOTTOM_MM)\
                      + self.marker_size_pt*0.3*0.5)
                ctx.rotate(math.pi)
                self._draw_arrow(ctx, cairo_surface,
                      south_arrow + self._first_map_page_number, max_digit_number,
                      rotate_text=math.pi)
                ctx.restore()
                break

        # west arrow
        for col_nb in reversed(range(0, current_col)):
            if self.page_disposition[current_line][col_nb] != None:
                west_arrow = self.page_disposition[current_line][col_nb]
                ctx.save()
                ctx.translate(Renderer.PRINT_BLEED_PT \
                         + commons.convert_mm_to_pt((MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM if map_number % 2 else MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM)) \
                         - self.marker_size_pt*0.3*0.5,
                    self._usable_map_area_height_pt/2)
                ctx.rotate(-math.pi/2)
                self._draw_arrow(ctx, cairo_surface,
                               west_arrow + self._first_map_page_number, max_digit_number,
                               rotate_text=math.pi/2)
                ctx.restore()
                break

        # east arrow
        for col_nb in range(current_col + 1, self.nb_pages_width):
            if self.page_disposition[current_line][col_nb] != None:
                east_arrow = self.page_disposition[current_line][col_nb]
                ctx.save()
                ctx.translate(self._usable_map_area_width_pt - Renderer.PRINT_BLEED_PT \
                         - commons.convert_mm_to_pt((MultiPageRenderer.GRAYED_MARGIN_OUTSIDE_MM if map_number % 2 else MultiPageRenderer.GRAYED_MARGIN_INSIDE_MM)) \
                         + self.marker_size_pt*0.3*0.5,
                    self._usable_map_area_height_pt/2)
                ctx.rotate(math.pi/2)
                self._draw_arrow(ctx, cairo_surface,
                               east_arrow + self._first_map_page_number, max_digit_number,
                               rotate_text=-math.pi/2)
                ctx.restore()
                break

    @staticmethod
    def _draw_labels(ctx, map_grid,
                     map_area_width_dots, map_area_height_dots,
                     grid_legend_margin_dots):
        """
        Draw the Grid labels at current position.

        Args:
           ctx (cairo.Context): The cairo context to use to draw.
           map_grid (Grid): the grid objects whose labels we want to draw.
           map_area_width_dots/map_area_height_dots (numbers): size of the
              map (cairo units).
           grid_legend_margin_dots (number): margin between border of
              map and grid labels (cairo units).
        """
        ctx.save()

        ctx.set_source_rgba(0, 0, 0, 0.7);

        step_horiz = map_area_width_dots / map_grid.horiz_count
        last_horiz_portion = math.modf(map_grid.horiz_count)[0]

        step_vert = map_area_height_dots / map_grid.vert_count
        last_vert_portion = math.modf(map_grid.vert_count)[0]

        ctx.set_font_size(min(0.75 * grid_legend_margin_dots,
                              0.5 * step_horiz))
        ctx.set_source_rgba(0, 0, 0, 1)

        # TODO labels can overlap with next page arrows,
        # if they do -> hide them? or move them out of the
        # grid center a bit?

        for i, label in enumerate(map_grid.horizontal_labels):
            x = i * step_horiz

            if i < len(map_grid.horizontal_labels) - 1:
                x += step_horiz/2.0
            elif last_horiz_portion >= 0.3:
                x += step_horiz * last_horiz_portion/2.0
            else:
                continue

            draw_utils.draw_halotext_center(ctx, label,
                                            x, - grid_legend_margin_dots/1.0)

            draw_utils.draw_halotext_center(ctx, label,
                                            x, map_area_height_dots +
                                            grid_legend_margin_dots/1.0)

        for i, label in enumerate(map_grid.vertical_labels):
            y = i * step_vert

            if i < len(map_grid.vertical_labels) - 1:
                y += step_vert/2.0
            elif last_vert_portion >= 0.3:
                y += step_vert * last_vert_portion/2.0
            else:
                continue

            draw_utils.draw_halotext_center(ctx, label,
                                            -grid_legend_margin_dots, y)

            draw_utils.draw_halotext_center(ctx, label,
                                            map_area_width_dots +
                                            grid_legend_margin_dots, y)

        ctx.restore()


    def render(self, cairo_surface, dpi, osm_date):
        ctx = cairo.Context(cairo_surface)

        self._render_front_page(ctx, cairo_surface, dpi, osm_date)
        self._render_blank_page(ctx, cairo_surface, dpi, 2)
        #self._render_blank_page(ctx, cairo_surface, dpi, 3)

        ctx.save()

        self._render_overview_page(ctx, cairo_surface, dpi)

        for map_number, (canvas, grid, overlay_canvases, overlay_effects) in enumerate(self.pages):
            ctx.save();
            #LOG.info('Map page %d of %d' % (map_number + 1, len(self.pages)))
            rendered_map = canvas.get_rendered_map()
            # LOG.debug('Mapnik scale: 1/%f' % rendered_map.scale_denominator())
            # LOG.debug('Actual scale: 1/%f' % canvas.get_actual_scale())

            ctx.rectangle(0, 0, self._usable_map_area_width_pt, self._usable_map_area_height_pt)
            ctx.clip()

            dest_tag = "mypage%d" % (map_number + self._first_map_page_number)
            draw_utils.anchor(ctx, dest_tag)

            mapnik.render(rendered_map, ctx)

            for overlay_canvas in overlay_canvases:
                rendered_overlay = overlay_canvas.get_rendered_map()
                mapnik.render(rendered_overlay, ctx)

            # Place the vertical and horizontal square labels
            ctx.save()
            ctx.translate(Renderer.PRINT_BLEED_PT + commons.convert_pt_to_dots(self.grayed_margin_inside_pt if map_number % 2 else self.grayed_margin_outside_pt),
                      Renderer.PRINT_BLEED_PT + commons.convert_pt_to_dots(self.grayed_margin_top_bottom_pt))
            self._draw_labels(ctx, grid,
                  commons.convert_pt_to_dots(self._usable_map_area_width_pt \
                        - 2 * Renderer.PRINT_BLEED_PT \
                        - self.grayed_margin_inside_pt - self.grayed_margin_outside_pt),
                  commons.convert_pt_to_dots(self._usable_map_area_height_pt \
                        - 2 * Renderer.PRINT_BLEED_PT \
                        - 2 * self.grayed_margin_top_bottom_pt),
                  commons.convert_pt_to_dots(self._grid_legend_margin_pt))
            ctx.restore()


            # apply effect overlays
            ctx.save()
            # we have to undo border adjustments here
            ctx.translate(-commons.convert_pt_to_dots(self.grayed_margin_inside_pt)/2,
                      -commons.convert_pt_to_dots(self.grayed_margin_top_bottom_pt)/2)
            self._map_canvas = canvas;
            for effect in overlay_effects:
                self.grid = grid
                self.render_plugin(effect, ctx)
            ctx.restore()


            # Render the page number
            draw_utils.render_page_number(ctx, map_number + self._first_map_page_number,
                                          self._usable_map_area_width_pt,
                                          self._usable_map_area_height_pt,
                                          self.grayed_margin_inside_pt,
                                          self.grayed_margin_outside_pt,
                                          self.grayed_margin_top_bottom_pt,
                                          Renderer.PRINT_BLEED_PT,
                                          transparent_background = True)
            self._render_neighbour_arrows(ctx, cairo_surface, map_number,
                                          len(str(len(self.pages) + self._first_map_page_number)))

            cairo_surface.set_page_label('Map page %d' % (map_number + self._first_map_page_number))
            cairo_surface.show_page()
            ctx.restore();
        ctx.restore()

        mpsir = MultiPageStreetIndexRenderer(self.rc.i18n,
                                             ctx, cairo_surface,
                                             self.index_categories,
                                             (self.paper_width_pt, self.paper_height_pt),
                                             (self.grayed_margin_inside_pt, self.grayed_margin_outside_pt, self.grayed_margin_top_bottom_pt),
                                             Renderer.PRINT_BLEED_PT,
                                             map_number+4)

        mpsir.render()

        cairo_surface.flush()

    # In multi-page mode, we only render pdf format
    @staticmethod
    def get_compatible_output_formats():
        return [ "pdf" ]

    @staticmethod
    def get_compatible_paper_sizes(bounding_box,
                                   renderer_context,
                                   scale=Renderer.DEFAULT_MULTIPAGE_SCALE,
                                   index_position=None, hsplit=1, vsplit=1):
        valid_sizes = []
        LOG.warning("getting multipage paper size options")
        LOG.warning(renderer_context)
        for sz in renderer_context.get_all_paper_sizes('multipage'):
            valid_sizes.append((sz[0], sz[1], sz[2], True, True, sz[0] == 'DinA4'))
        return valid_sizes

    def _draw_overview_labels(self, ctx, map_canvas, overview_grid,
                     area_width_dots, area_height_dots):
        """
        Draw the page numbers for the overview grid.

        Args:
           ctx (cairo.Context): The cairo context to use to draw.
           overview_grid (OverViewGrid): the overview grid object
           area_width_dots/area_height_dots (numbers): size of the
              drawing area (cairo units).
        """
        ctx.save()
        ctx.set_font_size(14)

        bbox = map_canvas.get_actual_bounding_box()
        bottom_right, bottom_left, top_left, top_right = bbox.to_mercator()
        bottom, left = bottom_right.y, top_left.x
        coord_delta_y = top_left.y - bottom_right.y
        coord_delta_x = bottom_right.x - top_left.x
        w, h = None, None
        for idx, page_bb in enumerate(overview_grid._pages_bbox):
            p_bottom_right, p_bottom_left, p_top_left, p_top_right = \
                                                        page_bb.to_mercator()
            center_x = p_top_left.x+(p_top_right.x-p_top_left.x)/2
            center_y = p_bottom_left.y+(p_top_right.y-p_bottom_right.y)/2
            y_percent = 100 - 100.0*(center_y - bottom)/coord_delta_y
            y = int(area_height_dots*y_percent/100)

            x_percent = 100.0*(center_x - left)/coord_delta_x
            x = int(area_width_dots*x_percent/100)

            if not w or not h:
                w = area_width_dots*(p_bottom_right.x - p_bottom_left.x
                                                         )/coord_delta_x
                h = area_height_dots*(p_top_right.y - p_bottom_right.y
                                                         )/coord_delta_y

            draw_utils.draw_text_adjusted(ctx, str(idx + self._first_map_page_number),
                                          x, y, w, h,
                                          max_char_number=len(str(len(overview_grid._pages_bbox)+3)),
                                          text_color=(0, 0, 0, 0.6))

            ctx.save()
            ctx.translate(x-w/2, y-h/2)
            ctx.set_source_rgba(0,0,0,0.1)
            draw_utils.begin_internal_link(ctx, "mypage%d" % (idx + self._first_map_page_number))
            ctx.rectangle(0,0,w,h)
            ctx.stroke()
            draw_utils.end_link(ctx)
            ctx.restore()

        ctx.restore()


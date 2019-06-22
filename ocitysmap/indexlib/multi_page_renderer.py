# -*- coding: utf-8 -*-

# ocitysmap, city map and street index generator from OpenStreetMap data
# Copyright (C) 2012  David Mentré
# Copyright (C) 2012  Thomas Petazzoni

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
import math
import gi
gi.require_version('Rsvg', '2.0')
gi.require_version('Pango', '1.0')
gi.require_version('PangoCairo', '1.0')
from gi.repository import Rsvg, Pango, PangoCairo

import draw_utils
import ocitysmap.layoutlib.commons as UTILS
from ocitysmap.layoutlib.abstract_renderer import Renderer

import logging
LOG = logging.getLogger('ocitysmap')

# FIXME: refactoring
# We use the same 10mm as GRAYED_MARGIN_MM in the map multi-page renderer
PAGE_NUMBER_MARGIN_PT  = UTILS.convert_mm_to_pt(10)

class MultiPageStreetIndexRenderer:
    """
    The MultiPageStreetIndexRenderer class encapsulates all the logic
    related to the rendering of the street index on multiple pages
    """

    # ctx: Cairo context
    # surface: Cairo surface
    def __init__(self, i18n, ctx, surface, index_categories, rendering_area, margins, print_bleed_pt,
                 page_offset):
        self._i18n            = i18n
        self.ctx              = ctx
        self.surface          = surface
        self.index_categories = index_categories
        self.rendering_area_x = Renderer.PRINT_SAFE_MARGIN_PT
        self.rendering_area_y = Renderer.PRINT_SAFE_MARGIN_PT
        self.print_safe_margin_pt = Renderer.PRINT_SAFE_MARGIN_PT
        self.rendering_area_w = rendering_area[0]
        self.rendering_area_h = rendering_area[1]
        self.margin_inside_pt = margins[0]
        self.margin_outside_pt = margins[1]
        self.margin_top_bottom_pt = margins[2]
        self.print_bleed_pt = print_bleed_pt
        self.page_offset      = page_offset
        self.index_page_num   = 1
        self.debug_mode       = False

    def _create_layout_with_font(self, ctx, pc, font_desc):
        layout = PangoCairo.create_layout(ctx)
        layout.set_font_description(font_desc)
        font = layout.get_context().load_font(font_desc)
        font_metric = font.get_metrics()

        fascent = float(font_metric.get_ascent()) / Pango.SCALE
        fheight = float((font_metric.get_ascent() + font_metric.get_descent())
                        / Pango.SCALE)
        em = float(font_metric.get_approximate_char_width()) / Pango.SCALE

        return layout, fascent, fheight, em

    def _draw_page_number(self):
        self.ctx.save()

        draw_utils.render_page_number(self.ctx,
                                      self.index_page_num + self.page_offset,
                                      self.rendering_area_w,
                                      self.rendering_area_h,
                                      self.margin_inside_pt,
                                      self.margin_outside_pt,
                                      self.margin_top_bottom_pt,
                                      self.print_bleed_pt,
                                      transparent_background = False)
        self.ctx.restore()
        self.surface.set_page_label('Index page %d' % (self.index_page_num))

    def _draw_page_background(self):
        if self.debug_mode:
            LOG.debug("grau: %f rendering_area_w, %f print_bleed_pt, %f print_safe_margin_pt" % (self.rendering_area_w, self.print_bleed_pt, self.print_safe_margin_pt))
            LOG.debug("grau: %f w, %f h" % (self.rendering_area_w - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt, self.rendering_area_h - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt))
            # temp / grey: show area without bleed-difference
            self.ctx.save()
            self.ctx.set_source_rgba(.85,.75,.75, .5)
            self.ctx.rectangle(
                self.print_bleed_pt + self.print_safe_margin_pt,
                self.print_bleed_pt + self.print_safe_margin_pt,
                self.rendering_area_w - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt,
                self.rendering_area_h - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt)
            self.ctx.fill()
            self.ctx.restore()

    def _draw_page_header(self, rtl, ctx, pc, layout, fascent, fheight,
             baseline_x, baseline_y, margin_top, text):

        content_width = self.rendering_area_w - 2*self.print_bleed_pt - self.margin_inside_pt - self.margin_outside_pt
        margin_left = self.print_bleed_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt)

        # calculate height -> fill background first.
        layout.set_text(text, -1)
        ext = layout.get_extents()
        textblock_height = float(ext.ink_rect.height)/Pango.SCALE * 1.8

        self.ctx.save()

        if self.debug_mode:
            LOG.debug("page_header: %f left, %f top, %f width, %f textblock_height" % (margin_left, margin_top, content_width, textblock_height))
            # background
            self.ctx.set_source_rgba(0.9, 0.9, 0.7, .5)
            self.ctx.rectangle(margin_left, margin_top, content_width, textblock_height)
            self.ctx.fill()

        # text
        self.ctx.set_source_rgb(0.0, 0.0, 0.0)
        self.ctx.translate(0, self.print_bleed_pt) # TODO: correct fheight/4
        draw_utils.draw_text_center(self.ctx, pc, layout, fascent, textblock_height, margin_left, baseline_y + (textblock_height / 2 * 1.1), text) #baseline_y
        self.ctx.restore()

        return textblock_height

    def _new_page(self):
        self.surface.show_page()
        self.index_page_num = self.index_page_num + 1
        self._draw_page_number()

    def render(self, dpi = UTILS.PT_PER_INCH):
        self.ctx.save()

        # Create a PangoCairo context for drawing to Cairo
        pc = PangoCairo.create_context(self.ctx)

        city_fd = Pango.FontDescription("DejaVu Sans Condensed Bold 18")
        header_fd = Pango.FontDescription("DejaVu Sans Condensed Bold 12")
        label_column_fd  = Pango.FontDescription("DejaVu 6")

        city_layout, city_fascent, city_fheight, city_em = \
            self._create_layout_with_font(self.ctx, pc, city_fd)
        header_layout, header_fascent, header_fheight, header_em = \
            self._create_layout_with_font(self.ctx, pc, header_fd)
        label_layout, label_fascent, label_fheight, label_em = \
            self._create_layout_with_font(self.ctx, pc, label_column_fd)
        column_layout, _, _, _ = \
            self._create_layout_with_font(self.ctx, pc, label_column_fd)

        # By OCitysmap's convention, the default resolution is 72 dpi,
        # which maps to the default pangocairo resolution (96 dpi
        # according to pangocairo docs). If we want to render with
        # another resolution (different from 72), we have to scale the
        # pangocairo resolution accordingly:
        PangoCairo.context_set_resolution(city_layout.get_context(),
                                          96.*dpi/UTILS.PT_PER_INCH)
        PangoCairo.context_set_resolution(column_layout.get_context(),
                                          96.*dpi/UTILS.PT_PER_INCH)
        PangoCairo.context_set_resolution(label_layout.get_context(),
                                          96.*dpi/UTILS.PT_PER_INCH)
        PangoCairo.context_set_resolution(header_layout.get_context(),
                                          96.*dpi/UTILS.PT_PER_INCH)

        margin = label_em
        cityBlockHeight = city_fheight * 2

        index_area_w_pt = self.rendering_area_w - 2*self.print_bleed_pt - self.margin_inside_pt - self.margin_outside_pt
        city_layout.set_width(int(UTILS.convert_pt_to_dots((index_area_w_pt) * Pango.SCALE, dpi)))

        firstPage = True
        self._draw_page_background()
        cities = list(self.index_categories.keys())
        cities.sort()
        margin_top = self.print_bleed_pt + self.print_safe_margin_pt + self.margin_top_bottom_pt
        margin_top_page = margin_top
        offset_y = margin_top_page
        max_drawing_height = 0
        city_index = -1
        LOG.debug("%f print_bleed_pt, %f print_safe_margin_pt, %f margin_top_bottom_pt, %f margin_top" % (self.print_bleed_pt, self.print_safe_margin_pt, self.margin_top_bottom_pt, margin_top))
        page_full_available_h = self.rendering_area_h - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt - 2*self.margin_top_bottom_pt

        for city in cities:
            city_index = city_index + 1
            # create new page - if it is not the first one
            #if not firstPage:
            #    self._new_page()
            firstPage = False

            margin_top_page += max_drawing_height # add max drawing height of previous city
            index_area_h_pt = self.rendering_area_h - self.print_bleed_pt - self.print_safe_margin_pt - self.margin_top_bottom_pt - margin_top_page
            LOG.debug("============")
            LOG.debug("printing index for city '%s'. available area: %f x %f, margin_top_page: %f" % (city, index_area_w_pt, index_area_h_pt, margin_top_page))

            if (margin_top_page > (page_full_available_h * 4 / 5)):
                LOG.debug("NEW PAGE: margin_top_page (%f) > %f" % (margin_top_page, page_full_available_h * 4 / 5))
                self._new_page()
                self._draw_page_background()
                margin_top = self.print_bleed_pt + self.print_safe_margin_pt + self.margin_top_bottom_pt
                margin_top_page = margin_top
                index_area_h_pt = self.rendering_area_h - self.print_bleed_pt - self.print_safe_margin_pt - self.margin_top_bottom_pt - margin_top_page # full page height available now with this new page.

            city_header_height = 0
            if len(cities) > 1:
                city_header_height = self._draw_page_header(
                            self._i18n.isrtl(), self.ctx, pc, city_layout,
                            UTILS.convert_pt_to_dots(city_fascent, dpi),
                            UTILS.convert_pt_to_dots(cityBlockHeight, dpi),
                            UTILS.convert_pt_to_dots(self.rendering_area_x + self.print_bleed_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt), dpi),
                            UTILS.convert_pt_to_dots(margin_top_page, dpi), # baseline_y, original: self.rendering_area_y + header_fascent
                            margin_top_page, #margin_top
                            city)
                index_area_h_pt = index_area_h_pt - city_header_height
                margin_top_page += city_header_height

            # find largest label and location
            max_label_drawing_width = 0.0
            max_location_drawing_width = 0.0

            if False:
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
                self.index_categories[city].append(self.index_categories[city][0])
            
            if False:
                # Alle Kategorien, bis auf 1 entfernen
                while len(self.index_categories[city])>1:
                    self.index_categories[city].pop(1)

                # Alle Einträge, bis auf 1, dieser Kategorie entferne
                #while len(self.index_categories[city][0].items)>4:
                #    self.index_categories[city][0].items.pop(1)

                # Bei dieser Kategorie weitere Einträge hinzufügen
                for i in range(40):
                    self.index_categories[city][0].items.append(self.index_categories[city][0].items[3])

            # calculate height of categories
            #LOG.debug("number of categories: %d" % len(self.index_categories[city]))
            #LOG.debug("number of entries in first category: %d" % len(self.index_categories[city][0].items))
            sum_height = 0
            for category in self.index_categories[city]:
                sum_height += category.label_drawing_height(header_layout) * 1.006756756756757
                #LOG.debug("adding height %f for category %s" % (category.label_drawing_height(header_layout), category.name))
                for street in category.items:
                    #LOG.debug("label_drawing_height of %s: %f" % (street.label, street.label_drawing_height(label_layout)))
                    sum_height += street.label_drawing_height(label_layout) * 1.031925675675676

                    w = street.label_drawing_width(label_layout)
                    if w > max_label_drawing_width:
                        max_label_drawing_width = w
                        #LOG.debug("new max_label_drawing_width: %f (%s)" % (max_label_drawing_width, street.label))

                    w = street.location_drawing_width(label_layout)
                    if w > max_location_drawing_width:
                        max_location_drawing_width = w
                        #LOG.debug("new max_location_drawing_width: %f (%s)" % (max_location_drawing_width, street.location_str))
            col_max_height = math.ceil(float(sum_height) / 4) + 50
            LOG.debug("sum_height: %f, %f per column (4) => col_max_height: %d" % (sum_height, float(sum_height) / 4, col_max_height))

            # No street to render, bail out
            if max_label_drawing_width == 0.0:
                return

            #LOG.debug("max_label_drawing_width: %f" % max_label_drawing_width)
            #LOG.debug("max_location_drawing_width: %f" % max_location_drawing_width)

            # Find best number of columns
            max_drawing_width = max_label_drawing_width + max_location_drawing_width + 2 * margin
            max_drawing_height = col_max_height
            needed_drawing_height = max_drawing_height
            if (index_area_h_pt < max_drawing_height):
                LOG.debug("more height neededed (max_drawing_height: %f), than there is available on this page left (index_area_h_pt: %f). Setting max_drawing_height to index_area_h_pt" % (max_drawing_height, index_area_h_pt))
                max_drawing_height = index_area_h_pt

            if self.debug_mode:
                # temp / green: show content-area (inside grayed margin)
                LOG.debug("grün: %f x %f" % (index_area_w_pt, max_drawing_height))
                self.ctx.save()
                self.ctx.set_source_rgba(.85,.95,.85, .5)
                self.ctx.rectangle(
                    self.print_bleed_pt + self.print_safe_margin_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt),
                    margin_top_page,
                    index_area_w_pt,
                    max_drawing_height
                )
                self.ctx.fill()
                self.ctx.restore()

            #LOG.debug("max_drawing_width: %f" % max_drawing_width)

            #columns_count = int(math.ceil(index_area_w_pt / max_drawing_width))
            # following test should not be needed. No time to prove it. ;-)
            #if columns_count == 0:
            #    columns_count = 1

            #LOG.debug("number of columns: %d" % columns_count)

            columns_count = 4 # Gerald: fixed to 4.
            # We have now have several columns
            column_width = index_area_w_pt / columns_count
            #LOG.debug("column_width: %d" % column_width)

            column_layout.set_width(int(UTILS.convert_pt_to_dots((column_width - margin) * Pango.SCALE, dpi)))
            label_layout.set_width(int(UTILS.convert_pt_to_dots((column_width - margin - max_location_drawing_width - 2 * label_em) * Pango.SCALE, dpi)))
            header_layout.set_width(int(UTILS.convert_pt_to_dots((column_width - margin) * Pango.SCALE, dpi)))

            if not self._i18n.isrtl():
                orig_offset_x = offset_x = margin/2.
                orig_delta_x  = delta_x  = column_width
            else:
                orig_offset_x = offset_x = index_area_w_pt - column_width + margin/2.
                orig_delta_x  = delta_x  = - column_width

            actual_n_cols = 0

            # page number of first page
            self._draw_page_number()

            if self.debug_mode:
                # temp: show index-area (inside grayed margin)
                LOG.debug("pink: %f w -> index_area_w_pt, %f h -> index_area_h_pt" % (index_area_w_pt, index_area_h_pt))
                self.ctx.save()
                self.ctx.set_source_rgba(.85,.25,.85,.5)
                self.ctx.rectangle(
                    self.print_bleed_pt + self.print_safe_margin_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt) + (city_index % 4) * column_width,
                    margin_top_page,
                    column_width,
                    max_drawing_height
                )
                self.ctx.fill()
                self.ctx.restore()

            offset_y = margin_top_page # each city/category starts on the corresponding margin
            for category in self.index_categories[city]:
                if ( offset_y + header_fheight + label_fheight + margin/2. > (max_drawing_height + margin_top_page) ):
                    offset_y       = margin_top_page
                    offset_x      += delta_x
                    actual_n_cols += 1

                    if actual_n_cols == columns_count:
                        LOG.debug("INSERT NEW PAGE. actual_n_cols %d == columns_count %d" % (actual_n_cols, columns_count))
                        self._new_page()
                        self._draw_page_background()
                        actual_n_cols = 0
                        city_header_height = 0
                        margin_top_page = margin_top
                        offset_y = margin_top_page
                        offset_x = orig_offset_x
                        delta_x  = orig_delta_x
                        max_drawing_height = needed_drawing_height - max_drawing_height

                if True: # if only for debugging
                    category_height = category.label_drawing_height(header_layout)
                    #LOG.debug("category_height draw %d | %d | %d | %d" % (category_height, header_fascent, UTILS.convert_pt_to_dots(header_fascent, dpi), header_fheight))
                    category.draw(self._i18n.isrtl(), self.ctx, pc, header_layout,
                                UTILS.convert_pt_to_dots(header_fascent, dpi),
                                UTILS.convert_pt_to_dots(header_fheight, dpi),
                                UTILS.convert_pt_to_dots(self.rendering_area_x + self.print_bleed_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt)
                                                        + offset_x, dpi),
                                UTILS.convert_pt_to_dots(self.rendering_area_y + offset_y + header_fascent, dpi))

                    offset_y += category_height

                if True: # if only for debugging
                    for street in category.items:
                        label_height = street.label_drawing_height(label_layout)
                        if ( offset_y + label_height + margin/2. > (max_drawing_height + margin_top_page) ):
                            offset_y       = margin_top_page
                            offset_x      += delta_x
                            actual_n_cols += 1

                            if actual_n_cols == columns_count:
                                LOG.debug("INSERT NEW PAGE. actual_n_cols %d == columns_count %d" % (actual_n_cols, columns_count))
                                self._new_page()
                                self._draw_page_background()
                                actual_n_cols = 0
                                city_header_height = 0
                                margin_top_page = margin_top
                                offset_y = margin_top_page
                                offset_x = orig_offset_x
                                delta_x  = orig_delta_x
                                max_drawing_height = needed_drawing_height - max_drawing_height

                                if self.debug_mode:
                                    # temp: show area without bleed-difference
                                    self.ctx.save()
                                    self.ctx.set_source_rgba(.95,.95,.95,.5)
                                    self.ctx.rectangle(
                                        self.print_bleed_pt + self.print_safe_margin_pt,
                                        self.print_bleed_pt + self.print_safe_margin_pt,
                                        self.rendering_area_w - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt,
                                        self.rendering_area_h - 2*self.print_bleed_pt - 2*self.print_safe_margin_pt)
                                    self.ctx.fill()
                                    self.ctx.restore()

                                    # temp: show content-area (inside grayed margin)
                                    self.ctx.save()
                                    self.ctx.set_source_rgba(.85,.95,.85,.5)
                                    self.ctx.rectangle(
                                        self.print_bleed_pt + self.print_safe_margin_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt),
                                        self.print_bleed_pt + self.print_safe_margin_pt + self.margin_top_bottom_pt,
                                        index_area_w_pt,
                                        index_area_h_pt
                                    )
                                    self.ctx.fill()
                                    self.ctx.restore()

                        street.draw(self._i18n.isrtl(), self.ctx, pc, column_layout,
                                    UTILS.convert_pt_to_dots(label_fascent, dpi),
                                    UTILS.convert_pt_to_dots(label_fheight, dpi),
                                    UTILS.convert_pt_to_dots(self.rendering_area_x + self.print_bleed_pt + (self.margin_inside_pt if (self.index_page_num + self.page_offset) % 2 else self.margin_outside_pt)
                                                            + offset_x, dpi),
                                    UTILS.convert_pt_to_dots(self.rendering_area_y + offset_y + label_fascent, dpi),
                                    label_layout,
                                    UTILS.convert_pt_to_dots(label_height, dpi),
                                    UTILS.convert_pt_to_dots(max_location_drawing_width, dpi))

                        offset_y += label_height

        self.ctx.restore()


if __name__ == '__main__':
    import random
    import string

    import commons
    import coords

    width = UTILS.convert_mm_to_pt(210)
    height = UTILS.convert_mm_to_pt(297)

    surface = cairo.PDFSurface('/tmp/myindex_render.pdf', width, height)

    random.seed(42)

    def rnd_str(max_len, letters = string.letters + ' ' * 4):
        return ''.join(random.choice(letters)
                       for i in xrange(random.randint(1, max_len)))

    class i18nMock:
        def __init__(self, rtl):
            self.rtl = rtl
        def isrtl(self):
            return self.rtl

    streets = []
    for i in ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
              'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
              'Schools', 'Public buildings']:
        items = []
        for label, location_str in [(rnd_str(40).capitalize(),
                                     '%s%d-%s%d' \
                                         % (rnd_str(2,
                                                    string.ascii_uppercase),
                                            random.randint(1,19),
                                            rnd_str(2,
                                                    string.ascii_uppercase),
                                            random.randint(1,19),
                                            ))]*random.randint(1, 20):
            item              = commons.StreetIndexItem(label, None, None)
            item.location_str = location_str
            item.page_number  = random.randint(1, 100)
            items.append(item)
        streets.append(commons.StreetIndexCategory(i, items))

    ctxtmp = cairo.Context(surface)

    rendering_area = \
        (15, 15, width - 2 * 15, height - 2 * 15)

    mpsir = MultiPageStreetIndexRenderer(i18nMock(False), ctxtmp, surface,
                                         streets, rendering_area, 1)
    mpsir.render()
    surface.show_page()

    mpsir2 = MultiPageStreetIndexRenderer(i18nMock(True), ctxtmp, surface,
                                          streets, rendering_area,
                                          mpsir.page_number + 1)
    mpsir2.render()

    surface.finish()

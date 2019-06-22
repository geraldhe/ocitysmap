import cairo
import os
import sys
import math
import qrcode
import qrcode.image.svg
import gi
gi.require_version('Rsvg', '2.0')
from gi.repository import Rsvg

from io import BytesIO

from ocitysmap.layoutlib.commons import convert_pt_to_dots
from ocitysmap.layoutlib.abstract_renderer import Renderer

import logging
LOG = logging.getLogger('ocitysmap')

def render(renderer, ctx):
    if renderer.rc.poi_file:
    ##
    ## Draw the creator notice
    ##
        #ctx.save()
        #
        # Move to the right position
        #ctx.translate(safe_margin_dots + usable_area_width_dots/2.3,
        #              ( safe_margin_dots + title_margin_dots
        #                + usable_area_height_dots
        #                + copyright_margin_dots/4. ) )
        
        # Draw the copyright notice
        #self._draw_creator_notice(ctx, usable_area_width_dots,
        #                          copyright_margin_dots,
        #                          osm_date=osm_date)
        #ctx.restore()

        # place POI markers on map canvas
        n = 0
        for category in renderer.street_index.categories:
            for poi in category.items:
                n = n + 1
                lat, lon = poi.endpoint1.get_latlong()
                renderer._marker(category.color, str(n), lat, lon, ctx, renderer.dpi)

        # place "you are here" circle if coordinates are given
        if renderer.street_index.lat != False:
            x,y = renderer._latlon2xy(renderer.street_index.lat, renderer.street_index.lon, renderer.dpi)
            ctx.save()
            ctx.translate(x, y)
            ctx.set_source_rgba(1, 0, 0, 0.8)
            ctx.set_line_width(10)
            ctx.arc(0, 0, 50, 0, 2*math.pi)
            ctx.stroke_preserve()
            ctx.set_source_rgba(1, 0, 0, 0.2)
            ctx.fill()
            ctx.restore()


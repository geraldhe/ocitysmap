# -*- coding: utf-8 -*-

# ocitysmap, city map and street index generator from OpenStreetMap data
# Copyright (C) 2010  David Decotigny
# Copyright (C) 2010  Frédéric Lehobey
# Copyright (C) 2010  Pierre Mauduit
# Copyright (C) 2010  David Mentré
# Copyright (C) 2010  Maxime Petazzoni
# Copyright (C) 2010  Thomas Petazzoni
# Copyright (C) 2010  Gaël Utard

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

from . import Stylesheet

import os
from string import Template
import gpxpy
import gpxpy.gpx
import codecs

class GpxStylesheet(Stylesheet):
    def __init__(self, gpx_file, tmpdir):
        super().__init__()

        gpx_fp = codecs.open(gpx_file, 'r', 'utf-8-sig')
        gpx = gpxpy.parse(gpx_fp)

        if gpx.copyright_year or gpx.copyright_author or gpx.copyright_license:
            self.annotation = "GPX track © %s %s %s" % (gpx.copyright_year, gpx.copyright_author, gpx.copyright_license)
        
        gpx_fp.close()
        
        template_dir = os.path.realpath(
            os.path.join(
                os.path.dirname(__file__),
                '../../templates/gpx'))

        template_file = os.path.join(template_dir, 'template.xml')
        GPX_filename = os.path.join(tmpdir, 'gpx_style.xml')
        tmpfile = open(GPX_filename, 'w')

        with open(template_file, 'r') as style_template:
            tmpstyle = Template(style_template.read())
            tmpfile.write(
                tmpstyle.substitute(
                    gpxfile = gpx_file,
                    svgdir = template_dir
                ))

        tmpfile.close()

        self.name = "GPX overlay"
        self.path = GPX_filename

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
import json
import re
import urllib3
import tempfile
import logging
from string import Template
import codecs

LOG = logging.getLogger('ocitysmap')


class UmapStylesheet(Stylesheet):
    def __init__(self, umap_file, tmpdir):
        super().__init__()

        template_dir = os.path.realpath(
            os.path.join(
                os.path.dirname(__file__),
                '../../templates/umap'))

        json_filename = os.path.join(tmpdir, 'geo.json')
        json_tmpfile = open(json_filename, 'w')
        json_tmpfile.write(self.umap_preprocess(umap_file, tmpdir))
        json_tmpfile.close()

        template_file = os.path.join(template_dir, 'template.xml')
        style_filename = os.path.join(tmpdir, 'umap_style.xml')
        style_tmpfile = open(style_filename, 'w')

        with open(template_file, 'r') as style_template:
            tmpstyle = Template(style_template.read())
            style_tmpfile.write(
                tmpstyle.substitute(
                    umapfile = json_filename,
                    basedir  = template_dir
                ))

        style_tmpfile.close()

        self.name = "UMAP overlay"
        self.path = style_filename


    def umap_preprocess(self, umap_file, tmpdir):
        umap_defaults = {
            'color'      :   'blue',
            'opacity'    :      0.5,
            'fillColor'  :   'blue',
            'fillOpacity':      0.2,
            'weight'     :        3,
            'dashArray'  :       '',
            'fill'       :    'yes',
            'stroke'     :    'yes',
            'name'       :       '',
            'iconClass'  : 'Square',
            'iconUrl'    : '/uploads/pictogram/circle-24_1.png'
        }

        marker_offsets = {
            'Square': -18,
            'Drop'  : -18,
            'Circle': 0,
            'Ball'  : -16
        }

        icon_dir = os.path.realpath(
            os.path.join(
                os.path.dirname(__file__),
                '../../templates/umap/maki/icons'))

        http = urllib3.PoolManager()

        fp = codecs.open(umap_file, 'r', 'utf-8-sig')

        umap = json.load(fp)

        if 'licence' in umap['properties'] or 'shortCredit' in umap['properties']:
            licence = ''
            try:
              licence = umap['properties']['licence']['name']
            except:
              pass
            credit = umap['properties']['shortCredit'] if 'shortCredit' in umap['properties'] else ''
            self.annotation = "Umap overlay © %s %s" % (licence, credit)

        for prop in ['color', 'opacity', 'fillColor', 'fillOpacity', 'weight', 'dashArray', 'iconClass', 'iconUrl']:
            if prop in umap['properties']:
                umap_defaults[prop] = umap['properties'][prop]

        layers = umap['layers']

        new_features = []

        icon_cache = {}

        for layer in layers:
            for feature in layer['features']:
                layer_defaults = umap_defaults

                for prop in ['color', 'opacity', 'fillColor', 'fillOpacity', 'weight', 'dashArray', 'iconClass', 'iconUrl']:
                    try:
                        if prop in layer['_storage']:
                            layer_defaults[prop] = layer['_storage'][prop]
                    except:
                        pass

                new_props = {}
                for prop in ['name', 'color', 'opacity', 'fillColor', 'fillOpacity', 'weight', 'dashArray', 'fill', 'stroke']:
                    new_props[prop] = layer_defaults[prop]
                    try:
                        if prop in feature['properties']:
                            new_props[prop] = feature['properties'][prop]
                        elif prop in feature['properties']['_storage_options']:
                            new_props[prop] = feature['properties']['_storage_options'][prop]
                    except:
                        pass

                if feature['geometry']['type'] == 'Point':
                    try:
                        iconClass = feature['properties']['_storage_options']['iconClass']
                    except:
                        iconClass = layer_defaults['iconClass']

                    try:
                        iconUrl = feature['properties']['_storage_options']['iconUrl']
                    except:
                        iconUrl = layer_defaults['iconUrl']

                    new_props['iconClass'] = iconClass

                    if iconClass == 'Square' or iconClass == 'Drop':
                        m = re.match(r'/uploads/pictogram/(.*)-24(.*)\.png', iconUrl)
                        if m:
                            new_props['iconUrl']  = icon_dir + '/' +  m.group(1) + "-15.svg"
                            if m.group(2) == '':
                                new_props['iconFill'] = 'black'
                            else:
                                new_props['iconFill'] = 'white'
                        else:
                            if iconUrl in icon_cache:
                                new_props['iconUrl'] = icon_cache[iconUrl]
                            else:
                                LOG.info("Umap: fetching icon from URL: %s" % iconUrl)
                                try:
                                    response = http.request('GET', iconUrl)
                                    iconFile = tempfile.NamedTemporaryFile(suffix='.png', delete=False, mode='wb', dir=tmpdir)
                                    iconFile.write(response.data)
                                    iconFile.close()

                                    iconPath = os.path.realpath(iconFile.name)
                                except:
                                    iconPath = icon_dir + '/circle-15.svg'

                                new_props['iconUrl'] = iconPath
                                icon_cache[iconUrl] = iconPath

                    try:
                        new_props['offset'] = marker_offsets[iconClass]
                    except:
                        pass

                new_props['weight'] = float(new_props['weight']) / 4

                new_features.append({
                    'type'       : 'Feature', 
                    'properties' : new_props, 
                    'geometry'   : feature['geometry']
                })

        new_umap = {
            'type'     : 'FeatureCollection', 
            'features' : new_features
        }

        return json.dumps(new_umap, indent=2)

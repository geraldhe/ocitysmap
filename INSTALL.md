OCitySMap installation instructions
===================================

These instructions refer to software dependencies by using Ubuntu Bionic (18.04LTS) package names. Minor adaptations might be needed for other distributions or for the precise Debian or Ubuntu release you are using. They have been tested on several x86_64 hosts.

If you are fine with running OCitySMap and MapOSMatic in a Vagrant virtual machine, plese have a look at the MapOSMatic Vagrant repository:

https://github.com/hholzgra/maposmatic-vagrant

Its provisioning shell scripts may also help as a guide to install things on a non-virtual machine.

 ## Installation of required packages

```bash
sudo aptitude install postgresql postgresql-contrib postgis osm2pgsql mapnik \
    python-psycopg2 python-gdal python-gtk2 python-cairo python-shapely
```

 ## Creation of a new PostgreSQL user

```bash
sudo -u postgres createuser -P -S -D -R maposmatic
```
Enter the password twice (we later use ``secret`` as example password).

 ## Creation of the database

```bash
sudo -u postgres createdb -E UTF8 -l en_US.UTF-8 -T template0 -O maposmatic maposmatic
```
(see also http://wiki.openstreetmap.org/wiki/Mapnik/PostGIS)

You can now try to connect to the database, using:

```bash
psql -h localhost -U maposmatic maposmatic
```
If it doesn't work, fix your configuration.

 ## Enable PostGIS and Hstore extensions on the database

```bash
echo "CREATE EXTENSION postgis;" | sudo -u postgres psql -d maposmatic
echo "ALTER TABLE geometry_columns OWNER TO maposmatic;" | sudo -u postgres psql -d maposmatic
echo "ALTER TABLE spatial_ref_sys OWNER TO maposmatic;" | sudo -u postgres psql -d maposmatic
echo "CREATE EXTENSION hstore;" | sudo -u postgres psql -d maposmatic
```
 
 ## Download OSM data

We use the Luxembourg country extract here, using the country extrat server provided by GeoFabrik, Germany:

```bash
wget http://download.geofabrik.de/osm/europe/luxembourg.osm.bz2
```

 ## Import the OSM data with ``osm2pgsql``

``` bash
    osm2pgsql -s -c -d maposmatic -m -U maposmatic -W \
              -H localhost -k luxembourg.osm.bz2
```
    
If you have a lot of RAM, remove ``-s``, it will make the import faster. If you miss RAM (and have a lot of time available) you can also use the ``-C`` option together with ``-s``. (See also ``osm2pgsql -h``).

If you want to add other OSM DB files, replace the ``-c`` option with a ``-a`` option in the subsequent files you are adding: if you keep the ``-c`` option, it will erase any previous GIS data you may have. For example:

```bash
osm2pgsql -s -a -d maposmatic -m -U maposmatic -W \
              -H localhost -k ile-de-france.osm.bz2
```

## Install Openstreetmap Carto style

TODO, for now please refer to the original OSM Carto install file:

https://github.com/gravitystorm/openstreetmap-carto/blob/master/INSTALL.md

## Installation of OCitySMap

### Download the source dode

If you have `git` installed, you can clone the project repository directly:

```bash
git clone git://git.savannah.nongnu.org/maposmatic/ocitysmap.git
cd ocitysmap
```

Or you can download the project source code as a ZIP archive from GitHub without having to have `git` installed:

```bash 
curl https://codeload.github.com/hholzgra/ocitysmap/zip/master --output ocitysmap.zip
unzip ocitysmap.zip
cd ocitysmap-master
```

###  Configuration file

Create a `~/.ocitysmap.conf` configuration file, modeled after the provided `ocitysmap.conf.dist` file:

```bash
cp ocitysmap.conf.dist ~/.ocitysmap.conf
```

### Run the OCitySMap renderer on the command line

E.g. for the example data imports above:

```bash
./render.py -t "Ceci n'est pas Paris" --osmid=-411354  # Contern, LU
./render.py -t "Ceci n'est pas Paris" --osmid=-943886  # Chevreuse, FR
```




Appendix A:  Installation of maposmatic-printable stylesheet
------------------------------------------------------------

a. Copy stylesheet/maposmatic-printable/symbols/* (i.e. all files in symbols/ directory) into mapnik2-osm/symbols/ directory.

b. Add absolute path to file stylesheet/maposmatic-printable/osm.xml into ~/.ocitysmap.conf.

c. Configure the stylesheet with database parameters and relevant  directories:

```bash
cd stylesheet/maposmatic-printable/

python ./generate_xml.py --dbname maposmatic --host 'localhost' \
         --user maposmatic --port 5432 \
         --password 'secret' \
         --world_boundaries mapnik2-osm/world_boundaries \
         --symbols mapnik2-osm/symbols
```


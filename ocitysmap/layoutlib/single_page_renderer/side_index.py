import ocitysmap
from ocitysmap.layoutlib.abstract_renderer import Renderer
from ocitysmap.layoutlib.single_page_renderers import SinglePageRenderer

class SinglePageRendererIndexOnSide(SinglePageRenderer):

    name = 'single_page_index_side'
    description = 'Full-page layout with the index on the side.'

    def __init__(self, db, rc, tmpdir, dpi, file_prefix):
        """
        Create the renderer.

        Args:
           rc (RenderingConfiguration): rendering parameters.
           tmpdir (os.path): Path to a temp dir that can hold temp files.
        """
        SinglePageRenderer.__init__(self, db, rc, tmpdir, dpi, file_prefix, 'side')

    @staticmethod
    def get_compatible_paper_sizes(bounding_box,
                                   scale=Renderer.DEFAULT_SCALE):
        """Returns a list of the compatible paper sizes for the given bounding
        box. The list is sorted, smaller papers first, and a "custom" paper
        matching the dimensions of the bounding box is added at the end.

        Args:
            bounding_box (coords.BoundingBox): the map geographic bounding box.
            scale (int): minimum mapnik scale of the map.

        Returns a list of tuples (paper name, width in mm, height in
        mm, portrait_ok, landscape_ok). Paper sizes are represented in
        portrait mode.
        """
        return SinglePageRenderer._generic_get_compatible_paper_sizes(
            bounding_box, scale, 'side')


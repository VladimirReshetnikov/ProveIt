"""fastunknot: exact unknot recognition with polynomial and width-bounded filters and a
scanning Khovanov backend.  No quasi-polynomial guarantee is claimed."""
from .alexander import alexander_polynomial
from .braid import braid_certificate
from .diagram import Diagram, DiagramError
from .factor import visible_factors
from .filters import alexander_obstruction, jones_obstruction
from .recognize import Result, factored_khovanov_rank, recognize
from .scan import ScanLimit, khovanov_rank

__all__ = ["Diagram", "DiagramError", "Result", "ScanLimit", "alexander_obstruction",
           "alexander_polynomial", "factored_khovanov_rank", "jones_obstruction", "khovanov_rank",
           "recognize", "visible_factors", "braid_certificate"]
__version__ = "0.3.0"

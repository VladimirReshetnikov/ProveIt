"""fastunknot: exact unknot recognition with polynomial filters and a scanning
Khovanov backend.  No quasi-polynomial guarantee is claimed."""
from .alexander import alexander_polynomial
from .diagram import Diagram, DiagramError
from .recognize import Result, recognize
from .scan import ScanLimit, khovanov_rank

__all__ = ["Diagram", "DiagramError", "Result", "ScanLimit", "alexander_polynomial",
           "khovanov_rank", "recognize"]
__version__ = "0.1.0"

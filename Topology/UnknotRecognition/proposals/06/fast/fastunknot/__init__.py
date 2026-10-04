"""fastunknot: exact unknot recognition with polynomial filters and a scanning
Khovanov backend.  No quasi-polynomial guarantee is claimed."""
from .alexander import alexander_polynomial
from .diagram import Diagram, DiagramError
from .recognize import Result, recognize
from .scan import ScanLimit, khovanov_rank

__all__ = ["Diagram", "DiagramError", "Result", "ScanLimit", "alexander_polynomial",
           "khovanov_rank", "recognize"]
__version__ = "0.2.0"

from .jones import normalized_bracket_mod
from .decompose import connected_sum_factors, verify_decomposition
__all__ += ["normalized_bracket_mod", "connected_sum_factors", "verify_decomposition"]

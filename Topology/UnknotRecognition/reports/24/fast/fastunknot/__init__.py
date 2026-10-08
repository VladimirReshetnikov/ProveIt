"""fastunknot: exact unknot recognition with polynomial and width-bounded filters and a
scanning Khovanov backend.  No quasi-polynomial guarantee is claimed."""
from .alexander import alexander_polynomial
from .braid import braid_certificate
from .diagram import Diagram, DiagramError
from .factor import visible_factors
from .filters import alexander_obstruction, jones_obstruction
from .interlace import visible_factors_interlacement, verify_interlacement_certificate
from .recognize import Result, factored_khovanov_rank, recognize
from .scan import ScanLimit, khovanov_rank
from .seifert import seifert_certificate, seifert_data, verify_seifert_certificate

__all__ = ["Diagram", "DiagramError", "Result", "ScanLimit", "alexander_obstruction",
           "alexander_polynomial", "factored_khovanov_rank", "jones_obstruction", "khovanov_rank",
           "recognize", "visible_factors", "seifert_certificate", "seifert_data",
           "verify_seifert_certificate", "visible_factors_interlacement",
           "verify_interlacement_certificate", "braid_certificate"]
__version__ = "0.3.0"


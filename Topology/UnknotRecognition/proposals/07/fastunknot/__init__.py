"""Exact unknot recognition with bounded filters and a scanning Khovanov backend.

Unrestricted worst-case complexity is exponential, not quasi-polynomial.
"""
from .alexander import alexander_polynomial
from .diagram import Diagram, DiagramError
from .factor import decompose, factorized_khovanov_rank, replay_decomposition
from .jones import JonesLimit, jones_modular, verify_jones_witness
from .recognize import Result, recognize
from .scan import ScanLimit, clear_caches, khovanov_rank

__all__ = ["Diagram", "DiagramError", "Result", "ScanLimit", "JonesLimit",
           "alexander_polynomial", "khovanov_rank", "recognize", "clear_caches",
           "jones_modular", "verify_jones_witness", "decompose",
           "replay_decomposition", "factorized_khovanov_rank"]
__version__ = "0.2.0"

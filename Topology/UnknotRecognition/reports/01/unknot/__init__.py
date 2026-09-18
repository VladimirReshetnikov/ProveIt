"""Exact grid-diagram recognition; no quasipolynomial worst-case claim."""
from .grid import DiagramError, Grid, Move
from .recognize import recognize, verify_certificate

__version__ = "0.1.0"
__all__ = ["DiagramError", "Grid", "Move", "recognize", "verify_certificate"]

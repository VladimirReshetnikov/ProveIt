"""Exact exponential reference recognizer and independently usable components.

This package does NOT implement the advertised quasi-polynomial algorithm.
"""
from .diagram import Diagram, DiagramError
from .khovanov import Limits, Result, recognize

__all__ = ["Diagram", "DiagramError", "Limits", "Result", "recognize"]
__version__ = "0.1.0"

"""Exact exponential unknot recognition and partial polynomial hierarchy kernels.

No quasipolynomial guarantee is claimed. See docs/report.pdf and README.md.
"""
from .diagram import InvalidDiagram, PlanarDiagram, braid_closure, read_diagram
from .solver import recognize

__version__ = "0.1.0"
__all__ = ["InvalidDiagram", "PlanarDiagram", "braid_closure", "read_diagram", "recognize"]

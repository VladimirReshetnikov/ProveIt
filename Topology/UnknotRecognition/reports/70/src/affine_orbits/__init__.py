"""Attachment-compatible weighted affine orbit kernels."""
from .core import BulkIndex, SparseOverlay, Model, Edge, Weight, Defect, wire
from .guard import UnsupportedModel, from_pairing_groups
__all__ = ["BulkIndex", "SparseOverlay", "Model", "Edge", "Weight", "Defect",
           "wire", "UnsupportedModel", "from_pairing_groups"]

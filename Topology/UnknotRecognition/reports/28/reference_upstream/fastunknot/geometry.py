"""Minimal import surface taken from the upstream geometry module."""
SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))
class ScanLimit(RuntimeError):
    """A user-selected ceiling was reached; this is never a knot verdict."""

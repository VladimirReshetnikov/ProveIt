"""Opt-in bridge to the existing ProveIt Python scanner.

Add both this archive root and ProveIt/Topology/UnknotRecognition/fast to
PYTHONPATH. No production defaults, input formats, or existing verdicts change.
The full upstream integration suite must be run before promoting this adapter.
"""
from unknot_windows.windows import probe

def window_probe(diagram, depth=2, **kwargs):
    from fastunknot.scan import ScanComplex
    from fastunknot.geometry import ScanLimit
    return probe(diagram, depth, scanner_factory=ScanComplex,
                 limit_exceptions=(ScanLimit,), **kwargs)

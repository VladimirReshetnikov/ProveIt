"""Compatibility geometry for the upstream algebra fixture.

Uses the unchanged geometric operations from the user's 18-Sep-2026
Knots.zip archive. This shim is NOT an exact upstream geometry.py snapshot.
"""
from reference.legacy.fastunknot.scan import (SMOOTHINGS, Glued, Matching, ScanLimit,
                                            _dsu_find as dsu_find, circles, glue)
glue_uncached = glue.__wrapped__

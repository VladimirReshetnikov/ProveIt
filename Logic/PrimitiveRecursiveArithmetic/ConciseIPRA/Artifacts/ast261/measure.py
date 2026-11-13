"""Measure the complete candidate and matched control; no checker is executed."""
import json
import sys
from verify import PROGRAMS, measure

print(json.dumps({
    "python": sys.version,
    "normalization": "CPython ast.unparse of the whole module plus one LF",
    "programs": [measure(name) for name in PROGRAMS],
}, indent=2))

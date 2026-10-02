"""Explicit leading-point comparison, preserving arithmetic fluctuations."""
import json
from numerics_core import saddle_diagnostics
print(json.dumps(saddle_diagnostics(include_fixed=True),indent=2))

"""Explicit-point inverse diagnostics; no inner saddle equation is solved."""
import json
from numerics_core import inverse_diagnostics
print(json.dumps(inverse_diagnostics(explicit=True),indent=2))

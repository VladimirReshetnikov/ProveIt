"""Centered exact-cumulant saddle checks; floating values are not certified."""
import json
from numerics_core import saddle_diagnostics
print(json.dumps(saddle_diagnostics(),indent=2))

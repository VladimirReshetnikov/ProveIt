"""Compare a clean replay with packaged symbolic/numerical reference outputs."""
import json
import sys
from pathlib import Path
import mpmath as mp

mp.mp.dps = 100
reference = Path(sys.argv[1])
replayed = Path(sys.argv[2])
files = ["involution-coefficients.json", "numerical-checks.json", "law-inversion-checks.json", "sector-checks.json"]

def compare(a, b, path):
    if isinstance(a, dict):
        assert isinstance(b, dict) and a.keys() == b.keys(), path
        for key in a: compare(a[key], b[key], path + "." + key)
    elif isinstance(a, list):
        assert isinstance(b, list) and len(a) == len(b), path
        for index, (x, y) in enumerate(zip(a, b)): compare(x, y, f"{path}[{index}]")
    elif a == b:
        return
    elif isinstance(a, str) and isinstance(b, str):
        # Symbolic strings are compared exactly; only numeric decimal records
        # receive a tolerance, allowing harmless mpmath version variation.
        try:
            x, y = mp.mpf(a), mp.mpf(b)
        except ValueError:
            raise AssertionError(f"Symbolic/text mismatch: {path}: {a!r} != {b!r}")
        assert abs(x-y) <= mp.mpf('1e-60') * max(1, abs(x), abs(y)), (path, a, b)
    else:
        raise AssertionError((path, a, b))

for name in files:
    compare(json.loads((reference/name).read_text()), json.loads((replayed/name).read_text()), name)
    print("PASS", name)

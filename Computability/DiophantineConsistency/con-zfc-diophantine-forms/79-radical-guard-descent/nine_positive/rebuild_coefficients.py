#!/usr/bin/env python3
"""Reconstruct original31 native integers; compare bytes without rebinding."""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "original31", ROOT / "coefficients/build_coefficients.py")
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)
data = native.recipe()
geometry = native.check_geometry(data)
padding = native.check_padding(data[5])
_, _, _, support, mu, dc, targets, pads = data
B = 1 << native.D
DC = sum(c << (native.BITS * e) for e, c in dc.items())
DR = 1 << (native.BITS * native.H)
MF0 = 4 + sum(mu << (native.BITS * t) for t in (native.T1, native.T2))
MF0 += sum(1 << (native.BITS * t) for t, *_ in targets)
MF0 += sum(c << (native.BITS * e) for e, c in pads.items())
MC = B - 1 - sum(1 << (native.BITS * e) for e in support if e != 1)
MC -= 2 << (native.BITS * 1063)
values = {"beta": B - 1, "K": DC + B * DR,
          "MC": MC, "MF_source": MF0 + B - 1}
checks = {}
for name, value in values.items():
    raw = value.to_bytes((value.bit_length() + 7) // 8, "little")
    path = ROOT / "coefficients/payloads" / (name + ".bin.gz")
    if raw != gzip.decompress(path.read_bytes()):
        raise ValueError("coefficient reconstruction failed: " + name)
    checks[name] = {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}
out = {"status": "PASS", "geometry": geometry, "padding": padding,
       "ports": checks,
       "scope": "Finite original31 reconstruction from literal transition rows"}
(ROOT / "COEFFICIENT_REBUILD.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"status": "PASS", "ports": len(checks),
                  "raw_bytes": sum(x["bytes"] for x in checks.values())}))

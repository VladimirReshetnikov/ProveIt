#!/usr/bin/env python3
"""Preserve the two initial, explicitly inconclusive precision experiments."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""):h.update(b)
    return h.hexdigest()
rows=[]
for m in [64,128]:
    p=ROOT/"production"/f"m{m:03d}.json"
    trace=Path(str(p)+".trace.gz")
    a=json.loads(p.read_text())
    if a["precision_bits"]!=256 or a["first_negative_certified"] or not a["first_inconclusive_degree"]:
        raise ArithmeticError("unexpected initial experiment")
    rows.append({"m":m,"precision_parameter":256,"first_negative_certified":False,
                 "first_inconclusive_degree":a["first_inconclusive_degree"],
                 "minimum_global_bitlength_margin":a["minimum_margin_bits"],
                 "seconds":a["runtime_seconds"],
                 "pressure_file":str(p.relative_to(ROOT)),"pressure_sha256":sha(p),
                 "trace_file":str(trace.relative_to(ROOT)),"trace_sha256":sha(trace),
                 "producer_source_sha256":sha(ROOT/"first_negative_interval.cpp")})
out={"meaning":"These are preserved inconclusive producer runs, not accepted first-negative certificates.",
     "experiments":rows}
(ROOT/"initial_inconclusive_experiments.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))


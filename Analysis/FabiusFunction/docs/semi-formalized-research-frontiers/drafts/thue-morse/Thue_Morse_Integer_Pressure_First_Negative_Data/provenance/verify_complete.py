#!/usr/bin/env python3
"""Validate accepted coverage, hashes, and both first-negative proofs."""
from pathlib import Path
import hashlib,json,gzip,sys
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with p.open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""):h.update(b)
    return h.hexdigest()
def need(b,s):
    if not b:raise ArithmeticError(s)
meta=json.loads((ROOT/"first_negative_manifest.json").read_text())
need(meta["complete"],"batch incomplete")
need([r["m"] for r in meta["cases"]]==list(range(2,129)),"coverage")
for name,key in [("first_negative_interval.cpp","producer_source_sha256"),("audit_first_negative.cpp","independent_source_sha256")]:
    need(sha(ROOT/name)==meta[key],name)
count=0
for row in meta["cases"]:
    m=row["m"];first=row["first_negative_degree"]
    for key,hashkey in [("production_file","production_sha256"),("trace_file","trace_sha256"),("audit_file","audit_sha256"),("radii_file","radii_sha256")]:
        need(sha(ROOT/row[key])==row[hashkey],f"hash {m} {key}")
    a=json.loads((ROOT/row["production_file"]).read_text())
    b=json.loads((ROOT/row["audit_file"]).read_text())
    for data in (a,b):
        need(data["first_negative_certified"] and data["first_negative_degree"]==first,"first degree")
        need([p["degree"] for p in data["pressure_bounds"]]==list(range(2*m,8*m,2)),"range")
        for p in data["pressure_bounds"]:
            lo=int(p["lower_numerator"]);hi=int(p["upper_numerator"]);d=int(p["denominator"])
            need(d>0 and lo<=hi,"interval")
            if p["degree"]==2*m:need(lo<=0<=hi,"zero")
            elif p["degree"]<first:need(lo>0,"prefix")
            elif p["degree"]==first:need(hi<0,"negative")
    for p,q in zip(a["pressure_bounds"],b["pressure_bounds"]):
        pl,ph,pd=map(int,(p["lower_numerator"],p["upper_numerator"],p["denominator"]))
        ql,qh,qd=map(int,(q["lower_numerator"],q["upper_numerator"],q["denominator"]))
        need(pl*qd<=qh*pd and ql*pd<=ph*qd,"independent intervals disjoint")
    with gzip.open(ROOT/row["radii_file"],"rt") as f:
        need(f.readline().split()==["TMPFIRST_RESIDUAL1",str(m),str(row["precision_bits"])],"radius header")
        for n in range(8*m-1):
            parts=f.readline().split()
            need(len(parts)==3 and int(parts[0])==n and int(parts[1])>=0 and int(parts[2])>=0,"radius state")
            if n==0 or n%2 or n<2*m:need(int(parts[2])==0,"structural scalar radius")
        need(not f.read().strip(),"radius trailing")
    count+=3*m
summary={"passed":True,"cases":127,"pressure_intervals_per_method":count,
 "positive_order_response_states":sum(8*m-2 for m in range(2,129)),
 "production_and_independent_hashes_verified":True,
 "all_first_negative_prefixes_verified":True,
 "all_production_and_independent_intervals_overlap":True}
(ROOT/"complete_validation.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary))


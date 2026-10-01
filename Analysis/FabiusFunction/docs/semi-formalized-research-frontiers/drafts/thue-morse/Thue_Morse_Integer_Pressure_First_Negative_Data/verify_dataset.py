#!/usr/bin/env python3
"""Fast structural/sign verification of the compact delivered certificates."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
DATA=ROOT/"compact"
def need(b,s):
    if not b:raise ArithmeticError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((DATA/"manifest.json").read_text())
accepted_path=ROOT/"first_negative_manifest.json"
accepted=json.loads(accepted_path.read_text())
summary=json.loads((ROOT/"dataset_summary.json").read_text())
need(sha(accepted_path)==summary["accepted_manifest_sha256"],"accepted manifest hash")
need(accepted["complete"] and [r["m"] for r in accepted["cases"]]==list(range(2,129)),"accepted coverage")
for file,key in [("first_negative_interval.cpp","producer_source_sha256"),("audit_first_negative.cpp","independent_source_sha256")]:
    need(sha(ROOT/file)==accepted[key],"proof source hash")
accepted_by_m={r["m"]:r for r in accepted["cases"]}
summary_by_m={r["m"]:r for r in summary["formula_comparison"]}
need(manifest["complete"] and manifest["cases"]==127,"coverage")
need([r["m"] for r in manifest["records"]]==list(range(2,129)),"orders")
comparisons=[];total=0
for row in manifest["records"]:
    p=DATA/row["file"];need(sha(p)==row["sha256"],"compact hash")
    data=json.loads(p.read_text());m=data["m"];first=data["first_negative_degree"]
    need(m==row["m"] and first==row["first_negative_degree"],"identity")
    original=accepted_by_m[m];comparison=summary_by_m[m]
    need(original["first_negative_degree"]==first==comparison["actual"],"accepted value")
    for compact_key,original_key in [("production_sha256","production_sha256"),("independent_sha256","audit_sha256"),("production_trace_sha256","trace_sha256"),("independent_radii_sha256","radii_sha256")]:
        need(data[compact_key]==original[original_key],"original certificate linkage")
    need(comparison["production_sha256"]==original["production_sha256"] and comparison["independent_sha256"]==original["audit_sha256"],"comparison hash linkage")
    need([x["degree"] for x in data["bounds"]]==list(range(2*m,8*m,2)),"degrees")
    need(2*m<first<8*m and first%2==0,"first degree range")
    for x in data["bounds"]:
        lo=int(x["lower_mantissa"]);hi=int(x["upper_mantissa"]);exponent=x["binary_exponent"]
        need(type(exponent) is int and lo<=hi,"dyadic interval")
        need(max(abs(lo),abs(hi))<(1<<96),"mantissa bits")
        if x["degree"]==2*m:need(lo<=0<=hi,"known cancellation")
        elif x["degree"]<first:need(lo>0,"positive prefix")
        elif x["degree"]==first:need(hi<0,"negative endpoint")
        total+=1
    predicted=2*((10*m)//3-1)
    if first!=predicted:comparisons.append([m,first,predicted])
need(total==manifest["pressure_intervals"]==24765,"total intervals")
need(comparisons==[[x["m"],x["actual"],x["predicted"]] for x in summary["all_exceptions"]],"formula comparison")
print(json.dumps({"passed":True,"cases":127,"dyadic_intervals":total,"formula_exceptions":comparisons}))


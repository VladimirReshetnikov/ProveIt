#!/usr/bin/env python3
"""Produce and independently certify first-negative degrees for m=2,...,128."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import hashlib,json,subprocess,time,sys
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent
def sha(p):
    h=hashlib.sha256()
    with Path(p).open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""):h.update(b)
    return h.hexdigest()
def need(b,s):
    if not b:raise ArithmeticError(s)
def read(p):return json.loads(p.read_text())
def check(data,m,audit=False):
    rows=data["pressure_bounds"]
    need(data["m"]==m,"m")
    need([x["degree"] for x in rows]==list(range(2*m,8*m,2)),"degree coverage")
    first=data["first_negative_degree"]
    need(first>2*m and first<8*m and first%2==0,"first scope")
    need(data["first_negative_certified"],"certification flag")
    for x in rows:
        degree=x["degree"];lo=int(x["lower_numerator"]);hi=int(x["upper_numerator"]);den=int(x["denominator"])
        need(den>0 and lo<=hi,"interval order")
        if degree==2*m:need(lo<=0<=hi,"cancellation")
        elif degree<first:need(lo>0,"positive prefix")
        elif degree==first:need(hi<0,"negative endpoint")
    if audit:need(data["trace_orders"]==8*m-1,"response coverage")
    else:need(data["checked_response_orders"]==8*m-2,"response coverage")
    return first
meta={"scope":"m=2,...,128; first even negative coefficient above degree2m",
      "producer_source_sha256":sha(ROOT/"first_negative_interval.cpp"),
      "independent_source_sha256":sha(ROOT/"audit_first_negative.cpp"),
      "producer_binary_sha256":sha(ROOT/"first_negative_interval"),
      "independent_binary_sha256":sha(ROOT/"audit_first_negative"),
      "runner_sha256":sha(Path(__file__)),"cases":[],"complete":False}
def run_tool(args,log):
    with log.open("w") as f:return subprocess.run(args,stdout=f,stderr=subprocess.STDOUT).returncode
def one(m):
    prec=256 if m<=20 else 512+16*m
    if m==64:prec=1536
    attempts=[]
    for retry in range(4):
        name=f"m{m:03d}" if m<=20 and prec==256 else f"m{m:03d}_p{prec}"
        prod=ROOT/"production"/(name+".json")
        trace=Path(str(prod)+".trace.gz")
        if not prod.exists():
            rc=run_tool([str(ROOT/"first_negative_interval"),str(m),str(prec),str(prod)],prod.with_suffix(".log"))
            need(rc in (0,2),"producer execution")
        data=read(prod)
        attempts.append({"precision_bits":prec,"pressure_file":str(prod.relative_to(ROOT)),"pressure_sha256":sha(prod),"trace_sha256":sha(trace)})
        if not data.get("first_negative_certified",False):
            prec*=2;continue
        first=check(data,m)
        target=ROOT/"audit"/(name+".json")
        if not target.exists():
            rc=run_tool([str(ROOT/"audit_first_negative"),str(trace),str(target)],target.with_suffix(".log"))
            need(rc in (0,2),"auditor execution")
        fresh=read(target)
        if not fresh.get("first_negative_certified",False):
            prec*=2;continue
        need(check(fresh,m,True)==first,"independent first agreement")
        rad=Path(str(target)+".radii.gz")
        return {"m":m,"first_negative_degree":first,"precision_bits":prec,
                "production_file":str(prod.relative_to(ROOT)),"production_sha256":sha(prod),
                "trace_file":str(trace.relative_to(ROOT)),"trace_sha256":sha(trace),
                "audit_file":str(target.relative_to(ROOT)),"audit_sha256":sha(target),
                "radii_file":str(rad.relative_to(ROOT)),"radii_sha256":sha(rad),
                "positive_prefix_count":(first-2*m)//2-1,
                "pressure_intervals":3*m,"positive_order_response_states":8*m-2,
                "production_all_signs":data["all_nonzero_signs_certified"],
                "audit_all_signs":fresh["all_nonzero_signs_certified"],
                "production_margin_bits":data["minimum_margin_bits"],
                "producer_seconds":data["runtime_seconds"],"audit_seconds":fresh["seconds"],
                "attempts":attempts}
    raise ArithmeticError(f"m={m} unresolved after precision retries")
start=time.time()
with ThreadPoolExecutor(max_workers=4) as pool:
    futures=[pool.submit(one,m) for m in range(2,129)]
    for f in as_completed(futures):
        row=f.result();meta["cases"].append(row);meta["cases"].sort(key=lambda x:x["m"])
        meta["completed_cases"]=len(meta["cases"]);meta["elapsed_seconds"]=time.time()-start
        (ROOT/"first_negative_manifest.json").write_text(json.dumps(meta,indent=2)+"\n")
        print(json.dumps({"m":row["m"],"first":row["first_negative_degree"],"complete":len(meta["cases"]),"elapsed":meta["elapsed_seconds"]}),flush=True)
need([x["m"] for x in meta["cases"]]==list(range(2,129)),"full coverage")
need(sha(ROOT/"first_negative_interval.cpp")==meta["producer_source_sha256"],"producer stable")
need(sha(ROOT/"audit_first_negative.cpp")==meta["independent_source_sha256"],"audit stable")
meta["complete"]=True
meta["pressure_intervals"]=sum(x["pressure_intervals"] for x in meta["cases"])
meta["positive_order_response_states"]=sum(x["positive_order_response_states"] for x in meta["cases"])
(ROOT/"first_negative_manifest.json").write_text(json.dumps(meta,indent=2)+"\n")
print("COMPLETE",json.dumps({k:meta[k] for k in ["completed_cases","pressure_intervals","positive_order_response_states","elapsed_seconds"]}),flush=True)


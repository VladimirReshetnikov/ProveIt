#!/usr/bin/env python3
"""Exact outward rounding of the hull of two certified rational intervals."""
from pathlib import Path
import json,hashlib,sys
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent
def need(b,s):
    if not b:raise ArithmeticError(s)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def floor_log2_ratio(p,d):
    need(p>0 and d>0,"log2 domain")
    q=p.bit_length()-d.bit_length()
    below=(p < (d<<q)) if q>=0 else ((p<<(-q)) < d)
    if below:q-=1
    # Independently check both exact inequalities.
    low=(p >= (d<<q)) if q>=0 else ((p<<(-q)) >= d)
    q1=q+1
    high=(p < (d<<q1)) if q1>=0 else ((p<<(-q1)) < d)
    need(low and high,"exact binary exponent")
    return q
def floor_scaled(n,d,e):
    return n//(d<<e) if e>=0 else (n<<(-e))//d
def ceil_scaled(n,d,e):return -floor_scaled(-n,d,e)
def dyadic_le_rational(z,e,n,d):
    return (z<<e)*d<=n if e>=0 else z*d<=(n<<(-e))
def rational_le_dyadic(n,d,z,e):
    return n<=(z<<e)*d if e>=0 else (n<<(-e))<=z*d
meta=json.loads((ROOT/"first_negative_manifest.json").read_text())
need(meta["complete"],"batch incomplete")
out=ROOT/"compact";out.mkdir(exist_ok=True)
records=[];rounding_checks=0;prefix_checks=0
for row in meta["cases"]:
    m=row["m"]
    pa=ROOT/row["production_file"];pb=ROOT/row["audit_file"]
    need(sha(pa)==row["production_sha256"] and sha(pb)==row["audit_sha256"],"input hash")
    a=json.loads(pa.read_text())["pressure_bounds"];b=json.loads(pb.read_text())["pressure_bounds"]
    bounds=[]
    for x,y in zip(a,b):
        need(x["degree"]==y["degree"],"degree")
        values=[(int(x["lower_numerator"]),int(x["denominator"])),
                (int(x["upper_numerator"]),int(x["denominator"])),
                (int(y["lower_numerator"]),int(y["denominator"])),
                (int(y["upper_numerator"]),int(y["denominator"]))]
        qs=[floor_log2_ratio(abs(n),d) for n,d in values if n]
        need(qs,"nontrivial interval")
        e=max(qs)-95
        while True:
            L=min(floor_scaled(n,d,e) for n,d in values)
            U=max(ceil_scaled(n,d,e) for n,d in values)
            if max(abs(L),abs(U))<(1<<96):break
            e+=1
        for interval in (x,y):
            lo=int(interval["lower_numerator"]);hi=int(interval["upper_numerator"]);d=int(interval["denominator"])
            need(dyadic_le_rational(L,e,lo,d),"lower outward rounding")
            need(rational_le_dyadic(hi,d,U,e),"upper outward rounding")
            rounding_checks+=2
        degree=x["degree"]
        if degree==2*m:need(L<=0<=U,"zero")
        elif degree<row["first_negative_degree"]:
            need(L>0,"rounded positive prefix");prefix_checks+=1
        elif degree==row["first_negative_degree"]:
            need(U<0,"rounded negative endpoint");prefix_checks+=1
        bounds.append({"degree":degree,"lower_mantissa":str(L),"upper_mantissa":str(U),"binary_exponent":e})
    data={"m":m,"first_negative_degree":row["first_negative_degree"],
          "meaning":"coefficient lies between lower_mantissa*2^binary_exponent and upper_mantissa*2^binary_exponent",
          "mantissa_bits_at_most":96,
          "production_sha256":row["production_sha256"],"independent_sha256":row["audit_sha256"],
          "production_trace_sha256":row["trace_sha256"],"independent_radii_sha256":row["radii_sha256"],
          "bounds":bounds}
    path=out/f"m{m:03d}.json";path.write_text(json.dumps(data,indent=2)+"\n")
    records.append({"m":m,"first_negative_degree":row["first_negative_degree"],"file":path.name,"sha256":sha(path)})
summary={"complete":True,"cases":len(records),"pressure_intervals":sum(3*m for m in range(2,129)),
         "exact_outward_rounding_inequalities":rounding_checks,"prefix_and_endpoint_sign_checks":prefix_checks,
         "binary_exponents_selected_by_integer_comparisons":True,"records":records}
(out/"manifest.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps({k:v for k,v in summary.items() if k!="records"}))


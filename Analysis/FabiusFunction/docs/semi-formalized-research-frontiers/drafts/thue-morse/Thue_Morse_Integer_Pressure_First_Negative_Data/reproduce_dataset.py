#!/usr/bin/env python3
"""Reproduce selected finite certificates from the two C++ proof programs."""
from pathlib import Path
import argparse,subprocess,json,concurrent.futures,sys
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument("--m",type=int,nargs="+",help="orders to reproduce, each between2 and128")
parser.add_argument("--all",action="store_true",help="reproduce all127 cases; substantial runtime and disk use")
parser.add_argument("--workers",type=int,default=1)
args=parser.parse_args()
if args.all==bool(args.m):parser.error("choose exactly one of --m or --all")
orders=list(range(2,129)) if args.all else sorted(set(args.m))
if any(m<2 or m>128 for m in orders) or args.workers<1:parser.error("invalid domain")
OUT=ROOT/"replay";OUT.mkdir(exist_ok=True)
for name in ["first_negative_interval","audit_first_negative"]:
    subprocess.run(["g++","-O2","-std=c++17",str(ROOT/(name+".cpp")),"-lgmpxx","-lgmp","-lz","-o",str(OUT/name)],check=True)
manifest=json.loads((ROOT/"first_negative_manifest.json").read_text())
by_m={row["m"]:row for row in manifest["cases"]}
def need(b,s):
    if not b:raise ArithmeticError(s)
def dyadic_le(z,e,n,d):return (z<<e)*d<=n if e>=0 else z*d<=n<<(-e)
def rational_le(n,d,z,e):return n<=(z<<e)*d if e>=0 else n<<(-e)<=z*d
def one(m):
    row=by_m[m];prod=OUT/f"m{m:03d}.json";audit=OUT/f"m{m:03d}_audit.json"
    with (OUT/f"m{m:03d}.log").open("w") as log:
        subprocess.run([str(OUT/"first_negative_interval"),str(m),str(row["precision_bits"]),str(prod)],stdout=log,stderr=subprocess.STDOUT,check=True)
        subprocess.run([str(OUT/"audit_first_negative"),str(prod)+".trace.gz",str(audit)],stdout=log,stderr=subprocess.STDOUT,check=True)
    compact=json.loads((ROOT/"compact"/f"m{m:03d}.json").read_text())
    first=compact["first_negative_degree"]
    for path in [prod,audit]:
        data=json.loads(path.read_text())
        need(data["first_negative_certified"] and data["first_negative_degree"]==first,"first negative mismatch")
        need([x["degree"] for x in data["pressure_bounds"]]==list(range(2*m,8*m,2)),"coverage")
        for q,c in zip(data["pressure_bounds"],compact["bounds"]):
            lo=int(q["lower_numerator"]);hi=int(q["upper_numerator"]);d=int(q["denominator"])
            L=int(c["lower_mantissa"]);U=int(c["upper_mantissa"]);e=c["binary_exponent"]
            need(dyadic_le(L,e,lo,d) and rational_le(hi,d,U,e),"delivered dyadic interval does not enclose replay")
            if 2*m<q["degree"]<first:need(lo>0,"prefix")
            if q["degree"]==first:need(hi<0,"endpoint")
    print(json.dumps({"m":m,"first_negative_degree":first,"both_methods_reproduced":True}),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:list(pool.map(one,orders))


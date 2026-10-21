#!/usr/bin/env python3
"""Fresh-compile the exact bundled 13-module Lean closure through KCodeDom.

  python3 build.py --lean /path/to/lean
Requires Lean 4.32.0. Every dependency is rebuilt from the bundled source.
"""
import argparse,datetime,hashlib,json,os,subprocess,time
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument("--lean",default=os.environ.get("LEAN","lean"))
ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parent/"formal")
args=ap.parse_args()
root=args.root.resolve();out=root.parent/"verification";out.mkdir(exist_ok=True)
seen=set();order=[]
def visit(name):
    if name in seen:return
    seen.add(name);p=root/(name.replace(".","/")+".lean")
    if not p.exists():raise FileNotFoundError(name)
    for line in p.read_text().splitlines():
        if line.startswith("import "):
            for dep in line[7:].split():
                if dep!="Init":visit(dep)
    order.append(name)
visit("BusyBeaver.ZFC.KCodeDom")
assert len(order)==13,("unexpected dependency closure",order)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={"status":"RUNNING","timestamp_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "scope":"Fresh 13-module logical interface closure through unchanged KCodeDom; not a full machine-to-ZFC endpoint rebuild.",
 "compiler":subprocess.check_output([args.lean,"--version"],text=True).strip(),"records":[]}
env=dict(os.environ,LEAN_PATH=str(root))
# Clear all compiled artifacts in the local closure before starting.
for name in order:
    p=root/(name.replace(".","/")+".lean")
    for ext in (".olean",".ilean",".olean.server",".olean.private"):
        p.with_suffix(ext).unlink(missing_ok=True)
for name in order:
    p=root/(name.replace(".","/")+".lean");obj=p.with_suffix(".olean");log=out/(name+".log")
    cmd=[args.lean,"-o",str(obj),str(p)]
    start=time.monotonic()
    result=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    log.write_text(result.stdout)
    rec={"module":name,"source_sha256":sha(p),"exit_code":result.returncode,
         "seconds":round(time.monotonic()-start,3),"command":cmd,
         "log":log.name,"log_sha256":sha(log)}
    if result.returncode==0:rec["object_sha256"]=sha(obj)
    report["records"].append(rec)
    print(name,result.returncode,flush=True)
    if result.stdout:print(result.stdout,flush=True)
    if result.returncode:
        report["status"]="FAILED";(out/"kernel_receipt.json").write_text(json.dumps(report,indent=2)+"\n")
        raise SystemExit(result.returncode)
report["status"]="PASS_FRESH_MINIMAL_CLOSURE"
(out/"kernel_receipt.json").write_text(json.dumps(report,indent=2)+"\n")
print(report["status"],flush=True)

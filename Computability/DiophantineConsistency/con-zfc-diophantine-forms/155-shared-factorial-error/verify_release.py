#!/usr/bin/env python3
"""Reproduce exact finite checks using only Python's standard library."""
from pathlib import Path
from datetime import datetime,timezone
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def seal_check():
    manifest=ROOT/"MANIFEST.sha256"
    if not manifest.exists():return {"present":False}
    count=0
    for line in manifest.read_text().splitlines():
        if not line:continue
        digest,name=line.split("  ",1);path=ROOT/name
        need(path.is_file(),"Missing sealed file: "+name)
        need(hashlib.sha256(path.read_bytes()).hexdigest()==digest,"Seal mismatch: "+name)
        count+=1
    return {"present":True,"files":count,"status":"PASS"}

def run(cwd,script,*args):
    flags=["-B"]+(["-O"] if sys.flags.optimize else [])
    p=subprocess.run([sys.executable,*flags,str(cwd/script),*args],
                     cwd=cwd,capture_output=True,text=True)
    need(p.returncode==0,"Failed "+script+"\n"+p.stdout+"\n"+p.stderr)
    try:return json.loads(p.stdout)
    except json.JSONDecodeError:return {"status":"PASS","stdout":p.stdout.strip()}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--rebuild",action="store_true")
    parser.add_argument("--manifest-only",action="store_true")
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args();start=time.monotonic()
    report={"status":"PASS","python":sys.version.split()[0],
            "optimized":bool(sys.flags.optimize),"manifest":seal_check(),
            "time_utc":datetime.now(timezone.utc).isoformat()}
    if not args.manifest_only:
        eq=ROOT/"equations"
        report["parent"]=run(eq/"parent252","code/verify.py")
        report["core244"]=run(eq,"verify_unified_bootstrap.py","--affine-radix")
        report["profiles"]=[
          run(eq,"verify_affine.py","--profile",profile)
          for profile in ("equation240","equation241_affine_balanced","equation241_affine")]
        report["printed_equation"]=run(ROOT,"verify_report.py")
        report["finite_factorial_samples"]=run(ROOT,"verify_factorial_lemma.py")
        if args.rebuild:
            with tempfile.TemporaryDirectory(prefix="conzfc-shared-factorial-") as td:
                fresh=Path(td)/"equations"
                shutil.copytree(eq,fresh,ignore=shutil.ignore_patterns("__pycache__","*.pyc"))
                commands=[
                  ("build249.py",),
                  ("build_unified_bootstrap.py","--affine-radix"),
                  ("build_affine.py","--affine-radix"),
                  ("build_affine.py","--affine-radix","--dense"),
                  ("reduce_rows.py","--affine-radix"),
                  ("reduce_rows.py","--affine-radix","--dense"),
                  ("select_balanced.py","--affine-radix")]
                results=[run(fresh,cmd[0],*cmd[1:]) for cmd in commands];count=0
                for folder in ("candidate244","candidate241_affine","candidate240_affine",
                               "equation240","equation241_affine","equation241_affine_balanced"):
                    originals=sorted((eq/folder).glob("*.json"))
                    generated=sorted((fresh/folder).glob("*.json"))
                    need([p.name for p in originals]==[p.name for p in generated],
                         "Rebuild file census differs: "+folder)
                    for a,b in zip(originals,generated):
                        need(a.read_bytes()==b.read_bytes(),"Rebuild bytes differ: "+folder+"/"+a.name)
                        count+=1
                report["rebuild"]={"status":"PASS","byte_identical_json_files":count,
                                   "build_steps":len(commands),"step_results":results}
    report["elapsed_seconds"]=round(time.monotonic()-start,3)
    report["scope"]="Exact finite artifacts and documented sanity checks; the unbounded equivalence is proved in the report and inherited source closure."
    rendered=json.dumps(report,sort_keys=True,indent=2)+"\n"
    if args.receipt:args.receipt.write_text(rendered)
    print(rendered,end="")

if __name__=="__main__":main()

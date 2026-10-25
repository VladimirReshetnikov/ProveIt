#!/usr/bin/env python3
"""Offline exact verification; no search for roots or consistency test."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,time,zipfile
ROOT=Path(__file__).resolve().parent
def need(p,m):
 if not p:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(script,*args,cwd=ROOT):
 flags=["-B"]+(["-O"] if sys.flags.optimize else [])
 p=subprocess.run([sys.executable,*flags,str(script),*map(str,args)],cwd=cwd,
                  capture_output=True,text=True)
 need(p.returncode==0,"Failed "+str(script)+"\n"+p.stdout+"\n"+p.stderr)
 try:return json.loads(p.stdout)
 except json.JSONDecodeError:return {"status":"PASS","output":p.stdout.strip()}
def manifest():
 path=ROOT/"MANIFEST.sha256"
 if not path.exists():return {"present":False}
 count=0
 for line in path.read_text().splitlines():
  h,name=line.split("  ",1)
  need((ROOT/name).is_file() and sha(ROOT/name)==h,"Manifest mismatch: "+name)
  count+=1
 return {"status":"PASS","files":count}
def source_bindings():
 ledger=json.loads((ROOT/"SOURCE_LEDGER.json").read_text())
 for a in ledger["archives"]:
  need(sha(ROOT/a["local_path"])==a["sha256"],"Archive hash mismatch")
 for a in ledger["calibration_excerpts"]:
  need(sha(ROOT/a["local_path"])==a["sha256"],"Calibration excerpt hash mismatch")
 checks=[]
 for profile in ("shared240_balanced","shared240_lowheight","factorialfree241"):
  folder=ROOT/"projection"/profile
  cert=json.loads((folder/"projection_certificate.json").read_text())
  archive=(ROOT/"sources"/("ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip"
           if profile=="factorialfree241" else "ConZFC_Shared_Factorial_Error_2026-10-25.zip"))
  with zipfile.ZipFile(archive) as z:
   raw=z.read(cert["source_path"])
  need(raw==(folder/"source_equation.json").read_bytes(),"Actual archive source mismatch")
  need(hashlib.sha256(raw).hexdigest()==cert["source_sha256"],"Projection source hash mismatch")
  checks.append(profile)
 for gram,project in (("balanced","shared240_balanced"),("lowheight","shared240_lowheight")):
  need((ROOT/"gram"/gram/"source_equation.json").read_bytes()
       ==(ROOT/"projection"/project/"equation.json").read_bytes(),
       "Gram input does not equal actual projected equation")
 for source,target in (("source_equation.json","equation.json"),
                       ("source_expanded_polynomial.json","expanded_polynomial.json")):
  need((ROOT/"finite_theory"/source).read_bytes()
       ==(ROOT/"gram/balanced"/target).read_bytes(),
       "Finite-theory source does not equal principal Gram polynomial")
 return {"status":"PASS","bound_sources":checks,"gram_bindings":2,
         "finite_theory_bindings":2,"calibration_excerpts":len(ledger["calibration_excerpts"])}
def rebuild():
 count=0
 with tempfile.TemporaryDirectory(prefix="conzfc-integral-rebuild-") as td:
  tmp=Path(td);shutil.copytree(ROOT/"projection",tmp/"projection")
  run(tmp/"projection/build.py",cwd=tmp/"projection")
  for old in sorted((ROOT/"projection").rglob("*.json")):
   rel=old.relative_to(ROOT/"projection")
   need(old.read_bytes()==(tmp/"projection"/rel).read_bytes(),"Projection rebuild mismatch: "+str(rel))
   count+=1
 gram=run(ROOT/"gram/build.py","--check")
 finite_theory=run(ROOT/"finite_theory/build.py","--check")
 return {"status":"PASS","projection_json_files":count,"gram":gram,
         "finite_theory":finite_theory}
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--rebuild",action="store_true")
 p.add_argument("--receipt",type=Path)
 p.add_argument("--skip-manifest",action="store_true")
 p.add_argument("--manifest-only",action="store_true")
 a=p.parse_args();start=time.monotonic()
 result={"status":"PASS","python":sys.version.split()[0],"optimized":bool(sys.flags.optimize)}
 if not a.skip_manifest:result["manifest"]=manifest()
 if not a.manifest_only:
  result["source_bindings"]=source_bindings()
  result["projections"]=run(ROOT/"projection/check.py")
  result["gram_balanced"]=run(ROOT/"gram/check_gram.py",ROOT/"gram/balanced")
  result["gram_lowheight"]=run(ROOT/"gram/check_gram.py",ROOT/"gram/lowheight")
  result["report"]=run(ROOT/"build_report.py","--check")
  result["printed_equation"]=run(ROOT/"check_printed_equation.py")
  result["finite_theory"]=run(ROOT/"finite_theory/check.py")
  if a.rebuild:result["rebuild"]=rebuild()
 result["elapsed_seconds"]=round(time.monotonic()-start,3)
 result["scope"]="Exact finite algebra and source identities; ordinary proofs and named inherited calibration supply the unbounded theorem."
 text=json.dumps(result,indent=2,sort_keys=True)+"\n"
 if a.receipt:a.receipt.write_text(text)
 print(text,end="")
if __name__=="__main__":main()

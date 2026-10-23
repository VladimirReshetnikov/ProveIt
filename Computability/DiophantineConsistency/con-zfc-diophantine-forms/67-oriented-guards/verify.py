#!/usr/bin/env python3
"""Authenticate the sealed release and replay all finite checks in a temporary copy."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
STAGES=['build_sections.py', 'encoding/verify_split.py', 'encoding/test_split.py', 'encoding/check_carry.py', 'quartic/build_verify.py', 'quartic/build_projections.py', 'review/quartic42/check_literal.py', 'review/projections/check.py', 'nine/build_nine.py', 'nine/check_ring.py', 'nine/check_nine.py', 'nine/test_corruption.py', 'nine/review/check_nine_independent.py', 'nine/review/check_majorant_sympy.py', 'signed/reproduce.py', 'signed108/reproduce.py', 'signed108trim/reproduce.py', 'signed13/reproduce.py', 'positive/build.py', 'positive/check.py', 'positive/negative_controls.py', 'review/positive14/check_independent.py', 'root_checks/check_endpoints.py', 'quartic/check_tex_residuals.py', 'root_checks/check_bindings.py']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def authenticate(root):
 manifest=json.loads((root/'SHA256SUMS.json').read_text())
 for name,h in manifest.items():
  p=root/name
  if not p.is_file() or digest(p)!=h:raise ValueError('Missing or changed release file: '+name)
 return manifest

def main():
 if sys.flags.optimize:raise SystemExit('Run the root replay without -O; separate optimized checker receipts are supplied.')
 manifest=authenticate(ROOT)
 generated=json.loads((ROOT/'REBUILD_FILES.json').read_text())
 reports=[]
 with tempfile.TemporaryDirectory(prefix='proveit-wave9-') as td:
  work=Path(td)/'release';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0')
  for stage in STAGES:
   p=subprocess.run([sys.executable,str(work/stage)],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if p.returncode:
    print(p.stdout);raise RuntimeError('Replay failed: '+stage)
   reports.append({'stage':stage,'status':'PASS'});print('PASS '+stage,flush=True)
  for name in generated:
   p=work/name
   if not p.is_file() or p.read_bytes()!=(ROOT/name).read_bytes():raise ValueError('Rebuilt bytes differ: '+name)
 receipt={'status':'PASS','stage_count':len(reports),'stages':reports,'byte_identical_rebuilt_files':len(generated),'sealed_files':len(manifest),'scope':'Finite exact data, identities, degree and reproducibility checks; not an unbounded compiler theorem or new kernel certificate.'}
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

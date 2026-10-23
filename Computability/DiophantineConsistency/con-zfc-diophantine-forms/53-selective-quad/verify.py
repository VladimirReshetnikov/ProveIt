#!/usr/bin/env python3
"""Authenticate the sealed release and replay all finite checks in a temporary copy."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
STAGES=[
 'weights/verify_selective.py','weights/test_selective.py',
 'packing/mask_popcount/reproduce.py',
 'nine/build_nine.py','nine/verify_nine.py',
 'jones/build_jones.py','jones/check_jones.py','jones/independent_seeded_audit.py',
 'batching/build_eleven.py','batching/check_eleven.py',
 'elimination/audit_eleven.py','elimination/audit_package.py',
 'short/build_relaxed.py','short/audit_relaxed.py','short/independent_literal_audit.py',
 'root_checks/check_popcount_bridge.py','root_checks/check_sparse_padding.py',
 'root_checks/check_seeded_norm.py','root_checks/check_square_threshold_padding.py',
 'root_checks/check_calibrated_block.py','root_checks/check_nine_degree_independent.py']
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
 with tempfile.TemporaryDirectory(prefix='proveit-wave7-') as td:
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

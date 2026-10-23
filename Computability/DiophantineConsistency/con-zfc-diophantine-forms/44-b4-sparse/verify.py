#!/usr/bin/env python3
"""Authenticate this release and replay deterministic checks in an isolated copy."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
STAGES=[
 'root_checks/bose_chowla.py','root_checks/optimize_bose.py',
 'sun/build_sun_b4.py','sun/verify_sun_b4.py',
 'signed_audit/build_signed_b4.py','signed_audit/check_signed_b4.py',
 'nine/build_nine_b4.py','nine/verify_nine_b4.py',
 'positive/build_positive.py','positive/check_positive.py',
 'native/build_coefficients.py','native/audit_coefficients.py',
 'quartic/audit_eliminations.py','quartic/check_sun_b4_independent.py',
 'root_checks/check_sparse_digit.py','root_checks/check_complement_clause.py',
 'root_checks/check_norm_and_guard.py','root_checks/check_dag_structure.py',
 'root_checks/independent_release_checks.py']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def authenticate(root):
 manifest=json.loads((root/'SHA256SUMS.json').read_text())
 for p,h in manifest.items():
  q=root/p
  if not q.is_file() or digest(q)!=h:raise ValueError('Missing or changed release file: '+p)
 return manifest
def main():
 if sys.flags.optimize:raise SystemExit('Run without -O: some inherited finite checkers use assertions.')
 manifest=authenticate(ROOT)
 generated=json.loads((ROOT/'REBUILD_FILES.json').read_text())
 reports=[]
 with tempfile.TemporaryDirectory(prefix='proveit-wave6-') as tmp:
  work=Path(tmp)/'release';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1')
  for stage in STAGES:
   r=subprocess.run([sys.executable,str(work/stage)],cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if r.returncode:
    print(r.stdout);raise RuntimeError('Replay failed: '+stage)
   reports.append({'stage':stage,'status':'PASS'})
   print('PASS '+stage,flush=True)
  for p in generated:
   if not (work/p).is_file() or (work/p).read_bytes()!=(ROOT/p).read_bytes():raise ValueError('Rebuilt bytes differ: '+p)
 receipt={'status':'PASS','stages':reports,'stage_count':len(reports),'byte_identical_rebuilt_files':len(generated),'sealed_files':len(manifest),'scope':'Finite reproducibility and certificates, not unbounded solvability or a new formal endpoint.'}
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

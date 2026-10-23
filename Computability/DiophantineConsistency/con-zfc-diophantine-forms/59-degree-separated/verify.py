#!/usr/bin/env python3
"""Authenticate the sealed release and replay all finite checks in a temporary copy."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
STAGES=['build_sections.py', 'encoding/verify_split.py', 'encoding/test_split.py', 'sun/reproduce.py', 'nine/build_nine.py', 'nine/verify_nine.py', 'nine/independent_review.py', 'signed/build_jones.py', 'signed/check_jones.py', 'signed/check_source_minimum_independent.py', 'positive/build_ordinary_merger.py', 'positive/check_ordinary_merger.py', 'positive/check_merger_independent.py', 'short/build.py', 'short/audit.py', 'root_checks/check_coprime_spectator.py', 'root_checks/check_primary_circuits.py', 'root_checks/check_dependency_metadata.py', 'nine_free_adjunct/build_nine.py', 'nine_free_adjunct/verify_nine.py', 'nine_free_adjunct/check_source_independent.py', 'nine_free_adjunct/independent_review.py', 'positive13_adjunct/build.py', 'positive13_adjunct/check.py', 'review/POSITIVE13_ADJUNCT_INDEPENDENT.py']
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
 with tempfile.TemporaryDirectory(prefix='proveit-wave8-') as td:
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

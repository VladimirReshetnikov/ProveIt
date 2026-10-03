#!/usr/bin/env python3
"""Portable exact replay for the smaller template 26 last-gap proof."""
import os,sys
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise SystemExit('Run with assertions enabled, without -O/-OO or PYTHONOPTIMIZE.')
import argparse,hashlib,json,shutil,subprocess,tempfile,time,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SHARED='/workspace/shared/'
AUDIT='preorder-gamma-degree4-independent-audit/structural-template26'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def manifest():
 count=0
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  h,name=line.split('  ',1);p=Path(name)
  require(not p.is_absolute() and '..' not in p.parts,'Unsafe manifest path')
  require(digest(ROOT/p)==h,'Manifest mismatch: '+name);count+=1
 return count
def pinned_receipt(name):
 p=ROOT/'sources'/AUDIT/name;r=json.loads(p.read_text())
 require(r['verdict'] in ('approved','approved valid smaller replacement proof of template26 last gap'),'Unapproved proof: '+name)
 for name,h in r['sha256'].items():
  require(name.startswith(SHARED),'Unknown provenance path: '+name)
  q=ROOT/'sources'/name[len(SHARED):]
  require(q.is_file() and digest(q)==h,'Proof dependency mismatch: '+name)
 return digest(p)
def extract_safe(path,dest):
 with zipfile.ZipFile(path) as z:
  require(z.testzip() is None,'Corrupt dependency ZIP')
  for n in z.namelist():
   p=Path(n);require(not p.is_absolute() and '..' not in p.parts,'Unsafe archive member')
  z.extractall(dest)
def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--verify-dependency',action='store_true',help='Also replay the included vertex-weighted degree-three dependency (requires g++).')
 a=parser.parse_args();start=time.perf_counter();count=manifest()
 pins=[pinned_receipt('deletion_mixture_approval_receipt.json'),pinned_receipt('template26_smaller_proof_approval_receipt.json')]
 results={}
 with tempfile.TemporaryDirectory(prefix='template26-exact-') as temp:
  stage=Path(temp)/'sources';shutil.copytree(ROOT/'sources',stage)
  out=stage/AUDIT
  # Fresh receipts, never historical successes, drive the following checks.
  for name in ['deletion_mixture_algebra_receipt.json','template26_assembly_algebra_receipt.json']:
   (out/name).unlink(missing_ok=True)
  for name in ['audit_deletion_mixture.py','audit_template26_assembly.py']:
   p=out/name;s=p.read_text();p.write_text(s.replace('/workspace/shared',str(stage)))
   print('Running',name,flush=True)
   subprocess.run([sys.executable,str(p)],cwd=stage,check=True)
  mix=json.loads((out/'deletion_mixture_algebra_receipt.json').read_text())
  asm=json.loads((out/'template26_assembly_algebra_receipt.json').read_text())
  require(mix['verdict']=='PASS' and mix['kernel_quotas']==56 and mix['distinct_pairs']==10 and mix['square_terms']==196 and mix['positive_remainder_terms']==846,'Mixture coverage mismatch')
  require(asm['verdict']=='PASS' and asm['quota_vectors']==1365 and asm['all_scalar_coefficients']==6825,'Assembly coverage mismatch')
  results['mixture']={k:mix[k] for k in ['kernel_quotas','kernel_coefficients','distinct_pairs','square_terms','positive_remainder_terms']}
  results['assembly']={k:asm[k] for k in ['quota_vectors','all_scalar_coefficients','nonzero_coefficients']}
  if a.verify_dependency:
   dest=Path(temp)/'dependency';extract_safe(ROOT/'dependencies/weighted-degree-three-package.zip',dest)
   child=dest/'weighted-degree-three-result';subprocess.run([sys.executable,str(child/'verify.py')],cwd=child,check=True)
   result=child/'local-replay.json';require(result.is_file(),'Missing dependency replay receipt')
   results['dependency_replay']=json.loads(result.read_text())
 receipt={'verdict':'PASS','scope':'Unweighted template 26 last order-four gap at nonnegative integer populations. Ordinary arguments reviewed in pinned approval receipts; exact local algebra freshly replayed.','files_hashed':count,'approval_receipt_hashes':pins,'dependency':'fully replayed' if a.verify_dependency else 'included and hash-pinned; use --verify-dependency for full replay','checks':results,'seconds':time.perf_counter()-start}
 (ROOT/'local-replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

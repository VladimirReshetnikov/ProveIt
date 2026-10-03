#!/usr/bin/env python3
"""Manifest-bound exact, symbolic and numerical compacted-DAG replay.
No network or package installation. All generated files go under output/.
"""
import argparse, hashlib, json, shutil, subprocess, sys, time
import importlib.metadata
from pathlib import Path

def verify_manifest(path):
 root=path.parent;count=0
 for line in path.read_text().splitlines():
  digest,name=line.split('  ',1);target=root/name
  assert target.is_file(),f'Missing input: {name}'
  assert hashlib.sha256(target.read_bytes()).hexdigest()==digest,f'Changed input: {name}'
  count+=1
 return count

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--manifest-only',action='store_true');args=parser.parse_args()
 root=Path(__file__).resolve().parent
 checked=verify_manifest(root/'SHA256SUMS')
 if args.manifest_only: print(f'{checked} manifest-bound input files verified');return
 output=root/'output';output.mkdir(exist_ok=True);work=output/'mathematical-replay';work.mkdir(exist_ok=True)
 cases=[('exact_positive_kernels','verify_positive_kernel.py',None),('formal_coefficients','formal_compacted.py','formal-coefficients.json'),('independent_coefficients','audit_compacted_coefficients.py',None),('shared_jacobi','check_shared_jacobi.py','check_shared_jacobi.json'),('delay_operator','check_delay_operator.py','delay-operator-check.json'),('inverse','inverse_check.py','inverse_check.json'),('exact_forward_evidence','check_forward.py','forward-check.json')]
 results={};start=time.monotonic()
 for name,script,jsonfile in cases:
  shutil.copy2(root/'checks'/script,work/script)
  tick=time.monotonic()
  run=subprocess.run([sys.executable,str(work/script)],cwd=work,capture_output=True,text=True,check=True)
  (output/(name+'.stdout.log')).write_text(run.stdout);(output/(name+'.stderr.log')).write_text(run.stderr)
  data=json.loads((work/jsonfile).read_text() if jsonfile else run.stdout)
  (output/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
  results[name]={'status':'passed','seconds':time.monotonic()-tick,'output':name+'.json'}
  print(name,'passed',flush=True)
 import sympy as s
 author=json.loads((output/'formal_coefficients.json').read_text());auditor=json.loads((output/'independent_coefficients.json').read_text())
 assert all(s.simplify(s.sympify(a)-s.sympify(b))==0 for a,b in zip(author['logforward_n'],auditor['logforward_n']))
 assert all(s.simplify(s.sympify(author['s'][k])-s.sympify(auditor['s'][k]))==0 for k in author['s'])
 a,x=s.symbols('a x')
 for degree,expression in author['s'].items():
  for (r,),coef in s.Poly(s.sympify(expression),a).terms():
   assert (r+int(degree))%3==0
 for degree,(pp,qq) in enumerate(author['profiles']):
  P,Q=map(s.sympify,(pp,qq))
  if degree:
   assert s.simplify(Q.subs(x,0))==0
   assert s.simplify((P+s.diff(Q,x)).subs(x,0))==0
  for (r,j),coef in s.Poly(P,a,x).terms():
   assert coef==0 or (degree+r+j)%3==0
  for (r,j),coef in s.Poly(Q,a,x).terms():
   assert coef==0 or (degree+r+j-1)%3==0
 exact=json.loads((output/'exact_positive_kernels.json').read_text());gold=json.loads((root/'fixtures/verify_positive_kernel_results.json').read_text())
 assert exact==gold,'Exact finite-state results differ from approved fixture'
 post=verify_manifest(root/'SHA256SUMS');assert post==checked
 result={'status':'passed','runtime':{'python':sys.version,'packages':{name:importlib.metadata.version(name) for name in ['sympy','mpmath','numpy','scipy']}},'manifest_sha256':hashlib.sha256((root/'SHA256SUMS').read_bytes()).hexdigest(),'manifest_bound_input_files':checked,'elapsed_seconds':time.monotonic()-start,'cases':results,'independent_coefficient_agreement':'exact symbolic equality','profile_boundary_and_mod3_grading':'exactly verified at every computed order','exact_fixture_agreement':True,'inputs_unchanged_after_replay':True,'numeric_scope':'Numerical diagnostics and fitted amplitudes are evidence only; not rigorous enclosures.'}
 (output/'replay-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

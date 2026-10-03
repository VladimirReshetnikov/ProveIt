#!/usr/bin/env python3
"""Run the authored evidence in normal and optimized Python; compare receipts."""
from pathlib import Path
import ast,hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
CHECKS=[
 ('gates',['gates/check_gates.py'],'gates/gate_receipt.json'),
 ('ca',['ca/test_lazy_u15.py'],'ca/verification.json'),
 ('router',['geometry/periodic_router.py','--output','geometry/router_checks.json'],'geometry/router_checks.json'),
 ('circuit',['compiler/literal_loader.py','--audit'],'compiler/circuit_manifest.json'),
 ('coefficients',['compiler/test_coefficients.py'],'compiler/coefficient_checks.json'),
 ('worked_example',['compiler/make_example.py'],'compiler/worked_example.json')]

def require(ok,detail):
 if not ok:raise AssertionError(detail)
def main():
 pure=ROOT/'data/u15_table.json'
 require(hashlib.sha256(pure.read_bytes()).hexdigest()=='0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a','pinned table hash mismatch')
 for p in ROOT.rglob('*.py'):
  require(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse(p.read_text()))),('optimization-disabled assertion',str(p)))
 rows=[]
 for name,args,receipt in CHECKS:
  hashes=[];stdout=[]
  for mode in ([],['-O']):
   r=subprocess.run([sys.executable,*mode,*args],cwd=ROOT,text=True,capture_output=True)
   require(r.returncode==0,(name,mode,r.stdout,r.stderr))
   hashes.append(hashlib.sha256((ROOT/receipt).read_bytes()).hexdigest())
   stdout.append(r.stdout)
  require(hashes[0]==hashes[1] and stdout[0]==stdout[1],('normal/-O mismatch',name))
  rows.append({'check':name,'status':'PASS','receipt':receipt,'normal_and_optimized_receipt_sha256':hashes[0]})
  print(name,'PASS',flush=True)
 out={'status':'PASS','normal_and_optimized_equal':True,'no_assert_statements':True,
      'pinned_u15_sha256':hashlib.sha256(pure.read_bytes()).hexdigest(),'checks':rows}
 (ROOT/'VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()

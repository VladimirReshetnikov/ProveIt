#!/usr/bin/env python3
"""Read-only release verification with independent exact temporary replays."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time

ROOT=Path(__file__).resolve().parent
JOBS=[
 ('producer-boundary','reproducibility/producer-boundary/universal_boundary_check.py','universal_boundary_receipt.json'),
 ('independent-boundary','reproducibility/independent-boundary/independent_boundary_check.py','independent_receipt.json'),
 ('producer-four-core','reproducibility/producer-four-core/check_four_core_obstruction.py','four_core_obstruction_receipt.json'),
 ('independent-four-core','reproducibility/independent-four-core/independent_check.py','independent_receipt.json'),
]

def canonical(value):
 if isinstance(value,dict):
  return{k:canonical(v)for k,v in value.items()if k not in {'elapsed_seconds','seconds'}}
 if isinstance(value,list):return[canonical(v)for v in value]
 return value

def main():
 start=time.monotonic();count=0
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,relative=line.split('  ',1);p=ROOT/relative
  assert p.is_file(),f'Missing file: {relative}'
  assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'Hash mismatch: {relative}'
  count+=1
 print(f'PASS: {count} release file hashes',flush=True)
 receipts={};results=[]
 with tempfile.TemporaryDirectory(prefix='three-core-rayleigh-replay-')as temporary:
  for name,relative,output in JOBS:
   script=ROOT/relative;directory=Path(temporary)/name;directory.mkdir()
   copied=directory/script.name;shutil.copyfile(script,copied)
   run=subprocess.run([sys.executable,str(copied)],cwd=directory,
       env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),text=True,capture_output=True)
   if run.returncode:
    print(run.stdout);print(run.stderr,file=sys.stderr)
    raise AssertionError(f'Checker failed: {name}')
   actual=json.loads((directory/output).read_text())
   expected=json.loads(script.with_name(output).read_text())
   assert canonical(actual)==canonical(expected),f'Receipt mismatch: {name}'
   receipts[name]=actual;results.append({'checker':name,'verdict':'PASS'})
   print(f'PASS: {name}; all deterministic receipt fields match',flush=True)
 def histograms(receipt):
  return{(tuple(c['core']),tuple(c['exterior_types'])):
    (c['potential_arcs'],c['graphs'],c['coefficient_histogram'])for c in receipt['cases']}
 assert histograms(receipts['producer-boundary'])==histograms(receipts['independent-boundary'])
 print('PASS: all 48 producer and independent coefficient histograms agree',flush=True)
 print(json.dumps({'verdict':'PASS','manifest_files':count,'checks':results,
  'coefficient_histograms_agree':True,'elapsed_seconds':round(time.monotonic()-start,3)},indent=2))

if __name__=='__main__':main()

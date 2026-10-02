#!/usr/bin/env python3
"""Run the separate independent checkers under the complete input manifest."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import replay
if not __debug__:raise SystemExit('Run without -O')
OUT=ROOT/'output'/'verification';OUT.mkdir(parents=True,exist_ok=True)
def compare(a,b,path=''):
 if isinstance(a,dict):
  assert isinstance(b,dict) and a.keys()==b.keys(),path
  for key in a:compare(a[key],b[key],path+'/'+key)
 elif isinstance(a,list):
  assert isinstance(b,list) and len(a)==len(b),path
  for i,(x,y) in enumerate(zip(a,b)):compare(x,y,path+'/'+str(i))
 elif isinstance(a,float):assert math.isclose(a,b,rel_tol=1e-7,abs_tol=1e-9),(path,a,b)
 else:assert a==b,(path,a,b)
record={'status':'running','tests':[],'manifest':replay.verify_manifest(ROOT/'SHA256SUMS')}
for name in ['check_formal_independent','check_frozen_and_spectrum']:
 replay.verify_manifest(ROOT/'SHA256SUMS')
 with (OUT/(name+'.stdout.log')).open('w') as log:
  subprocess.run([sys.executable,str(ROOT/'verification'/(name+'.py'))],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
 actual=OUT/(name+'.json'); expected=ROOT/'verification'/'expected'/(name+'.json')
 compare(json.loads(expected.read_text()),json.loads(actual.read_text()))
 record['tests'].append({'name':name,'reference_comparison':'passed','result_sha256':hashlib.sha256(actual.read_bytes()).hexdigest()})
record['final_manifest']=replay.verify_manifest(ROOT/'SHA256SUMS');record['status']='passed'
(OUT/'verification-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))

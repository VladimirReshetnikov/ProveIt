#!/usr/bin/env python3
"""Compare retained selected-header records, not producer-time ancestry."""
from pathlib import Path
from hashlib import sha256
import json

H=Path(__file__).resolve().parent
D=H.parents[1]
inputs={
 'fixed':(H/'observations/attempt01/result.json','beca7bfd182f49fb0640ed2b49bff33aa2aa8e1ec09bb1fa1d632b2f06ab9883'),
 'forward':(D/'research/direct-bfs-80-model-halt-serialized-audit/observations/attempt01/result.json','9591ab25369f57a711315fbee02bd19a360ec4aba15535dc44e85cc983a84003'),
 'rebuilt80':(D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json','75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276'),
}
def sha(p):return sha256(p.read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
for n,(p,h) in inputs.items():need(sha(p)==h,n+' input changed')
a=json.loads(inputs['fixed'][0].read_text());f=json.loads(inputs['forward'][0].read_text());b=json.loads(inputs['rebuilt80'][0].read_text())
need(a['status']=='PASS_CAPTURE' and f['status']=='PASS_CAPTURE' and b['status']=='PASS','input status')
A=a['closure']['project'];F=f['closure']['project'];B=b['selected_project']
def digest(x):return None if x is None else x['sha256']
def compare(ref,old_shape):
 same=[];different={};absent=[]
 for name,row in sorted(A.items()):
  if name not in ref:absent.append(name);continue
  x=row['companions'];y=ref[name]['companions'] if old_shape else ref[name]
  keys=sorted(set(x)|set(y));changes={k:{'fixed':digest(x.get(k)),'reference':digest(y.get(k))} for k in keys if digest(x.get(k))!=digest(y.get(k))}
  if changes:different[name]=changes
  else:same.append(name)
 return {'same':same,'different':different,'absent':absent,'report':{'same':len(same),'different':len(different),'absent':len(absent)}}
forward=compare(F,True);rebuilt=compare(B,False)
# Reverse direction matters too: a missing original forward ancestor is not hidden.
forward_missing=sorted(set(F)-set(A))
result={'scope':'hash/companion comparison of captured selected project objects; not a replay or producer-time source ancestry proof',
 'inputs':{n:{'path':str(p),'sha256':h} for n,(p,h) in inputs.items()},'fixed_project_count':len(A),'forward_project_count':len(F),'rebuilt80_project_count':len(B),
 'against_forward':forward,'forward_names_missing_from_fixed':forward_missing,'against_rebuilt80':rebuilt}
out=H/'observations/reconcile01.json';need(not out.exists(),'output exists')
for n,(p,h) in inputs.items():need(sha(p)==h,n+' input changed during comparison')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'forward':forward['report'],'forward_names_missing_from_fixed':len(forward_missing),'rebuilt80':rebuilt['report'],'rebuilt_differences':rebuilt['different']},indent=2))

#!/usr/bin/env python3
"""Two exact literal1M forks from the actual second R252 blank root."""
import argparse,hashlib,json,sys
from pathlib import Path
P=argparse.ArgumentParser(description=__doc__);P.add_argument('--repo',type=Path,required=True);P.add_argument('--output',type=Path,required=True);a=P.parse_args()
assert __debug__
base=a.repo/'Computability/BusyBeaver/Research/ZFC';sys.path.insert(0,str(base))
import candidate252_independent_audit as A
raw=(base/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes();assert hashlib.sha256(raw).hexdigest()==A.EXPECTED_SHA
baseline=A.read_table(raw);mutant={k:v for k,v in baseline.items()if k[0]!=204};mutant[172,1]=(1,'R',252)
assert [(k,v)for k,v in baseline.items()if v[2]==204]==[((172,1),(1,'R',204))]
physical=[3,1,0,0,2,0,0,0,2];spares=[0]*9+[1]
q,h,ones=64,0,set()
for _ in range(15963):
 assert q!=254
 w,d,q=mutant[q,int(h in ones)]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=1 if d=='R'else-1
assert(q,h,ones)==(96,3,A.paint('',19,physical,spares,3))
f={'step':15963,'head':3,'header':22,'gap':19,'physical':physical,'logical':[physical[A.NEWPHYS[r]]for r in range(9)],'spares':spares,'whole_ones':sorted(ones),'whole_repaint_equal':True}
assert f['logical']==[0,0,3,2,0,0,2,0,1]
def root_frame(ones,h):
 if h-1 not in ones or min(ones)!=h-1:return None
 right=[p for p in ones if p>=h]
 if not right:return None
 header=min(right)
 if header-h<3:return None
 maximum=max(ones);cursor=header+1;values=[]
 while cursor<=maximum:
  if cursor in ones:return None
  cursor+=1;value=0
  while cursor in ones:value+=1;cursor+=1
  if not value:return None
  values.append(value-1)
 if len(values)<9:return None
 assert A.paint('',header-h,values[:9],values[9:],h)==ones
 return {'head':h,'header':header,'gap':header-h,'physical':values[:9],'spares':values[9:],'whole_repaint_equal':True}
def run(name,table,gap):
 q,h,ones=96,3,A.paint('',gap,physical,spares,3);initial=sorted(ones);fuel=1000000;tick=0;status='fuel_cutoff';visits=0;nextroot=None
 while tick<fuel:
  if q==254:status='halt';break
  bit=int(h in ones)
  if (q,bit)==(172,1):status='next_changed_row_before_execution';break
  if q==96 and tick:
   visits+=1;nextroot=root_frame(ones,h)
   if nextroot is not None:status='next_complete_root';break
  w,d,q=table[q,bit]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R'else-1;tick+=1
 return {'name':name,'initial_gap':gap,'initial_whole_ones':initial,'status':status,'moves':tick,'fuel':fuel,'state':q,'head':h,'one_count':len(ones),
 'whole_ones':sorted(ones),'whole_tape_ones_sha256':hashlib.sha256(json.dumps(sorted(ones),separators=(',',':')).encode()).hexdigest(),
 'subsequent_dispatch_visits':visits,'nextroot':nextroot,'stop_condition':'next completePC000 root, altered incomingrow before execution, halt, or1Mfuel'}
results=[run('baseline',baseline,19),run('R252',mutant,19),run('baseline_repaint_gap40',baseline,40)]
assert all(results[0][k]==results[1][k]for k in ('moves','state','head','whole_ones','subsequent_dispatch_visits'))
out={'scope':__doc__,'baseline_sha256':A.EXPECTED_SHA,'mutant_sha256':hashlib.sha256(A.encode(mutant)).hexdigest(),'seed_prefix_literal_moves':15963,
 'seed':f,'results':results,'finite_endpoints_identical':True,'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'nonclaims':'No unbounded binary simulation, futureavoidance ofmodifiedrow, sourcecoding atgap19, or nonhalting inferred.'}
a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:v for k,v in x.items()if k!='whole_ones'}for x in results],indent=2))

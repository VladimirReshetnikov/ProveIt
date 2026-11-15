#!/usr/bin/env python3
"""Independent literal verification of delivered GD selector/shortcut premises."""
from pathlib import Path
from itertools import product
import argparse,hashlib,json,subprocess,tempfile,sys
BASE=Path(__file__).resolve().parent
PKG=BASE.parent
if not __debug__: raise SystemExit('Verification requires assertions; run without -O.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path,default=BASE/'variant_review.json')
args=parser.parse_args()
START=74;HALT=254

def read(path):
 out={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,t=line.split();key=int(q),int(b)
  assert key not in out
  out[key]=int(w),(-1 if d=='L' else 1),int(t)
 return out

def pred(tm,q):return {(p,b,w,d) for (p,b),(w,d,t) in tm.items() if t==q}

def run(tm,q,h,tape,n):
 tape=dict(tape)
 trace=[]
 for _ in range(n):
  assert q!=HALT and h in tape
  w,d,t=tm[q,tape[h]];trace.append((q,h));tape[h]=w;h+=d;q=t
 return(q,h,tape),trace

result={}
for family in ('GD','GDH','GDHS'):
 p=PKG/'machines'/('PA194'+family+'_SF');old=read(PKG/'inputs'/(family+'.native.tm'));sel=read(p/'selector.native.tm');new=read(p/'machine.native.tm');receipt=json.loads((p/'certificate.json').read_text())
 assert len(old)==len(sel)==len(new)==388
 fmap=lambda q:127 if q==124 else q
 for (q,b),act in old.items():
  if (q,b) not in {(127,0),(124,0),(124,1)}:
   assert sel[q,b]==(act[0],act[1],fmap(act[2]))
 assert pred(old,127) and all((w,d)==(0,1) for q,b,w,d in pred(old,127))
 assert pred(old,124) and all((w,d)==(1,1) for q,b,w,d in pred(old,124))
 cases=0
 for q,hist in ((127,0),(124,1)):
  for bit in (0,1):
   tape={-1:hist,0:bit};a,_=run(old,q,0,tape,1);b,tr=run(sel,fmap(q),0,tape,1 if bit else 3)
   assert (fmap(a[0]),a[1],a[2])==b
   assert all(st!=HALT for st,h in tr);cases+=1
 fast={(26,1),(101,0)}
 assert {k for k in new if new[k]!=sel[k]}==fast
 assert pred(sel,101)=={(96,0,0,1)} and pred(new,101)==pred(sel,101)
 assert pred(sel,26)=={(11,0,0,-1),(101,0,0,-1)}
 assert pred(new,26)=={(11,0,0,-1)}
 assert pred(sel,11)==pred(new,11) and all(w==0 for q,b,w,d in pred(sel,11))
 for bits in product((0,1),repeat=5):
  tape=dict(zip(range(-2,3),bits))
  for q,ok in ((26,tape[0]==1 and tape[1]==0 and tape[2]==0),(101,tape[-1]==0 and tape[0]==0)):
   if not ok:continue
   a,tr=run(sel,q,0,tape,3);b,_=run(new,q,0,tape,1)
   assert a==b and all(st!=HALT for st,h in tr);cases+=1
 assert cases==16
 # Literal table-to-dense conjugacy, including both starts and halt.
 labels=json.loads((p/'labels.json').read_text());dense=read(p/'machine.tm')
 assert len(labels)==195 and labels[0]==74 and labels[-1]==254 and len(set(labels))==195
 for (q,b),(w,d,t) in dense.items():assert new[labels[q],b]==(w,d,labels[t])
 assert hashlib.sha256((p/'machine.tm').read_bytes()).hexdigest()==receipt['sha256']
 result[family]={'cases':cases,'selector_predicate':True,'child_predecessor_conditions':True,'complete_local_tape_equality':True,'intermediate_nonhalting':True,'dense_conjugacy':True,'printed_digest_matches':True}
with tempfile.TemporaryDirectory(prefix='pa194-review-') as td:
 cp=subprocess.run([sys.executable,'-B',str(PKG/'verify.py'),'--output',td],capture_output=True,text=True,check=True)
 for family in ('GD','GDH','GDHS'):
  n='PA194'+family+'_SF'
  for p in (Path(td)/n).iterdir():assert p.read_bytes()==(PKG/'machines'/n/p.name).read_bytes()
 result['fresh_rebuild']=cp.stdout.splitlines()
report={'status':'PASS','results':result,'claim':'Finite relative-simulation premises and package reproduction independently reviewed; absolute consistency calibration is inherited.'}
args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

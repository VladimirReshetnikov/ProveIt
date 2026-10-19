from pathlib import Path
import sys,json,time
from collections import Counter
ROOT=Path(__file__).resolve().parents[2]
ref=ROOT/'reference/baseline245'
sys.path.insert(0,str(ref/'code'))
import build_routing_machine as B
import parametric_prefix_affine as A
from review_affine_source import full_inc,full_strip
C=ROOT/'machine'
T,start=B.rebuild.read_table(ROOT/'reference/zfc_combined243_old.tm')
T[41,0]=(0,'L',84)
del T[58,0];del T[58,1]
assert all(q!=58 for w,d,q in T.values())
A.PADDING=64
TT={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in T.items()}
sites=json.loads((C/'sites_physical.json').read_text());count=0;failures=[];began=time.monotonic()
for i,(p,op,r) in enumerate(sites):
 for zero in ((True,False) if op=='CD' else (None,)):
  branch=(r,zero) if op=='CD'else None;extra=0;effect=None;over=False
  if op=='CI':succ,over=full_inc(p);effect=('inc',r)
  elif op=='CD'and not zero:succ,over=full_inc(p);effect=('dec',r);extra=1
  elif op=='CD':succ,over=full_inc(full_strip(p,'0',1))
  elif op=='CB':succ,over=full_inc(full_strip(p,'0',r))
  elif op=='CC':succ=full_strip(p,'1',r)
  else:succ=''
  right=[('b',int(b))for b in succ]+[('r',0,1,64+extra+int(over)-len(succ)),('b',1),('box',('plain',effect))]
  try:rc,literal=A.run(TT,p,branch,A.canon([('b',1)],right),halt=op=='CH',fuel=1000)
  except Exception as e:
   print('FAIL',i,p,op,r,zero,repr(e),flush=True);failures.append([i,p,op,r,zero,repr(e)]);break
  count+=1
 if failures:break
out=dict(candidate_states=len(T)//2,edit='41/0 -> 0 L 84; delete58',passed_cases=count,failures=failures,seconds=time.monotonic()-began)
Path(__file__).with_name('shorten_scanner_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

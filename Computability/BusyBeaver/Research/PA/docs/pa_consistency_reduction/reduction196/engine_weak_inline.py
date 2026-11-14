from pathlib import Path
import time,json
from engine_weak_folds import *
if __name__=='__main__':
 begin=time.time();m=S.load_machine();files=[[0]*10,[1]*10,list(range(10)),[2,0,1,0,3,0,1,2,0,1]]
 tests=[];bounds=[]
 for vs in files:
  for test in fixture_inputs([vs]):
   name,initial,end=test
   if name.startswith('mark'):continue
   r=int(name[-1]);vv=vs[:9];off=0
   if name.startswith('inc'):vv[r]+=1
   elif name.startswith('decp'):vv[r]-=1;off=1
   tests.append(test);bounds.append(off+len(filebits(vv)))
 out=[]
 for remove,entry in[({125},(62,0)),({62},(82,0)),({62,125},(82,0))]:
  for w in(0,1):
   for d in(-1,1):
    for z in range(196):
     if z in remove:continue
     n={k:v for k,v in m.items()if k[0]not in remove};n[entry]=(w,d,z)
     if any(v[2]in remove for v in n.values()):continue
     if all(check(n,t,b,limit=12000)for t,b in zip(tests,bounds)):
      print('PASS',remove,entry,(w,d,z),flush=True);out.append((sorted(remove),entry,(w,d,z)))
  print('DONE',remove,flush=True)
 print('CANDIDATES',out,'secs',time.time()-begin,flush=True)
 Path(__file__).with_name('engine_weak_inline_candidates.json').write_text(json.dumps(out))

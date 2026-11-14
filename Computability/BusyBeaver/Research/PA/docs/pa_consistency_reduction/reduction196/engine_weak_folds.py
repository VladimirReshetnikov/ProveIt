from pathlib import Path
import sys,time,json
from engine_detours import S,fixture_inputs,check as strongcheck
from engine_folds import filebits

def weakmatch(tape,expected,boundary):
 # Positions before boundary, including the entire logical 9-register prefix,
 # match exactly. The rest must be a nonempty well-formed spare register file.
 if {p for p in tape if p<boundary}!={p for p in expected if p<boundary}:return False
 if boundary in tape or boundary+1 not in tape:return False
 last=max(tape,default=-1);p=boundary
 while p<=last:
  if p in tape or p+1 not in tape:return False
  p+=2
  while p in tape:p+=1
 return True

def check(m,test,boundary,fold=None,limit=8000):
 name,(q,h,tape),(target,hh,end)=test;tape=tape.copy()
 if fold is not None:
  a,b=fold;q=b if q==a else q;target=b if target==a else target
 for t in range(limit):
  if q==target and h==hh and weakmatch(tape,end,boundary):return True
  v=int(h in tape)
  if(q,v)not in m:return False
  w,d,q=m[q,v]
  if w:tape.add(h)
  else:tape.discard(h)
  h+=d
 return False

if __name__=='__main__':
 begin=time.time();m=S.load_machine();files=[[0]*10,[1]*10,list(range(10)),[2,0,1,0,3,0,1,2,0,1]]
 tests=[];boundaries=[]
 for vs in files:
  ts=fixture_inputs([vs]);tests.extend(ts)
  for name,initial,end in ts:
   r=int(name[-1]);vv=vs[:9];offset=0
   if name.startswith('inc'):vv[r]+=1
   elif name.startswith('decp'):vv[r]-=1;offset=1
   boundary=offset+len(filebits(vv));boundaries.append(boundary)
 for t,b in zip(tests,boundaries):assert check(m,t,b),t[0]
 qs=sorted({q for q,b in S.ENGINE_ROWS});use={q:[]for q in qs}
 for i,t in enumerate(tests):
  used=strongcheck(m,t,limit=5000)
 # Every fixture checks globally; most folds reject in firstfewcases.
 candidates=[]
 for q in qs:
  for p in range(196):
   if p==q:continue
   n={(s,b):(w,d,p if z==q else z)for(s,b),(w,d,z)in m.items()if s!=q}
   if all(check(n,t,b,(q,p))for t,b in zip(tests,boundaries)):
    print('PASS',q,p,flush=True);candidates.append((q,p))
  print('DONE',q,flush=True)
 print('CANDIDATES',candidates,'seconds',time.time()-begin,flush=True)
 Path(__file__).with_name('engine_weak_fold_candidates.json').write_text(json.dumps(candidates))

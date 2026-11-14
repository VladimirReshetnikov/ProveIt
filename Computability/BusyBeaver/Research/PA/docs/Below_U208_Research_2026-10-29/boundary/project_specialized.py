from pathlib import Path
import sys,json,itertools,functools,time,hashlib
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'baseline'
sys.path.insert(0,str(BASE/'code'));sys.path.insert(0,str(BASE/'code/runtime'))
import native_symbolic as s
from build import read
R=3; ALL=set(range(1<<(2*R+1)))
t=read(BASE/'machine/u208.native.tm'); sites=json.loads((BASE/'machine/sites.json').read_text()); contexts={q:set() for q,b in t}; broad=set(); calls=0
from projection import prefix
def record(st):
 global calls
 calls+=1
 if st.q not in contexts or contexts[st.q]==ALL:return
 st.key()
 a=prefix(tuple(st.left),R+(st.direction==-1));b=prefix(tuple(st.right),R+(st.direction==1))
 for l in a:
  for r in b:
   word=l[::-1]+r; assert len(word)==2*R+1
   contexts[st.q].add(sum(v<<i for i,v in enumerate(word)))
original=s.State.step
def step(st,table,lemmas,clock,motion):
 record(st)
 answer=original(st,table,lemmas,clock,motion)
 event=answer[2]
 if event[0]=='unary':
  q=event[1][0];contexts[q]=ALL.copy();broad.add(q)
 elif event[0]=='list':
  q=event[1][0];contexts[q]=ALL.copy();broad.add(q)
 return answer
# Block lemmas proved without hook: intermediate literal rows conservatively broad.
lemmas,blocks=s.prove_blocks(t)
for block in blocks:
 for event in block['trace']:
  q=event[1][0];contexts[q]=ALL.copy();broad.add(q)
s.State.step=step
sys.path.insert(0,str(ROOT/'categories'))
from check import verify
CP=ROOT/'categories'
cert=json.loads((CP/'certificate.json').read_text())
verify((CP/'inputs/compatibility.sites.json').read_bytes(),cert,(BASE/'machine/sites.json').read_bytes())
original_var=s.var
start=time.time();cases=0
for i,site in enumerate(sites):
 masks=cert['states'][i]
 if masks is None:continue
 for positive in ([False,True] if site[1]=='CD' else [False]):
  if site[1]=='CD' and not(masks[site[2]] & (14 if positive else 1)):continue
  substitutions={}
  for r,m in enumerate(masks):
   vals=[k for k in range(4) if m>>k&1]; minimum=min(vals); exact=vals[0] if len(vals)==1 and vals[0]<3 else None
   if site[1]=='CD' and r==site[2]:
    if not positive:continue
    vals=[v for v in vals if v>0];minimum=min(vals)-1;exact=vals[0]-1 if len(vals)==1 and vals[0]<3 else None
   substitutions[2+r]=s.num(exact) if exact is not None else s.add(original_var(2+r),s.num(minimum))
  s.var=lambda n:substitutions.get(n,original_var(n))
  try:s.case(t,lemmas,site,positive);cases+=1
  finally:s.var=original_var
 if i%500==0:print(i,cases,time.time()-start,flush=True)
# Exact complete blank startup, including endpoint.
q=h=0;ones=set()
for tick in range(48141):
 contexts[q].add(sum(int(h+i in ones)<<(i+R) for i in range(-R,R+1)))
 if tick==48140:break
 w,d,z=t[q,int(h in ones)];ones.add(h) if w else ones.discard(h);q,h=z,h+d
assert(q,h)==(84,-2)
out={'table_sha256':hashlib.sha256((BASE/'machine/u208.native.tm').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((BASE/'machine/sites.json').read_bytes()).hexdigest(),'engine_sha256':hashlib.sha256((BASE/'code/runtime/native_symbolic.py').read_bytes()).hexdigest(),'radius':R,'cases':cases,'symbolic_calls':calls,'startup_steps':48140,'conservatively_broad_states':sorted(broad),'contexts':{q:sorted(v) for q,v in contexts.items()},'seconds':time.time()-start,'scope':'Source-category specialized overapproximate windows, inherited source entry and verified category invariant; unary/list interiors conservatively broad.'}
(ROOT/'specialized_windows.json').write_text(json.dumps(out,indent=2)+'\n');print('DONE',time.time()-start, sorted((len(v),q) for q,v in contexts.items())[:30])

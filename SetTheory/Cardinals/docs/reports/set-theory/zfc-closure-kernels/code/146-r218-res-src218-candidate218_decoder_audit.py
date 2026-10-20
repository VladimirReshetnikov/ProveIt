#!/usr/bin/env python3
"""Independent literal decoder audit of the provisional88/301/51 reduction.

The source-prefix and local lemmas below are exact. They do not claim blank
startup: the first candidate fails there, and that failure is also reproduced.
"""
from pathlib import Path
from collections import defaultdict,Counter
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'baseline219/K219_Construction_2026-10-20/machine'
NEW=ROOT/'root218/candidate218'
OUT=ROOT/'source218/candidate218_audit';OUT.mkdir(exist_ok=True)
def parse(path):
 T={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,bit,w,d,z=line.split();key=int(q),int(bit)
  assert key not in T;T[key]=(int(w),1 if d=='R'else-1,int(z))
 return T
old=parse(BASE/'k219.native.tm');new=parse(NEW/'candidate.tm')
assert hashlib.sha256((NEW/'candidate.tm').read_bytes()).hexdigest()=='cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f'
expected={key:(w,d,88 if z==301 else z)for key,(w,d,z)in old.items()if key[0]!=301}
expected[88,0]=(0,-1,51);expected[51,0]=(0,1,122)
assert new==expected and len(new)==436
rows=json.loads((BASE/'sites219.json').read_text())
assert (BASE/'sites219.json').read_bytes()==(NEW/'sites.json').read_bytes()
prefixes={p[:i]for p,op,arg in rows for i in range(len(p))}
def decode(T,p):
 cells={-1:1,**{i:int(b)for i,b in enumerate(p)}};before=dict(cells);q=84;h=0
 for tick in range(10000):
  if h==len(p):assert cells==before;return q,tick
  assert h in cells and(q,cells[h])in T
  w,d,q=T[q,cells[h]];cells[h]=w;h+=d
 raise AssertionError('Prefix did not close')
paths=defaultdict(list);timing=Counter();old_states=set();new_states=set()
for p in sorted(prefixes,key=lambda p:(len(p),p)):
 a,sa=decode(old,p);b,sb=decode(new,p)
 assert b==(88 if a==301 else a)
 paths[a].append(p);timing[sb-sa]+=1;old_states.add(a);new_states.add(b)
assert len(prefixes)==4743 and len(old_states)==169 and len(new_states)==168
assert len(paths[301])==len(paths[88])==4
assert all(p.endswith('0')for p in paths[301])and all(p.endswith('1')for p in paths[88])
def trace(T,q,h,cells,count):
 cells=dict(cells);ans=[]
 for _ in range(count):
  assert h in cells
  key=q,cells[h];act=T[key];ans.append(dict(state=q,head=h,read=cells[h],action=act))
  w,d,q=act;cells[h]=w;h+=d
 return q,h,cells,ans
lemmas=[]
for pred,source_state,steps,target in [(0,301,5,45),(1,88,3,122)]:
 cells={-1:pred,0:0};q,h,after,steps_trace=trace(new,88,0,cells,steps)
 assert(q,h,after)==(target,1,cells)
 oq,oh,oa,_=trace(old,source_state,0,cells,1);assert(oq,oh,oa)==(q,h,after)
 lemmas.append(dict(name='A_branch'if pred==0 else'R_branch',predecessor=pred,read=0,old_steps=1,new_steps=steps,
                    target=target,head_displacement=1,tape_preserved=True,trace=steps_trace))
for bit in(0,1):assert new[51,1]==old[51,1]and new[88,1]==old[88,1]==old[301,1]
cells={0:0,1:1};oq,oh,oc,ot=trace(old,51,0,cells,2);nq,nh,nc,nt=trace(new,51,0,cells,2)
assert(oq,oh,oc)==(nq,nh,nc)==(1,0,{0:0,1:0})
lemmas.append(dict(name='Old51_zero_with_next1',old_steps=2,new_steps=2,old_trace=ot,new_trace=nt,endpoint=[1,0],written_cells=nc))
contexts={}
for suffix in('windows_r7.txt','windows_postinit_r7.txt'):
 checks=defaultdict(Counter)
 for line in(ROOT/'machine218/windows219'/suffix).read_text().splitlines():
  q,w=map(int,line.split())
  if q in(88,301):checks[q][((w>>6)&1,(w>>7)&1)]+=1
  if q==51 and not(w>>7)&1:checks[q][(w>>8)&1]+=1
 contexts[suffix]={q:{str(k):v for k,v in count.items()}for q,count in checks.items()}
 assert all(pred==(0 if q==301 else 1)for q in(88,301)for pred,read in checks[q])
 if 'postinit'in suffix:assert dict(checks[51])=={1:441}
# Check the first failed blank-start use independently on both literal tables.
def blank_prefix(T,count):
 q=0;h=0;ones=set()
 for _ in range(count):
  bit=int(h in ones);w,d,q=T[q,bit]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 return q,h,ones
assert blank_prefix(old,79)==blank_prefix(new,79)==(51,5,{-3,-2})
assert 6 not in blank_prefix(new,79)[2]
old81=blank_prefix(old,81);new81=blank_prefix(new,81)
assert old81==(1,5,{-3,-2,6})and new81==(137,5,{-3,-2})
report=dict(status='EXACT_SOURCE_DECODER_LEMMAS_PASS_BLANK_START_COUNTEREXAMPLE_CONFIRMED',
            working_states=218,transition_rows=436,source_prefixes=4743,old_decoder_states=169,new_decoder_states=168,
            table_sha256=hashlib.sha256((NEW/'candidate.tm').read_bytes()).hexdigest(),
            source_sha256=hashlib.sha256((NEW/'sites.json').read_bytes()).hexdigest(),
            original_301_paths=paths[301],original_88_paths=paths[88],prefix_step_increases=dict(timing),
            local_lemmas=lemmas,projected_context_counts=contexts,
            first_bad_bootstrap=dict(step=79,state=51,head=5,read=0,next=0,one_cells=[-3,-2]),
            old_after81=[old81[0],old81[1],sorted(old81[2])],new_after81=[new81[0],new81[1],sorted(new81[2])],
            scope='Literal unchanged-source decoder proof and context-dependent local simulations. Projected contexts are supplementary evidence. This provisional table is not accepted from blank start; it needs a separate initializer repair.')
(OUT/'decoder_audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in('local_lemmas','projected_context_counts')},indent=2))

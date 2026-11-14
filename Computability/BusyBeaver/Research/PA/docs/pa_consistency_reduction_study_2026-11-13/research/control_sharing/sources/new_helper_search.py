#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
import sys,json,itertools,time
from pathlib import Path
from collections import defaultdict
sys.path.insert(0,str(Path(__file__).parent/'base'))
import compiler as c,symbolic_runtime as s
PACKAGE=Path(__file__).resolve().parent.parent
OUTPUT_DIR=PACKAGE/'rerun_outputs'
OUTPUT_DIR.mkdir(parents=True,exist_ok=True)
c.ROOT=s.ROOT=PACKAGE/'inputs/pa196'
inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
base=PACKAGE/'inputs/primary'
g=c.read_grammar(base/'source/pa194.grammar.json');rows,ix,shape=c.build(g)
# Force native tuples to bool direction for hashing consistency.
qs=sorted({q for q,b in rows})
incoming=defaultdict(set)
for (q,b),(w,d,n) in rows.items():
 if d and w==b:incoming[n].add(b)
L=[q for q in shape if incoming[q]=={0}];R=[q for q in shape if incoming[q]=={1}]
providers=[defaultdict(list),defaultdict(list)]
rev=[defaultdict(set),defaultdict(set)]
for q in qs:
 for b in (0,1):rev[b][rows[q,b]].add(q)
 z,o=rows[q,0],rows[q,1]
 if z[:2]==(0,True) and o[:2]==(1,True) and z[2] in qs and o[2] in qs:
  for b in (0,1):providers[b][rows[z[2],b],rows[o[2],b]].append((q,z[2],o[2]))
baseops=c.opportunities_fast(rows,shape)
print('BASE',len(qs),len(shape),len(baseops),len(c.max_matching(baseops)),flush=True)
possible_helpers=set()
for a,b in itertools.product(L,R):
 missing=[]
 for x in (0,1):
  if rows[a,x]==rows[b,x]:continue
  pp=[v for v in providers[x].get((rows[a,x],rows[b,x]),[]) if not {a,b}&set(v)]
  if not pp:
   missing.append({(u,v) for u in rev[x][rows[a,x]] for v in rev[x][rows[b,x]] if not {a,b}&{u,v}})
 if missing:
  possible_helpers|=set.intersection(*missing)
print('HELPERS',len(possible_helpers),flush=True)
H=2400
def valid(chosen,table):
 aliases={a:b for a,b,acts in chosen};patched={b:acts for a,b,acts in chosen}
 for a,b,ac in chosen:
  for ctx,old in ((0,a),(1,b)):
   for bit in (0,1):
    w,d,t=table[old,bit];target=(aliases.get(t,t),1 if d else -1,(ctx,w))
    q,h,tape=b,0,[ctx,bit]
    for step in range(21):
     if step and (q,h,tuple(tape))==target:break
     if h not in(-1,0) or(q,tape[h+1])not in table or q in aliases:return False
     w,d,t=(patched[q][tape[h+1]] if q in patched else table[q,tape[h+1]])
     tape[h+1]=w;h+=1 if d else -1;q=aliases.get(t,t)
    else:return False
 return True

def solve(ops,table,goal):
 # Narrower early compatibility checks are unsound for not-yet-applied aliases,
 # so check only the final simultaneous table.
 chosen=[];used=set();counter=0
 def dfs(i):
  nonlocal counter
  if len(chosen)==goal:
   counter+=1
   if valid(chosen,table):return list(chosen)
   return
  if len(chosen)+len(ops)-i<goal:return
  if i==len(ops):return
  a,b,acts=ops[i]
  if not {a,b}&used:
   used.update((a,b))
   for ac in itertools.product(*acts):
    chosen.append((a,b,ac));out=dfs(i+1)
    if out:return out
    chosen.pop()
   used.remove(a);used.remove(b)
  return dfs(i+1)
 out=dfs(0);return out,counter
count=0;t0=time.time();best=7
for u,v in sorted(possible_helpers):
 table=dict(rows);table[H,0]=(0,True,u);table[H,1]=(1,True,v)
 ops=c.opportunities_fast(table,shape);bound=len(c.max_matching(ops))
 if bound<9:continue
 count+=1
 print('BOUND',u,v,bound,'ops',len(ops),flush=True)
 sol,n=solve(ops,table,9)
 if sol:
  rec={'helper':H,'actions':[[0,True,u],[1,True,v]],'folds':sol,'raw_controls':len(qs),'final_controls':len(qs)+1-len(sol)}
  (OUTPUT_DIR/f'newhelper_{u}_{v}.json').write_text(json.dumps(rec,indent=2))
  print('HIT',json.dumps(rec),flush=True);break
print('DONE screened',len(possible_helpers),'bound_passes',count,'elapsed',time.time()-t0,flush=True)

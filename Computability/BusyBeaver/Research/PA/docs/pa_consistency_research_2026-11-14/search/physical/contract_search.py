#!/usr/bin/env python3
"""Discover multi-step contractions certified on a blank-start window closure."""
from pathlib import Path
from collections import deque,defaultdict
import json,sys,time,hashlib,argparse
import z3
ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('out',type=Path);ap.add_argument('--radius',type=int,default=6);ap.add_argument('--steps',type=int,default=31);args=ap.parse_args();args.out.mkdir(exist_ok=True)
raw=args.table.read_bytes();table={}
for line in raw.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,n=line.split();table[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
N=len(table)//2;assert set(table)=={(q,b)for q in range(N)for b in(0,1)};assert {t for w,d,t in table.values()}-set(range(N))=={N}
R=args.radius;W=2*R+1;MASK=(1<<W)-1;MID=1<<R
seen={(0,0)};todo=deque(seen);contexts=defaultdict(list)
while todo:
 q,bits=todo.popleft();bit=(bits>>R)&1;contexts[q,bit].append(bits);w,d,t=table[q,bit];written=(bits|MID)if w else bits&~MID
 if t==N:continue
 for fresh in(0,1):
  shifted=(written>>1)|(fresh<<(W-1))if d==1 else((written<<1)&MASK)|fresh
  k=(t,shifted)
  if k not in seen:seen.add(k);todo.append(k)
print('CLOSURE',N,len(seen),flush=True)

def options(q,b,bits):
 tape=bits;head=0;state=q;ans={};visited=set()
 for tick in range(1,args.steps+1):
  if state==N or abs(head)>R:break
  key=(state,head,tape)
  if key in visited:break
  visited.add(key)
  read=(tape>>(head+R))&1;w,d,state=table[state,read]
  tape=(tape|1<<(head+R))if w else tape&~(1<<(head+R));head+=d
  if abs(head)==1 and(tape&~MID)==(bits&~MID):ans.setdefault(((tape>>R)&1,head,state),tick)
 return ans
allopts={};certs={};total=0;new=0
for q in range(N):
 for b in(0,1):
  cases=contexts[q,b]
  if not cases:
   opts={(0,1,0):0,(1,1,N):0};durs={a:[0,0]for a in opts}
  else:
   opts=options(q,b,cases[0]);durs={a:[t,t]for a,t in opts.items()}
   for bits in cases[1:]:
    these=options(q,b,bits)
    opts={a:t for a,t in opts.items()if a in these}
    for a in opts:durs[a]=[min(durs[a][0],these[a]),max(durs[a][1],these[a])]
    if len(opts)==1:break
   assert table[q,b]in opts
  allopts[q,b]=list(sorted(opts));certs[q,b]=durs
  total+=len(opts);new+=len(opts)-1
print('OPTIONS',total,'additional',new,flush=True)
info={'table_sha256':hashlib.sha256(raw).hexdigest(),'radius':R,'max_steps':args.steps,'states':N,'closure':len(seen),'options':[{"q":q,"b":b,"rows":[[*a,*certs[q,b][a]]for a in allopts[q,b]]}for q in range(N)for b in(0,1)]}
(args.out/'options.json').write_text(json.dumps(info,indent=2)+'\n')
solver=z3.Optimize();solver.set(timeout=60000)
active=[z3.Bool(f'a{q}')for q in range(N)];solver.add(active[0]);sel={}
for q in range(N):
 for b in(0,1):
  opts=allopts[q,b];vs=[z3.Bool(f'o{q}_{b}_{i}')for i in range(len(opts))];sel[q,b]=vs
  solver.add(z3.Implies(active[q],z3.PbEq([(x,1)for x in vs],1)))
  for x,(w,d,n)in zip(vs,opts):
   if n<N:solver.add(z3.Implies(z3.And(active[q],x),active[n]))
solver.minimize(z3.Sum([z3.If(a,1,0)for a in active]));res=solver.check();info['solver']=str(res)
if res==z3.sat:
 model=solver.model();keep={q for q in range(N)if z3.is_true(model[active[q]])};chosen={}
 for q in keep:
  for b in(0,1):chosen[q,b]=next(a for v,a in zip(sel[q,b],allopts[q,b])if z3.is_true(model[v]))
 reach={0};todo=[0]
 for q in todo:
  for b in(0,1):
   n=chosen[q,b][2]
   if n<N and n not in reach:reach.add(n);todo.append(n)
 assert reach<=keep
 chosen={k:a for k,a in chosen.items()if k[0]in reach}
 info.update(working_states=len(reach),removed=sorted(set(range(N))-reach),changed_rows=[[*k,*a]for k,a in chosen.items()if table[k]!=a])
 labels=[0]+sorted(reach-{0})+[N];ren={x:i for i,x in enumerate(labels)}
 (args.out/'candidate.tm').write_text(''.join(f'{ren[q]} {b} {w} {"R"if d==1 else"L"} {ren[n]}\n'for(q,b),(w,d,n)in sorted(chosen.items())))
 (args.out/'labels.json').write_text(json.dumps(labels)+'\n')
 print('RESULT',len(reach),'removed',info['removed'],'changed',len(info['changed_rows']),flush=True)
(args.out/'receipt.json').write_text(json.dumps(info,indent=2)+'\n')

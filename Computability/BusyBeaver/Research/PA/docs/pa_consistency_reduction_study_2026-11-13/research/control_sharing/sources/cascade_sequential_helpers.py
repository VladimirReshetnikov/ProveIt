#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
exec(Path(__file__).with_name('new_helper_search.py').read_text().split('count=0;t0=time.time()')[0])

def apply(table,folds):
 aliases={a:b for a,b,ac in folds};patch={b:ac for a,b,ac in folds}
 return {(q,x):(w,bool(d),aliases.get(t,t)) for(q,x),act in table.items() if q not in aliases for w,d,t in [patch[q][x] if q in patch else act]}

def prune(table):
 reached={74};todo=[74]
 for q in todo:
  for b in(0,1):
   n=table[q,b][2]
   if(n,0)in table and n not in reached:reached.add(n);todo.append(n)
 return{key:act for key,act in table.items() if key[0]in reached}

def minimize(table):
 table=prune(table);qs2=sorted({q for q,b in table});groups={q:0 for q in qs2};groups[254]=-1
 while True:
  idx={};new={254:-1}
  for q in qs2:
   sig=tuple((w,d,groups[t])for w,d,t in [table[q,b] for b in(0,1)])
   new[q]=idx.setdefault(sig,len(idx))
  if all(new[q]==groups[q]for q in qs2):break
  groups=new
 rep={}
 for q in qs2:rep.setdefault(groups[q],q)
 # Keep start name74 unchanged for subsequent traversal.
 rep[groups[74]]=74;rep[-1]=254
 ren={q:rep[g]for q,g in groups.items()}
 out={(ren[q],b):(w,d,ren[t])for(q,b),(w,d,t)in table.items()}
 return out,ren

def eligible(table):
 incoming=defaultdict(list)
 for(q,b),(w,d,n)in table.items():incoming[n].append((w,d))
 return {q:None for q in shape if(q,0)in table and q!=74 and incoming[q] and all(d for w,d in incoming[q])}

def localvalid(old,new,a,b):
 for ctx,q in((0,a),(1,b)):
  for bit in(0,1):
   w,d,n=old[q,bit];target=(b if n==a else n,1 if d else-1,(ctx,w))
   state,pos,tape=b,0,[ctx,bit]
   for j in range(41):
    if j and(state,pos,tuple(tape))==target:break
    if pos not in(-1,0)or(state,tape[pos+1])not in new:return False
    w,d,state=new[state,tape[pos+1]];tape[pos+1]=w;pos+=1 if d else-1
   else:return False
 return True

def signature(table):return tuple(sorted(table.items()))

def searchtable(table,history,limit=20000):
 todo=[(table,history)];seen={signature(table)};best=len(table)//2;visited=0
 while todo and visited<limit:
  table,hist=todo.pop();visited+=1
  minimized,ren=minimize(table)
  if len(minimized)<len(table):hist=hist+[{'kind':'bisimulation','rename':ren}];table=minimized
  size=len(table)//2
  if size<best:best=size;print('CASCADE_BEST',best,'visited',visited,flush=True)
  if size<=193:return table,hist,visited
  for a,b,choices in c.opportunities_fast(table,eligible(table)):
   for ac in itertools.product(*choices):
    new=c.fold(table,a,b,ac)
    if not localvalid(table,new,a,b):continue
    sig=signature(new)
    if sig in seen:continue
    seen.add(sig);todo.append((new,hist+[{'kind':'context_fold','remove':a,'keep':b,'actions':ac}]))
 return None,None,visited

count=0;visited=0;hit=False
for u,v in sorted(possible_helpers):
 table=dict(rows);table[2400,0]=(0,True,u);table[2400,1]=(1,True,v)
 ops=c.opportunities_fast(table,shape)
 for a,b,choices in ops:
  for ac in itertools.product(*choices):
   if not any(act[2]==2400 for act in ac):continue
   quotient=c.fold(table,a,b,ac)
   if not localvalid(table,quotient,a,b):continue
   count+=1
   new,hist,n=searchtable(quotient,[{'kind':'helper','name':2400,'u':u,'v':v},{'kind':'context_fold','remove':a,'keep':b,'actions':ac}],limit=20000);visited+=n
   print('TRIED',u,v,'fold',a,b,'states',len(quotient)//2,'visited',n,flush=True)
   if new:
    print('HIT',u,v,len(new)//2,flush=True)
    (OUTPUT_DIR/'cascade_hit.native.tm').write_text(''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(new.items())))
    (OUTPUT_DIR/'cascade_history.json').write_text(json.dumps(hist,indent=2));hit=True;break
  if hit:break
 if hit:break
print('DONE',count,'helper quotients, visited',visited,flush=True)

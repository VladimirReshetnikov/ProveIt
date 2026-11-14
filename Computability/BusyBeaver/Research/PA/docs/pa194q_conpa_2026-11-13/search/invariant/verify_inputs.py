#!/usr/bin/env python3
"""Check the source/path binding, invariant, table identity, and literal startup."""
from pathlib import Path
import hashlib,json,subprocess,sys
if not __debug__:raise RuntimeError('Assertions required')
ROOT=Path(__file__).resolve().parent
sites=json.loads((ROOT/'sites.json').read_text());program=json.loads((ROOT/'instructions.json').read_text())
paths=[tuple(map(int,s[0]))for s in sites]
assert len(set(paths))==len(paths)==len(program)==3649
by_path={p:i for i,p in enumerate(paths)}
def locate(p):
 if p in by_path:return by_path[p]
 for i,q in enumerate(paths):
  if q[:len(p)]==p or(p[:len(q)]==q and not any(p[len(q):])):return i
 raise ValueError(p)
def after(p):
 p=list(p)
 for i in range(len(p)-1,-1,-1):
  if p[i]==0:p[i]=1;return locate(tuple(p[:i+1]))
 raise ValueError(p)
def cut(p,b,k):
 for i in range(len(p)-1,-1,-1):
  if p[i]==b:
   k-=1
   if not k:return p[:i]
 raise ValueError((p,b,k))
resolved=[]
for p,(_,op,arg)in zip(paths,sites):
 if op=='inc':ins=['inc',arg,after(p)]
 elif op=='dec':ins=['dec',arg,after(cut(p,0,1)),after(p)]
 elif op=='breakTo':ins=['jump',after(cut(p,0,arg))]
 elif op=='continueTo':ins=['jump',locate(cut(p,1,arg))]
 elif op=='halt':ins=['halt']
 else:raise ValueError(op)
 resolved.append(ins)
assert resolved==program
out=ROOT/'input_check';out.mkdir(exist_ok=True)
subprocess.run([sys.executable,str(ROOT/'abstract_source.py'),str(ROOT/'instructions.json'),str(out/'invariant.json')],check=True,stdout=subprocess.DEVNULL)
assert json.loads((out/'invariant.json').read_text())==json.loads((ROOT/'invariant.json').read_text())
rows={}
for ln in(ROOT/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=ln.split();rows[int(q),int(b)]=int(w),1 if d=='R'else-1,int(n)
assert len(rows)==388
order=[74];index={74:0}
for q in order:
 for b in(0,1):
  n=rows[q,b][2]
  if n!=254 and n not in index:index[n]=len(order);order.append(n)
assert len(order)==194
text=''.join(f'{index[q]} {b} {rows[q,b][0]} {"R"if rows[q,b][1]==1 else"L"} {194 if rows[q,b][2]==254 else index[rows[q,b][2]]}\n'for q in order for b in(0,1))
sha=hashlib.sha256(text.encode()).hexdigest()
assert sha=='48e98b5504dc5b3f20a2d040cb54ed1c96bee4c5e32ea27ae98ffada4dce7ea1'
head=-2;physical=[0,0,0,0,0,0,2,0,0]+[1]*26
want={head-1,head+48};want.update(head+i for i,b in enumerate(paths[25])if b)
pos=head+49
for v in physical:
 pos+=1;want.update(range(pos,pos+v+1));pos+=v+1
q,h,ones=74,0,set()
for _ in range(57922):
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
assert(q,h,ones)==(84,head,want)
receipt={'source_path_binding':True,'inductive_invariant_recomputed':True,'dense_sha256':sha,'source_entry_site':25,'startup_steps':57922,'complete_tape_equality':True,'initial_logical_values':[2]+[0]*8,'physical_spares':26}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

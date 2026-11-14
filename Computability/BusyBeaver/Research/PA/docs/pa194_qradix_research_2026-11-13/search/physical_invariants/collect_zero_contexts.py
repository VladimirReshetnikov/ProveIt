"""Collect conservative windows after a sound must-zero source analysis.

The reduction screen is only discovery. Any candidate requires full contracts
with these proved invariants and an exact blank seed.
"""
from pathlib import Path
from collections import defaultdict,deque
from functools import lru_cache
import sys,json,itertools,time

ROOT=Path(__file__).resolve().parent
REF=ROOT/'reference'
BASE=ROOT/'inputs'
sys.path.insert(0,str(REF))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48
r.PHY=(6,2,0,4,3,7,8,5,1)
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'zero_contexts'
OUT.mkdir(parents=True,exist_ok=True)

ins=json.loads((BASE/'instructions.json').read_text());sites=json.loads((BASE/'sites.json').read_text())
status=[None]*len(ins);status[25]=tuple(2 if i==0 else 1 for i in range(9));queue=deque([25])
while queue:
 pc=queue.popleft(); v=list(status[pc]);a=ins[pc];op=a[0]
 if op=='halt':out=[]
 elif op=='jump':out=[(a[1],v)]
 elif op=='inc':v[a[1]]=2;out=[(a[2],v)]
 elif op=='dec':
  reg,z,p=a[1:];out=[]
  if v[reg]&1:w=v.copy();w[reg]=1;out.append((z,w))
  if v[reg]&2:w=v.copy();w[reg]=3;out.append((p,w))
 for nxt,w in out:
  merged=tuple(w) if status[nxt] is None else tuple(x|y for x,y in zip(status[nxt],w))
  if merged!=status[nxt]:status[nxt]=merged;queue.append(nxt)

mp={int(k):v for k,v in json.loads((REF/'legacy_mapping.json').read_text()).items()}
rows=r.table(BASE/'machine.native.tm')
for q in {q for q,b in rows}|{254}:mp.setdefault(q,q+10000)
reverse={v:k for k,v in mp.items()}
table={(mp[q],b):(w,d,mp[t])for(q,b),(w,d,t)in rows.items()}
K=5;patterns=defaultdict(set);seen=set();current=None
@lru_cache(maxsize=200000)
def prefix(atoms,k):
 if k==0:return ((),)
 if not atoms:return ((0,)*k,)
 a,*tail=atoms;tail=tuple(tail)
 if a[0]=='blank':return ((0,)*k,)
 if a[0] in ('list','opaque'):return tuple(itertools.product((0,1),repeat=k))
 assert a[0]=='run';bit,n=a[1:];n0=n[0];assert n0>=0
 if not any(n[1:]):
  if n0>=k:return ((bit,)*k,)
  return tuple((bit,)*n0+p for p in prefix(tail,k-n0))
 out=set()
 for size in range(n0,k+1):
  if size>=k:out.add((bit,)*k);break
  for p in prefix(tail,k-size):out.add((bit,)*size+p)
 if n0>k:out.add((bit,)*k)
 return tuple(out)
def observe(q,dr,left,right):
 q=reverse[q]
 lp=prefix(tuple(left),K+1 if dr==-1 else K);rp=prefix(tuple(right),K if dr==-1 else K+1)
 key=q,dr,lp,rp
 if key in seen:return
 seen.add(key)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if dr==-1 else tuple(reversed(a))+b
  patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
old_step=s.State.step
def step(self,table,lemmas,clock,motion):
 self.key();observe(self.q,self.direction,self.left,self.right)
 src,dst=(self.right,self.left)if self.direction==1 else(self.left,self.right)
 if src and src[0][0]=='run':
  a=src[0];w,d,q=table[self.q,a[1]]
  if q==self.q and d==self.direction:
   length=a[2];count=K if any(length[1:])else min(K,max(0,length[0]-1))
   for j in range(1,count+1):
    rem=s.add(s.var(1),s.num(1))if any(length[1:])else s.num(length[0]-j)
    ss=[s.run(a[1],rem)]+src[1:];dd=[s.run(w,j)]+dst
    observe(self.q,self.direction,dd if self.direction==1 else ss,ss if self.direction==1 else dd)
 return old_step(self,table,lemmas,clock,motion)
s.State.step=step
t0=time.time();lemmas,blocks=s.prove_blocks(table)
original_var=s.var
def var(i):
 if current is not None and 2<=i<=10 and status[current][i-2]==1:return s.ZERO
 return original_var(i)
s.var=var
codes={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
total=0;skipped=0
for i,(path,op,arg) in enumerate(sites):
 current=i
 if status[i] is None:continue
 for positive in ([False,True] if op=='dec' else [False]):
  if op=='dec'and not(status[i][arg]&(2 if positive else 1)):
   skipped+=1;continue
  s.case(table,lemmas,[path,codes[op],arg],positive);total+=1
 if (i+1)%500==0:print(i+1,len(seen),total,time.time()-t0,flush=True)
current=None
q,h,ones=74,0,set()
for _ in range(58154):
 patterns[q].add(sum(int(h+j-K in ones)<<j for j in range(2*K+1)))
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
assert(q,h)==(84,-2)
(OUT/'patterns_k5.txt').write_text(''.join(f'{q} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
rec=dict(radius=K,source_outcomes=total,skipped_impossible_outcomes=skipped,states=len(patterns),patterns=sum(map(len,patterns.values())),views=len(seen),seconds=time.time()-t0)
(OUT/'zero_invariant.json').write_text(json.dumps(status))
(OUT/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec,flush=True)

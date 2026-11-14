"""Collect conservative windows after a sound must-zero source analysis.

The reduction screen is only discovery. Any candidate requires full contracts
with these proved invariants and an exact blank seed.
"""
from pathlib import Path
from collections import defaultdict,deque
from functools import lru_cache
import sys,json,itertools,time,math

ROOT=Path(__file__).resolve().parent
REF=ROOT/'reference'
BASE=ROOT/'inputs'
sys.path.insert(0,str(REF))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48
r.PHY=(6,2,0,4,3,7,8,5,1)
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'modular_contexts'
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

modular=json.loads((ROOT/'mod4_verified.json').read_text())
mp={int(k):v for k,v in json.loads((REF/'legacy_mapping.json').read_text()).items()}
rows=r.table(BASE/'machine.native.tm')
for q in {q for q,b in rows}|{254}:mp.setdefault(q,q+10000)
reverse={v:k for k,v in mp.items()}
table={(mp[q],b):(w,d,mp[t])for(q,b),(w,d,t)in rows.items()}
K=5;patterns=defaultdict(set);seen=set();list_seen=set();current=None;current_positive=False
@lru_cache(maxsize=200000)
def prefix(atoms,k):
 if k==0:return ((),)
 if not atoms:return ((0,)*k,)
 a,*tail=atoms;tail=tuple(tail)
 if a[0]=='blank':return ((0,)*k,)
 if a[0]=='opaque':return tuple(itertools.product((0,1),repeat=k))
 if a[0]=='list':
  assert a[2]=='spare_tail'
  word=(0,1,1) if a[1]=='B' else (1,0,1)
  if a[3]:word=tuple(reversed(word))
  return (tuple(word[i%3]for i in range(k)),)
 assert a[0]=='run';bit,n=a[1:];n0=n[0];assert n0>=0
 if not any(n[1:]):
  if n0>=k:return ((bit,)*k,)
  return tuple((bit,)*n0+p for p in prefix(tail,k-n0))
 out=set()
 stride=math.gcd(*n[1:])
 for size in range(n0,k+stride,stride):
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
def emit(self,table):
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
def step(self,table,lemmas,clock,motion):
 emit(self,table)
 src,dst=(self.right,self.left)if self.direction==1 else(self.left,self.right)
 if src and src[0][0]=='list':
  atom=src[0];_,before,tag,reversed_word=atom
  key=(self.q,self.direction,before,reversed_word)
  after=lemmas[key]
  local_key=(key,after,prefix(tuple(dst),K),prefix(tuple(src[1:]),K))
  if local_key in list_seen:return old_step(self,table,lemmas,clock,motion)
  list_seen.add(local_key)
  words=s.block(s.num(1),before)*3
  if reversed_word:words=s.rev(words)
  # First three and last three blocks cover both boundary zones and all
  # periodic interior phases of a list with at least 25 value-one blocks.
  for edge in ('first','last'):
   source=words+[atom]+src[1:] if edge=='first'else words+src[1:]
   dest=dst if edge=='first'else [('list',after,tag,not reversed_word)]+dst
   probe=s.State(self.q,dest,source,1)if self.direction==1 else s.State(self.q,source,dest,-1)
   pc,pm=s.ZERO,s.ZERO
   for _ in range(30):
    probe.key();active=probe.right if probe.direction==1 else probe.left
    if probe.q==self.q and probe.direction==self.direction and active==src[1:]:break
    if active and active[0][0]=='list':break
    emit(probe,table)
    pc,pm,event=old_step(probe,table,lemmas,pc,pm)
    if pc==s.num(9):break
   assert pc==s.num(9),('three periodic blocks',edge,self.q,pc)
 return old_step(self,table,lemmas,clock,motion)
t0=time.time();lemmas,blocks=s.prove_blocks(table)
s.State.step=step
original_var=s.var
def var(i):
 if i==11:return s.num(1)
 if current is not None and 2<=i<=10:
  mask=modular[current][i-2]
  shifted=current_positive and ins[current][0]=='dec' and ins[current][1]==i-2
  if mask==1:return s.ZERO
  if mask in(2,3,4,8,16):
   base={2:4,3:0,4:1,8:2,16:3}[mask]
   if shifted:base=3 if mask in(2,3)else base-1
   return s.add(tuple(4*x for x in original_var(i)),s.num(base))
  if mask==30 and not shifted:return s.add(original_var(i),s.num(1))
 return original_var(i)
s.var=var
codes={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
total=0;skipped=0
for i,(path,op,arg) in enumerate(sites):
 current=i
 if status[i] is None:continue
 for positive in ([False,True] if op=='dec' else [False]):
  current_positive=positive
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

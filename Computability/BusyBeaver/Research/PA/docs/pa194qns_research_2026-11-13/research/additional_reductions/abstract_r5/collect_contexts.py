from pathlib import Path
import sys,itertools,json,time
from collections import defaultdict
from functools import lru_cache
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('table',type=Path);parser.add_argument('sites',type=Path);parser.add_argument('startup_steps',type=int);parser.add_argument('output',type=Path)
args=parser.parse_args()
REF=Path(__file__).resolve().parent/'reference'
sys.path.insert(0,str(REF))
import symbolic_runtime as s
import independent_runtime as r
s.HEADER_BASE=48
r.PHY=(6,2,0,4,3,7,8,5,1)
K=5
OUT=args.output;OUT.mkdir(parents=True,exist_ok=True)
# Use legacy labels solely as interface names; all rows come from candidate.
mp={int(k):v for k,v in json.loads((REF/'legacy_mapping.json').read_text()).items()}
rows={}
for line in (args.table).read_text().splitlines():
    q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));rows[q,b]=(w,1 if d=='R' else -1,t)
for q in {q for q,b in rows}|{254}:mp.setdefault(q,q+10000)
reverse={v:k for k,v in mp.items()}
table={(mp[q],b):(w,d,mp[t])for(q,b),(w,d,t)in rows.items()}
patterns=defaultdict(set)
@lru_cache(maxsize=200000)
def prefix(atoms,k):
    if k==0:return ((),)
    if not atoms:return ((0,)*k,)
    a,*tail=atoms;tail=tuple(tail)
    if a[0]=='blank':return ((0,)*k,)
    if a[0] in ('list','opaque'):return tuple(itertools.product((0,1),repeat=k))
    assert a[0]=='run'
    bit,n=a[1:];n0=n[0];assert n0>=0
    if not any(n[1:]):
        if n0>=k:return ((bit,)*k,)
        return tuple((bit,)*n0+p for p in prefix(tail,k-n0))
    out=set()
    for size in range(n0,k+1):
        if size>=k:out.add((bit,)*k);break
        for p in prefix(tail,k-size):out.add((bit,)*size+p)
    if n0>k:out.add((bit,)*k)
    return tuple(out)
seen=set()
def observe(q,dr,left,right):
    q=reverse[q]
    # Collect all states; identical local prefix products need one evaluation.
    lp=prefix(tuple(left),K+1 if dr==-1 else K)
    rp=prefix(tuple(right),K if dr==-1 else K+1)
    key=(q,dr,lp,rp)
    if key in seen:return
    seen.add(key)
    for a,b in itertools.product(lp,rp):
        tape=tuple(reversed(a[1:]))+(a[0],)+b if dr==-1 else tuple(reversed(a))+b
        patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
old=s.State.step
def step(self,table,lemmas,clock,motion):
    self.key()
    observe(self.q,self.direction,self.left,self.right)
    src,dst=(self.right,self.left) if self.direction==1 else(self.left,self.right)
    if src and src[0][0]=='run':
        a=src[0];w,d,q=table[self.q,a[1]]
        if q==self.q and d==self.direction:
            length=a[2]
            # Cover interiors skipped by unary acceleration; conservative independent lengths.
            count=K if any(length[1:]) else min(K,max(0,length[0]-1))
            for j in range(1,count+1):
                rem=s.add(s.var(1),s.num(1)) if any(length[1:]) else s.num(length[0]-j)
                ss=[s.run(a[1],rem)]+src[1:];dd=[s.run(w,j)]+dst
                observe(self.q,self.direction,dd if self.direction==1 else ss,ss if self.direction==1 else dd)
    return old(self,table,lemmas,clock,motion)
s.State.step=step
t0=time.time();lemmas,blocks=s.prove_blocks(table)
sites=json.loads((args.sites).read_text())
invariants=json.loads(args.sites.with_name('invariants.json').read_text())
code={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
total=0
for i,(pc,op,arg) in enumerate(sites):
    inv=invariants[i]
    if inv is None:continue
    s.CURRENT_DOMAIN=inv
    branches=([False] if inv[arg]&1 else [])+([True] if inv[arg]&6 else []) if op=='dec' else [False]
    for pos in branches:
        s.case(table,lemmas,[pc,code[op],arg],pos);total+=1
    if(i+1)%500==0:print(i+1,'sites',len(seen),'localviews',time.time()-t0,flush=True)
q,h,ones=74,0,set()
for _ in range(args.startup_steps):
    patterns[q].add(sum(int(h+j-K in ones)<<j for j in range(2*K+1)))
    w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
assert(q,h)==(84,-2)
(OUT/'patterns_k5.txt').write_text(''.join(f'{q} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
rec={'radius':K,'source_outcomes':total,'states':len(patterns),'patterns':{q:len(p)for q,p in sorted(patterns.items())},'localviews':len(seen),'elapsed_seconds':time.time()-t0,'scope':'Conservative windows including unary-loop interiors and generic-list-block traces; screening only, candidate requires new complete symbolic verification.'}
(OUT/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({k:v for k,v in rec.items()if k!='patterns'}),flush=True)

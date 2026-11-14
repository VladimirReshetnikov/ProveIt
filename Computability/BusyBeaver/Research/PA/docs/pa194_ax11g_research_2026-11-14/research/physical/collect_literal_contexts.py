"""Heuristic local context envelope from literal universal proof executions.

The subsequent candidate checks must independently rederive whole-frame contracts.
"""
from pathlib import Path
import sys,json,itertools,functools,math,collections
HERE=Path(__file__).resolve().parent
name=sys.argv[1] if len(sys.argv)>1 else '4l'
R=4
ref=HERE/'literal_reference'
table_path=HERE/'inputs'/f'{name}.native.tm'
sites_path=HERE/'inputs'/f'{name}.sites.json'
sys.path.insert(0,str(ref))
import symbolic_runtime as sym
import independent_runtime as runtime
sym.HEADER_BASE=48
rows={}
for ln in table_path.read_text().splitlines():
 if ln.strip():
  q,b,w,d,n=ln.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
states={q for q,b in rows}
mp={int(k):v for k,v in json.loads((ref/'legacy_mapping.json').read_text()).items()}
for q in states|{254}:mp.setdefault(q,q+10000)
back={v:k for k,v in mp.items()}
table={(mp[q],b):(w,d,mp[n]) for(q,b),(w,d,n) in rows.items()}
lemmas,_=sym.prove_blocks(table)
seen=set();patterns=collections.defaultdict(set)
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
@functools.lru_cache(maxsize=500000)
def prefix(atoms,k):
 if not k:return ((),)
 if not atoms:return tuple(itertools.product((0,1),repeat=k))
 a,*tail=atoms;tail=tuple(tail)
 if a[0]=='blank':return ((0,)*k,)
 if a[0] in ('opaque','list'):return tuple(itertools.product((0,1),repeat=k))
 assert a[0]=='run'
 coeff=a[2];minimum=coeff[0];g=math.gcd(*coeff[1:])
 lens=[min(k,minimum)] if not g else list(range(minimum,k,g))+[k]
 out=set()
 for n in lens:
  if n>=k:out.add((a[1],)*k)
  else:
   for rest in prefix(tail,k-n):out.add((a[1],)*n+rest)
 return tuple(out)
def record(q,onl,left,right):
 if len(patterns[q])==(1<<(2*R+1)):return
 key=(q,onl,tuple(left),tuple(right))
 if key in seen:return
 seen.add(key)
 lp=prefix(tuple(left),R+1 if onl else R)
 rp=prefix(tuple(right),R if onl else R+1)
 for a,b in itertools.product(lp,rp):
  word=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  patterns[q].add(sum(v<<i for i,v in enumerate(word)))
oldstep=sym.State.step
def step(self,t,l,c,m):
 self.key();q=back[self.q]
 if q not in BOX:return oldstep(self,t,l,c,m)
 record(q,self.direction<0,self.left,self.right)
 # Include all locally distinguishable interior positions in an accelerated run.
 src,dst=(self.right,self.left) if self.direction==1 else (self.left,self.right)
 if src and src[0][0]=='run':
  a=src[0];w,d,n=t[self.q,a[1]]
  if n==self.q and d==self.direction:
   coeff=a[2];minimum=coeff[0];g=math.gcd(*coeff[1:]);cap=2*R+1
   lens=[min(cap,minimum)] if not g else list(range(minimum,cap,g))+[cap]
   for size in lens:
    for consumed in range(size):
     A=[sym.run(a[1],size-consumed)]+src[1:]
     B=[sym.run(w,consumed)]+dst
     record(q,self.direction<0,B if self.direction>0 else A,A if self.direction>0 else B)
 return oldstep(self,t,l,c,m)
sym.State.step=step
# Generic block inductions supply observations in arbitrary list-element contexts.
sym.prove_blocks(table)
sites=json.loads(sites_path.read_text());opcodes={'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}
for i,(p,op,a) in enumerate(sites):
 for positive in ([False,True] if op=='dec' else [False]):sym.case(table,lemmas,[p,opcodes[op],a],positive)
 if (i+1)%100==0:print('sites',i+1,flush=True)
# Whole blank-start trace; a candidate must retain exact original seed.
q=74;h=0;ones=set()
startup=58154
if name!='primary':startup=58320
for _ in range(startup):
 patterns[q].add(sum(int(h+i in ones)<<(i+R) for i in range(-R,R+1)))
 w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
# Root state84 is the interface; all arithmetic box controls remain eligible.
base=json.loads((HERE/f'{name}_contexts.json').read_text())['contexts']
for q,ws in base.items():patterns[int(q)].update(ws)
contexts={q:sorted(ws) for q,ws in patterns.items() if q not in (74,84)}
data={'radius':R,'rows':[[q,b,w,int(d==1),n] for(q,b),(w,d,n) in sorted(rows.items())],'contexts':contexts}
(HERE/f'{name}_literal_r{R}.json').write_text(json.dumps(data))
with (HERE/f'{name}_literal_r{R}.txt').open('w') as f:
 print(R,len(data['rows']),file=f)
 for row in data['rows']:print(*row,file=f)
 print(len(contexts),file=f)
 for q,ws in sorted(contexts.items()):print(q,len(ws),*ws,file=f)
print('contexts',sum(map(len,contexts.values())),'controls',len(contexts),'max',max(map(len,contexts.values())),flush=True)

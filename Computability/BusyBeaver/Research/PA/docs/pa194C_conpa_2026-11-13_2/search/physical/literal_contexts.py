from pathlib import Path
import json,sys,itertools,time
from functools import lru_cache
from collections import defaultdict
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'reference/pa194'
sys.path.insert(0,str(BASE/'verification/independent/reference'))
import symbolic_runtime as sym
import independent_runtime as runtime
sym.HEADER_BASE=48
K=int(sys.argv[1]) if len(sys.argv)>1 else 4
mapping={int(k):v for k,v in json.loads((BASE/'verification/independent/reference/legacy_mapping.json').read_text()).items()}
native=runtime.table(BASE/'construction/tables/pa194.native.tm')
for q in {q for q,b in native}|{254}:mapping.setdefault(q,q+10000)
inverse={v:k for k,v in mapping.items()}
table={(mapping[q],b):(w,d,mapping[t]) for (q,b),(w,d,t) in native.items()}
lemmas,certificates=sym.prove_blocks(table)
unknown={e[1][0] for cert in certificates for e in cert['trace'] if e[0] in ('literal','unary')}
print('FULL_LEMMA_STATES',[inverse[q] for q in sorted(unknown)],flush=True)
@lru_cache(maxsize=200000)
def prefixes(atoms,k):
 if k==0:return ((),)
 if not atoms:return ((0,)*k,)
 a,*tail=atoms;tail=tuple(tail)
 if a[0]=='blank':return ((0,)*k,)
 if a[0]=='list':return tuple(itertools.product((0,1),repeat=k))
 if a[0]=='run':
  _,b,aff=a;const=aff[0];assert const>=0
  if const>=k:return ((b,)*k,)
  if not any(aff[1:]):return tuple((b,)*const+p for p in prefixes(tail,k-const))
  # Ignore correlations and divisibility: every possible length >= constant.
  return tuple(set((b,)*n+p for n in range(const,k+1) for p in prefixes(tail,k-n)))
 raise ValueError(a)
patterns=defaultdict(set);seen=set();count=0

def record(q,d,l,r):
 global count
 if q in unknown:return
 lp=prefixes(tuple(l),K+int(d==-1));rp=prefixes(tuple(r),K+int(d==1))
 key=q,d,lp,rp
 if key in seen:return
 seen.add(key);count+=1
 for a,b in itertools.product(lp,rp):
  bits=tuple(reversed(a[1:]))+(a[0],)+b if d==-1 else tuple(reversed(a))+b
  mask=sum(v<<i for i,v in enumerate(bits));patterns[inverse[q]].add(mask)
orig_step=sym.State.step

def step(self,table,lemmas,clock,motion):
 self.key();record(self.q,self.direction,self.left,self.right)
 src,dst=(self.right,self.left) if self.direction==1 else (self.left,self.right)
 if src and src[0][0]=='run':
  a=src[0];act=table[self.q,a[1]]
  if act[2]==self.q and act[1]==self.direction:
   src2=[sym.run(a[1],sym.add(sym.num(1),sym.var(1)))]+src[1:]
   dst2=[sym.run(act[0],sym.var(1))]+dst
   l,r=(dst2,src2) if self.direction==1 else (src2,dst2)
   record(self.q,self.direction,l,r)
 return orig_step(self,table,lemmas,clock,motion)
sym.State.step=step
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
sites=json.loads((BASE/'construction/source/pa194.sites.json').read_text())
start=time.monotonic();steps=0
for i,(p,op,arg) in enumerate(sites):
 for pos in ([False,True] if op=='dec' else [False]):
  result=sym.case(table,lemmas,[p,ops[op],arg],pos);steps+=result['symbolic_steps']
 if (i+1)%500==0:print('SITES',i+1,'OBS',count,'PATTERNS',sum(map(len,patterns.values())),'SEC',round(time.monotonic()-start,2),flush=True)
# Exact startup. Omit lemma states to retain general abstract contexts.
tape=set();q=74;head=0
for _ in range(58154):
 if mapping[q] not in unknown:patterns[q].add(sum(int(head+i-K in tape)<<i for i in range(2*K+1)))
 w,d,q=native[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=d
assert q==84 and head==-2
out=HERE/'generated'/f'literal_patterns_k{K}.txt'
out.write_text(''.join(f'{q} {v}\n' for q in sorted(patterns) for v in sorted(patterns[q])))
receipt={'sites':len(sites),'contracts':4780,'observations':count,'patterns':sum(map(len,patterns.values())),'omitted_list_sweep_states':[inverse[q] for q in sorted(unknown)],'symbolic_steps':steps,'k':K}
(HERE/'generated'/f'literal_contexts_k{K}.json').write_text(json.dumps(receipt,indent=2))
print(receipt,flush=True)

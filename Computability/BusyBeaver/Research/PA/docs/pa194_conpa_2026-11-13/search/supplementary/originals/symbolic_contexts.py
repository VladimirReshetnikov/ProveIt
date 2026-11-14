from pathlib import Path
import sys,json,itertools,time
ROOT=Path('/dev/shm/pa_reader_search/pa_consistency_research/construction195')
sys.path.insert(0,str(ROOT))
import compiler as c
from support import apply
from functools import lru_cache
from collections import defaultdict
K=4
c.MACROS[(('leaf','inc',1),('leaf','inc',1))]=99
c.MACROS[((('leaf','inc',1),('leaf','inc',1)),(('leaf','inc',1),('leaf','inc',1)))]=190
rows,ix,shape=c.build(c.read_grammar(ROOT/'grammar.json'))
folds=json.loads((ROOT/'folds.json').read_text());rows,alias=apply(rows,folds)
sites,instructions,contracts=c.source(c.read_grammar(ROOT/'grammar.json'))
# Superset of all finite prefixes of the symbolic stream, for all n>=0
# and all register files. l is listed from the boundary toward negative cells.
@lru_cache(maxsize=200000)
def prefixes(s,k):
 if k==0:return ((),)
 if not s:return ((0,)*k,)
 x,*tail=s;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
 if x[0]=='r':
  _,b,a,d=x;assert a>=0 and d>=0,(s,k)
  if a==0:
   if d>=k:return ((b,)*k,)
   return tuple((b,)*d+p for p in prefixes(tail,k-d))
  # Covers the possible residues without assuming correlations with other runs.
  out=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:out.add((b,)*k);break
   for p in prefixes(tail,k-size):out.add((b,)*size+p)
  return tuple(out)
 raise ValueError(x)

patterns=defaultdict(set);observations=0
seen=set()
def observe(s):
 global observations
 q,onl,l,r=s
 if q in c.BOXSTATES:return
 # Include every point, even normalization points, making the sets conservative.
 lp=prefixes(l,K+1 if onl else K)
 rp=prefixes(r,K if onl else K+1)
 key=(q,onl,lp,rp)
 if key in seen:return
 seen.add(key);observations+=1
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1
  v=sum(bit<<i for i,bit in enumerate(tape));patterns[q].add(v)

result=c.validate(rows,contracts,observe=observe)
print('VALIDATE',result,'observations',observations,'pattern_total',sum(map(len,patterns.values())),flush=True)
assert result['ok']
# Literal startup includes every intermediate control until the certified frame.
tape=set();q=74;head=0
for step in range(58154):
 if q not in c.BOXSTATES:
  v=sum(int(head+i-K in tape)<<i for i in range(2*K+1));patterns[q].add(v)
 w,d,q=rows[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=1 if d else -1
assert q==84 and head==-2
out=Path('root_research/symbolic_patterns_k4.txt')
out.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
Path('root_research/symbolic_contexts_receipt.json').write_text(json.dumps({'k':K,'contracts':result,'symbolic_frame_observations':observations,'patterns':{q:len(p) for q,p in patterns.items()},'excluded_states':sorted(c.BOXSTATES),'startup_steps':58154},indent=2))
print('COMPLETE',len(patterns),sum(map(len,patterns.values())),str(out),flush=True)

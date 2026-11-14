from pathlib import Path
import sys,json,itertools,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
import argparse
ap=argparse.ArgumentParser(description='Extract conservative source/startup tape-window contexts for optional local merge search')
ap.add_argument('family',choices=['A','B','C'])
ap.add_argument('--radius',type=int,default=4)
ap.add_argument('--out',type=Path)
args=ap.parse_args()
K=args.radius
assert 1<=K<=8
OUT=args.out or HERE/'generated'/(args.family+str(K))
OUT.mkdir(parents=True,exist_ok=True)
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
from functools import lru_cache
from collections import defaultdict
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99
c.MACROS[((inc,inc),(inc,inc))]=190
if args.family=='B':
 tablepath=HERE/'inputs/B.native.tm';grammarpath=HERE/'inputs/B.grammar.json'
else:
 tablepath=ROOT/'construction/tables'/('pa194c.native.tm' if args.family=='C' else 'pa194.native.tm')
 grammarpath=ROOT/'construction/source/pa194.grammar.json'
if args.family=='C':
 original_nodes=c.raw_nodes
 def changed_nodes():
  nodes=original_nodes();nodes['node163']=('node6','node147');nodes['node170']=(('node36',('node167','node145')),'node57');return nodes
 c.raw_nodes=changed_nodes
rows={}
for line in tablepath.read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
sites,instructions,contracts=c.source(c.read_grammar(grammarpath))
startup_steps=57922 if args.family=='C' else 58154
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
for step in range(startup_steps):
 if q not in c.BOXSTATES:
  v=sum(int(head+i-K in tape)<<i for i in range(2*K+1));patterns[q].add(v)
 w,d,q=rows[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=1 if d else -1
assert q==84 and head==-2
out=(OUT/f'symbolic_patterns_k{K}.txt')
out.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
(OUT/'symbolic_contexts_receipt.json').write_text(json.dumps({'k':K,'contracts':result,'symbolic_frame_observations':observations,'patterns':{q:len(p) for q,p in patterns.items()},'excluded_states':sorted(c.BOXSTATES),'startup_steps':startup_steps},indent=2))
print('COMPLETE',len(patterns),sum(map(len,patterns.values())),str(out),flush=True)

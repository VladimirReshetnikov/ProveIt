from pathlib import Path
import itertools,json
from functools import lru_cache
from collections import defaultdict
import sys,os
sys.path.insert(0,os.environ.get('PA194C_CONSTRUCTION',str(Path(__file__).resolve().parents[2]/'construction')))
import build194C as a
a.enable_combined()
c=a.c
ROOT=Path(__file__).resolve().parent
K=4
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
  out=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:out.add((b,)*k);break
   for p in prefixes(tail,k-size):out.add((b,)*size+p)
  return tuple(out)
 raise ValueError(x)
patterns=defaultdict(set);seen=set()
def observe(s):
 q,onl,l,r=s
 if q in c.BOXSTATES:return
 lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
 key=q,onl,lp,rp
 if key in seen:return
 seen.add(key)
 for a,b in itertools.product(lp,rp):
  tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
  assert len(tape)==2*K+1
  patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
rows=a.b.read_table(a.OUT/'pa194C.native.tm');sites,ins,cs=c.source(c.read_grammar(a.HERE/'source/pa194.grammar.json'))
result=c.validate(rows,cs,observe=observe);print(result,flush=True);assert result['ok']
tape=set();q=74;head=0
for step in range(57922):
 if q not in c.BOXSTATES:patterns[q].add(sum(int(head+i-K in tape)<<i for i in range(2*K+1)))
 w,d,q=rows[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=1 if d else -1
assert q==84 and head==-2
(ROOT/'194C_symbolic_patterns_k4.txt').write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
(ROOT/'194C_contexts_receipt.json').write_text(json.dumps({'k':K,'contracts':result,'observations':len(seen),'patterns':{q:len(p) for q,p in patterns.items()}},indent=2)+'\n')
print('COMPLETE',len(patterns),sum(map(len,patterns.values())),flush=True)

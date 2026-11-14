from pathlib import Path
import sys,json,itertools,time
from functools import lru_cache
from collections import defaultdict
ROOT=Path(__file__).resolve().parents[2]/'construction'
OUT=Path(__file__).resolve().parent/'cached';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT))
import compiler as c
import baseline_tools as b
K=int(sys.argv[1]) if len(sys.argv)>1 else 4
rows=b.read_table(ROOT/'candidate/pa194C.native.tm')
old_nodes=c.raw_nodes
def new_nodes():
    ns=old_nodes();ns['node163']=('node6','node147');ns['node170']=(('node36',('node167','node145')),'node57');return ns
c.raw_nodes=new_nodes
c.MACROS[(('leaf','inc',1),('leaf','inc',1))]=99
c.MACROS[((('leaf','inc',1),('leaf','inc',1)),(('leaf','inc',1),('leaf','inc',1)))]=190
sites,ins,cs=c.source(c.read_grammar(ROOT/'inputs/pa194.grammar.json'))
@lru_cache(maxsize=300000)
def prefixes(s,k):
    if k==0:return ((),)
    if not s:return ((0,)*k,)
    x,*tail=s;tail=tuple(tail)
    if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
    if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
    if x[0]=='r':
        _,v,a,d=x
        assert a>=0 and d>=0
        if a==0:
            if d>=k:return ((v,)*k,)
            return tuple((v,)*d+p for p in prefixes(tail,k-d))
        out=set()
        for n in range(k+1):
            size=a*n+d
            if size>=k:out.add((v,)*k);break
            for p in prefixes(tail,k-size):out.add((v,)*size+p)
        return tuple(out)
    raise ValueError(x)
patterns=defaultdict(set);seen=set()
def observe(s):
    q,onl,l,r=s
    if q in c.BOXSTATES:return
    lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
    key=(q,onl,lp,rp)
    if key in seen:return
    seen.add(key)
    for a,bb in itertools.product(lp,rp):
        tape=tuple(reversed(a[1:]))+(a[0],)+bb if onl else tuple(reversed(a))+bb
        assert len(tape)==2*K+1
        patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
t=time.time();result=c.validate(rows,cs,observe=observe);assert result['ok'],result
q,h,ones=74,0,set()
for step in range(57922):
    if q not in c.BOXSTATES:patterns[q].add(sum(int(h+i-K in ones)<<i for i in range(2*K+1)))
    w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=1 if d else -1
assert (q,h)==(84,-2)
(OUT/f'patterns_k{K}.txt').write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
receipt={'radius':K,'validation':result,'elapsed':time.time()-t,'observed_states':len(patterns),'patterns':{q:len(p) for q,p in sorted(patterns.items())},'symbolic_observations':len(seen),'scope':'heuristic screening windows; any candidate needs independent universal verification'}
(OUT/f'contexts_k{K}.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='patterns'}))

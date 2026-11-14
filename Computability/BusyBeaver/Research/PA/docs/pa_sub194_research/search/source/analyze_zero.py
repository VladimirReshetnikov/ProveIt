from pathlib import Path
import json,sys,collections
sys.path.insert(0,str(Path(__file__).parent))
import compiler as c
ROOT=Path(__file__).parent
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
ns={k:tup(v) for k,v in json.loads((ROOT/'nodes.json').read_text()).items()}
c.raw_nodes=lambda:ns
grammar=c.read_grammar(ROOT/'pa194.grammar.json')
sites,ins,contracts=c.source(grammar)
N=len(ins)
# Abstract value is bitset {zero,positive}. Join is pointwise union.
inv=[None]*N
inv[25]=(2,1,1,1,1,1,1,1,1)
todo=collections.deque([25]);visited=0
while todo:
 p=todo.popleft();s=inv[p];row=ins[p];visited+=1
 out=[]
 if row[0]=='inc':
  _,r,n=row;t=list(s);t[r]=2;out=[(n,tuple(t))]
 elif row[0]=='dec':
  _,r,z,n=row
  if s[r]&1:t=list(s);t[r]=1;out.append((z,tuple(t)))
  if s[r]&2:t=list(s);t[r]=3;out.append((n,tuple(t)))
 elif row[0]=='jump':out=[(row[1],s)]
 for n,t in out:
  v=t if inv[n] is None else tuple(a|b for a,b in zip(inv[n],t))
  if v!=inv[n]:inv[n]=v;todo.append(n)
counts=collections.Counter()
impossible=[]
for p,row in enumerate(ins):
 if row[0]=='dec':
  mask=inv[p][row[1]] if inv[p] else 0;counts[mask]+=1
  if mask!=3:impossible.append({'pc':p,'path':''.join(map(str,sites[p][0])),'row':row,'mask':mask,'state':inv[p]})
print('sites',N,'iterations',visited,'branch_counts',dict(counts),'unreachable_sites',sum(x is None for x in inv))
(ROOT/'zero_invariants.json').write_text(json.dumps({'sites':[[''.join(map(str,p)),op,a]for p,op,a in sites],'instructions':ins,'invariants':inv,'forced':impossible},indent=2))
print(json.dumps(impossible[:20],indent=2))

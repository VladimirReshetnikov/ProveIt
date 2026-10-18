"""Source-certified removal of two loops entered with a zero counter.
No TM correctness claim: this tool counts structural decoder nodes and emits
experimental DAGs for separately checked contextual compilation.
"""
from search_common import *
from functools import lru_cache
nodes,_=audit.parse_source(B/'sources/Prog254.v')
@lru_cache(None)
def unfold(n):
 return ('N', *(unfold(a) if op=='CN' else (op[1:],a) if a is not None else ('H',) for op,a in nodes[n]))
def intern(t):
 compact={};seen={}
 def walk(t):
  if t[0]!='N':return t
  pair=(walk(t[1]),walk(t[2]))
  if pair not in seen:
   n=len(seen);seen[pair]=n;compact[n]=pair
  return ('N',seen[pair])
 return compact,walk(t)[1]
@lru_cache(None)
def bounds(t):
 if t[0]!='N':return (0,t[1] if t[0]=='B' else 1 if t[0]=='D' else 0,t[1] if t[0]=='C' else 0)
 a,b=bounds(t[1]),bounds(t[2]);return (1+max(a[0],b[0]),max(a[1]-1,b[1]),max(a[2],b[2]-1))
def closed(t):return bounds(t)[1:]==(0,0)
def simplify(t):
 if t[0]!='N':return t
 a,b=map(simplify,t[1:])
 if a==('B',0) and closed(b):return b
 if b==('B',0) and closed(a):return a
 return ('N',a,b)
def replace(t,pc):
 if not pc:return ('B',0)
 a,b=t[1:]
 if pc[0]=='0':a=replace(a,pc[1:])
 else:b=replace(b,pc[1:])
 return ('N',a,b)
def subtree(t,pc):
 for b in pc:t=t[int(b)+1]
 return t
root=unfold(0);N,R=intern(root)
print('baseline',len(N),bounds(root))
paths=('11101001011000110','11111100')
for p in paths:print('REMOVAL',p,subtree(root,p),'closed',closed(subtree(root,p)))
reports=[]
for choice in ((paths[0],),(paths[1],),paths):
 t=root
 for p in choice:t=replace(t,p)
 t=simplify(t);n,r=intern(t)
 report=dict(paths=choice,nodes=len(n),bounds=bounds(t),root=r)
 reports.append(report)
 label='both' if len(choice)==2 else str(paths.index(choice[0]))
 Path(__file__).with_name('pruned-dag-'+label+'.json').write_text(json.dumps(dict(root=r,nodes=n,paths=choice),indent=2)+'\n')
 print(report)
Path(__file__).with_name('source-prune-results.json').write_text(json.dumps(reports,indent=2)+'\n')

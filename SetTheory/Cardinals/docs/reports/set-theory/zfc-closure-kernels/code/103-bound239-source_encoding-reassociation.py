from pathlib import Path
import json
from functools import cache
D=json.loads((Path(__file__).parent/'mapping.json').read_text())
S=[tuple(x) for x in D['structures']];ids={x:n for n,x in enumerate(S)}
@cache
def paths(n):
 x=S[n]
 if isinstance(x[0],str):return (('',x[0],x[1]),)
 return tuple((str(b)+p,op,r) for b in (0,1) for p,op,r in paths(x[b]))
@cache
def closed(n):
 for p,op,r in paths(n):
  if op=='CH':return False
  if op=='CC' and r>p.count('1'):return False
  if op=='CB' and r>p.count('0'):return False
  if op=='CD' and '0' not in p:return False
 return True
@cache
def leaves(n):return len(paths(n))
root=D['pathnode']['']
occ={n:[] for n in range(len(S))}
for p,n in D['pathnode'].items():occ[n].append(p)
def gc(root,db):
 todo=[root];seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n)
  if isinstance(db[n][0],int):todo.extend(db[n])
 return seen
base=gc(root,S)
@cache
def depth(n):
 return max(map(len,[p for p,o,r in paths(n)]))
@cache
def zr(n):
 return max(max(map(len,p.split('1'))) for p,o,r in paths(n))
print('closed',sum(closed(n) for n in base),'base',len(base),'depth',depth(root),'zeros',zr(root))
for n in base:
 x=S[n]
 if isinstance(x[0],str):continue
 # arbitrary associativity on closed chunks
 candidates=[]
 A,B=x
 if isinstance(S[B][0],int):
  B,C=S[B]
  if closed(A) and closed(B) and closed(C):candidates.append(('L',A,B,C))
 A,C=x
 if isinstance(S[A][0],int):
  A,B=S[A]
  if closed(A) and closed(B) and closed(C):candidates.append(('R',A,B,C))
 for direction,A,B,C in candidates:
  db=list(S)
  def intern(key):
   if key not in db:db.append(key)
   return db.index(key)
  replacement=intern((intern((A,B)),C)) if direction=='L' else intern((A,intern((B,C))))
  # change every occurrence node n by replacement; intern all changed ancestors
  from functools import cache
  @cache
  def change(k):
   if k==n:return replacement
   if isinstance(S[k][0],str):return k
   return intern(tuple(change(e) for e in S[k]))
  nr=change(root); live=gc(nr,db)
  if len(live)<=len(base):
   qs=[q for q,ns in D['qnodes'].items() if ns==[n]]
   print('ROTATE',n,qs,direction,'chunks',A,B,C,'total',len(live),'delta',len(live)-len(base),'new nodes',[db[i] for i in live if i>=len(S)],'dead',base-live)

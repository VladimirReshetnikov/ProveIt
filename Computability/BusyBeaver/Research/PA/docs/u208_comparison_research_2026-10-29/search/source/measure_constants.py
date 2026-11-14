import json,pathlib,functools,random,time,sys
kvalue=int(sys.argv[1]) if len(sys.argv)>1 else 5
P=pathlib.Path(__file__).resolve().parent/'inputs';rows=json.loads((P/'k215_sites.json').read_text());leaves={p:(o,a)for p,o,a in rows}
def parse(p=''):return leaves[p]if p in leaves else(parse(p+'0'),parse(p+'1'))
root=parse()
def leaf(n):return isinstance(n[0],str)
@functools.cache
def size(n):return 1 if leaf(n)else size(n[0])+size(n[1])
@functools.cache
def nodes(n):return frozenset([n])if leaf(n)else nodes(n[0])|nodes(n[1])|{n}
def serial(a):return a[0]if len(a)==1 else(a[0],serial(a[1:]))
def forest(lo,hi):
 out=[]
 def walk(n,k=0):
  end=k+size(n)
  if end<=lo or k>=hi:return
  if lo<=k and end<=hi:out.append(n);return
  walk(n[0],k);walk(n[1],k+size(n[0]))
 walk(root);assert sum(size(n)for n in out)==hi-lo;return serial(out)
recipe=json.loads((P/'source_recipe.json').read_text());m={k:forest(*v)for k,v in recipe['macro_intervals'].items()}
M={'c':m['168'],'1':m['177'],'0':m['171'],'I':m['119'],'R':m['181'],'Q':m['180'],'N':m['218'],'Eq':m['182'],'5':(m['177'],((('CI',1),('CI',1)),(('CI',1),('CI',1))))}
def incs(k):
 return ('CI',1) if k==1 else (incs(k//2),incs(k-k//2))
M['5']=m['177'] if kvalue==1 else (m['177'],incs(kvalue-1))
word='c 1 1 0 R N 1 5 Eq I c 1 c R I I Q 1 1 c R c I Q N I Q'.split()
# prune original shell, inserting singleton placeholder representing full newtree
stub=('STUB',0)
def splice(n,k=0):
 end=k+size(n)
 if end<=2885 or k>=4482:return n
 if 2885<=k and end<=4482:return stub if k==2885 else None
 a=splice(n[0],k);b=splice(n[1],k+size(n[0]));return b if a is None else a if b is None else(a,b)
base=splice(root);pool=nodes(base)
for v in M.values():pool|=nodes(v)
# intervalDP additivecostfornewnodes, iterativelyaccept newlysharedsubexpressions.
N=len(word);best=None
for iteration in range(8):
 D={}
 for i,w in enumerate(word):D[i,i+1]=(M[w],0)
 for span in range(2,N+1):
  for i in range(N-span+1):
   j=i+span;opts=[]
   for k in range(i+1,j):
    a,ca=D[i,k];b,cb=D[k,j];n=(a,b);opts.append((ca+cb+(n not in pool),len(nodes(n)-pool),k,n))
   cost,_,_,n=min(opts,key=lambda x:x[:3]);D[i,j]=(n,cost)
 result=D[0,N][0]
 def fill(n):return result if n==stub else n if leaf(n)else(fill(n[0]),fill(n[1]))
 full=fill(base);met={'dag':len(nodes(full)),'leaves':size(full),'emitter_leaves':size(result),'tokens':N,'iteration':iteration};print(met,flush=True)
 if best is None or met['dag']<best[0]:best=(met['dag'],full,met)
 pool|=nodes(result)
def emit(n,p=''):return [[p,*n]]if leaf(n)else emit(n[0],p+'0')+emit(n[1],p+'1')
out=pathlib.Path(__file__).resolve().parent;(out/f'adjoin_source_k{kvalue}.json').write_text(json.dumps(emit(best[1]),separators=(',',':'))+'\n');(out/f'adjoin_metrics_k{kvalue}.json').write_text(json.dumps(best[2],indent=2))

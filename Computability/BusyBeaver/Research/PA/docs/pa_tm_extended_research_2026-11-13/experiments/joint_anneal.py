import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'verification'))
from words import *
from layout import *
from functools import lru_cache
import random,math,time
random.seed(3175)
CONFIG=json.loads(Path('config.json').read_text())
ns=raw_nodes()
def tree(s):
 if isinstance(s,str)and s.startswith('x'):
  a,b=ns[s];return(tree(a),tree(b))
 return s
initial=tree('x67')
macroattrs={}
def attrs(t):
 if isinstance(t,str):
  if t in macroattrs:return macroattrs[t]
  a=attrs(ns[t]);macroattrs[t]=a;return a
 if not isnode(t):return (0,0,0)
 h1,l1,m1=attrs(t[0]);h2,l2,m2=attrs(t[1]);return 1+max(h1,h2),l1+1,max(1+l1,m1,m2)
for m in MACROS:attrs(m)
def stats(t):
 intern={}
 def rec(t):
  if not isnode(t):return attrs(t)
  if t in intern:return intern[t]
  h1,l1,m1=rec(t[0]);h2,l2,m2=rec(t[1]);a=1+max(h1,h2),l1+1,max(1+l1,m1,m2);intern[t]=a;return a
 a=rec(t);return len(intern),a,list(intern)
def replace(t,x,y):
 if t==x:return y
 if isnode(t):return replace(t[0],x,y),replace(t[1],x,y)
 return t
def rotations(t):
 if isnode(t[0]):
  a,b=t[0];yield a,(b,t[1])
 if isnode(t[1]):
  b,c=t[1];yield (t[0],b),c

def assign(t,word):
 it=iter(word)
 def rec(t):
  if not isnode(t):return next(it)
  return rec(t[0]),rec(t[1])
 return rec(t)
S=[tuple(s)if isinstance(s,list)else s for s in CONFIG['symbols']]
def make_word(meta):
 flip,sw,perm,roles=meta
 out=CONFIG['prefix'][:]
 for j in perm:out+=CONFIG['heads'][flip][j][roles[j]]
 out+=CONFIG['gate'][flip][sw]+CONFIG['suffix']
 return [S[x]for x in out]
def mutate(meta):
 flip,sw,perm,roles=meta;perm=list(perm);roles=list(roles)
 k=random.randrange(12)
 if k<6:roles[k]=random.randrange(len(CONFIG['heads'][flip][k]))
 elif k<10:
  a,b=random.sample(range(6),2);perm[a],perm[b]=perm[b],perm[a]
 elif k==10:sw=1-sw
 else:flip=1-flip
 return flip,sw,tuple(perm),tuple(roles)

def cost(t):
 n,(h,l,m),choices=stats(t)
 if m>6 or h>38:return n+max(0,m-6)*2+max(0,h-38),n,0,choices
 r,idx,sh=build(t);ops=opportunities_fast(r,sh);f=len(max_matching(ops));return n-f,n,f,choices
meta=(0,0,tuple(range(6)),(0,)*6)
assert make_word(meta)==w
best=cost(initial)[0];best_tree=initial;best_meta=meta;start=time.time();pool=[(initial,meta)]
print('initial',cost(initial)[:3],flush=True)
for cycle in range(1000):
 t,meta=random.choice(pool);c,n,f,choices=cost(t)
 for j in range(3000):
  if random.random()<0.09:
   nm=mutate(meta);nt=assign(t,make_word(nm))
  else:
   nm=meta;node=random.choice(choices);rs=list(rotations(node))
   if not rs:continue
   nt=replace(t,node,random.choice(rs))
  nc,nn,nf,nchoices=cost(nt)
  temp=0.20+0.85*(1-j/3000)
  if nc<=c or random.random()<math.exp((c-nc)/temp):
   t,c,n,f,choices,meta=nt,nc,nn,nf,nchoices,nm
   if c<=best and n<=70:
    if c<best:
     best=c;best_tree=t;best_meta=meta;print('BEST',best,'nodes',n,'folds',f,'meta',meta,'cycle',cycle,'iteration',j,'seconds',time.time()-start,flush=True)
     Path(f'joint_{best}.grammar.json').write_text(json.dumps(encode(t),indent=2));Path(f'joint_{best}.meta.json').write_text(json.dumps(meta))
     if best<62:raise SystemExit()
    if c==62 and (not pool or all(meta!=pm for _,pm in pool)):
     pool.append((t,meta));print('pool',len(pool),meta,flush=True)
 print('cycle',cycle,'best',best,'pool',len(pool),'secs',time.time()-start,flush=True)

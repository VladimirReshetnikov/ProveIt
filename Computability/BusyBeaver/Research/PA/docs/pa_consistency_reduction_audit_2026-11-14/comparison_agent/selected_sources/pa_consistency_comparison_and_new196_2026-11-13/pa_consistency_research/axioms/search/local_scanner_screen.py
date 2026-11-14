from support import *
from functools import lru_cache
p=(INC,INC);c.MACROS[p]=99;c.MACROS[(p,p)]=190
@lru_cache(None)
def leaves(t):
 if isinstance(t,str):return leaves(raw[t])
 return leaves(t[0])+leaves(t[1])if c.isnode(t)else 1
@lru_cache(None)
def sb(t,k=0):
 if k>=6:return leaves(t)
 if isinstance(t,str):return sb(raw[t],k)
 return sb(t[0],k+1)+sb(t[1],0)if c.isnode(t)else 0
def occurrences(t,path=()):
 if c.isnode(t):
  yield path,t
  yield from occurrences(t[0],path+(0,));yield from occurrences(t[1],path+(1,))
def setpath(t,path,x):
 if not path:return x
 a,b=t
 return(setpath(a,path[1:],x),b)if path[0]==0 else(a,setpath(b,path[1:],x))
def patched(t):
 r,idx,s=c.build(t);r[100,0]=0,True,213;r[100,1]=1,True,174;r[174,0]=0,True,28;r[174,1]=1,True,164
 return r,s
if __name__=='__main__':
 import sys,time
 t=c.read_grammar(sys.argv[1]);bc=sb(t);nseen=0;start=time.time();seen={t}
 for iteration in range(7):
  candidates=[]
  for path,x in occurrences(t):
   for y in rotations(x):
    z=setpath(t,path,y)
    if z in seen:continue
    seen.add(z);nseen+=1;zb=sb(z)
    if zb>=bc or bad(z):continue
    h,l,m,mi,first=attrs(z)
    if m>6 or mi>5:continue
    r,s=patched(z);low=len(s)-len(c.max_matching(c.opportunities_fast(r,s)))
    if low>62:continue
    ch=bestcompatible_all(r,s);eff=len(s)-len(ch)
    if eff<=62:candidates.append((zb,eff,z))
  if not candidates:break
  bc,eff,t=min(candidates,key=lambda x:x[:2]);name='scanner_local_'+str(bc);Path(name+'.grammar.json').write_text(json.dumps(encode(t),indent=2));print('BEST',bc,eff,'local_neighbors',nseen,'seconds',time.time()-start,flush=True)
 print('END',bc,'neighbors',nseen,'seconds',time.time()-start,flush=True)

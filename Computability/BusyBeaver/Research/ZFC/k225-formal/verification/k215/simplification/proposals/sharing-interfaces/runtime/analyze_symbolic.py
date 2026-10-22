"""Owned transcription of inspected symbolic rules; BoxLemmas assumed."""
if not __debug__:raise RuntimeError('Assertions must be enabled')
from types import SimpleNamespace
B=lambda b:('b',int(b))
U=lambda b,a,c:('r',int(b),a,c)
X=lambda kind='none',r=0:('x',kind,r)
SK=[51,36,25,48,32,33,22,55,60]
def table(p):
 t={}
 for ln in p.read_text().splitlines():
  if not ln or ln.startswith('#'):continue
  q,b,w,d,z=ln.split();t[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return t
def inc(pc):
 n=len(pc);v=(int(pc,2)if pc else 0)+1
 return(format(v%(2**n),'0'+str(n)+'b')if n else ''),int(v==2**n)
def strip(pc,b,k):
 if not k:return pc
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==b:
   k-=1
   if not k:return pc[:i]
 return ''
I=SimpleNamespace(table=table,inc=inc,strip=strip,PHY=(6,2,0,4,3,7,8,5,1))
def norm(seq,left=False):
 out=[]
 for t in seq:
  if t[0]=='b':t=U(t[1],0,1)
  if t[0]=='r'and t[2:]==(0,0):continue
  if out and t[0]=='r'and out[-1][:2]==t[:2]:
   b=out.pop();t=U(t[1],t[2]+b[2],t[3]+b[3])
  out.append(t)
 if left and out and out[-1][:2]==('r',0):out.pop()
 return tuple(out)
def key(s):q,on,l,r=s;return q,on,norm(l,True),norm(r)
def step(T,br,s):
 q,on,l,r=s;l=list(l);r=list(r)
 if on:
  if not l:return(q,False,(),(B(0),)+tuple(r)),False,'reorient'
  a=l.pop(0)
  if a[0]=='b':return(q,False,tuple(l),(a,)+tuple(r)),False,'reorient'
  assert a[0]=='r'
  _,b,c,n=a;w,d,z=T[q,b]
  if d==-1 and z==q:return(q,True,tuple(l),(U(w,c,n),)+tuple(r)),False,'scan'
  assert n>0 or c==0
  return(q,True,((B(b),U(b,c,n-1))if n else())+tuple(l),tuple(r)),False,'peel'
 assert r
 a=r.pop(0)
 if a[0]=='b':
  w,d,z=T[q,a[1]]
  return((z,False,(B(w),)+tuple(l),tuple(r))if d==1 else(z,True,tuple(l),(B(w),)+tuple(r))),True,'literal'
 if a[0]=='r':
  _,b,c,n=a;w,d,z=T[q,b]
  if d==1 and z==q:return(q,False,(U(w,c,n),)+tuple(l),tuple(r)),False,'scan'
  assert n>0 or c==0
  return(q,False,tuple(l),((B(b),U(b,c,n-1))if n else())+tuple(r)),False,'peel'
 assert not r
 _,kind,i=a;ans=None
 if kind=='none'and q in SK:
  j=SK.index(q);ans=(1 if j==0 else 3,X('mark',j),False)
 elif kind=='mark'and i<9:
  if q==64:ans=(40,X('inc',i),False)
  elif q==0 and br is not None and br[0]==i:ans=(97,X(),False)if br[1]else(40,X('dec',i),True)
 if ans:
  z,x,e=ans;return(z,True,((B(1),)if e else())+tuple(l),(x,)),False,'oracle'
 assert T[q,0][:2]==(0,-1)
 return(T[q,0][2],True,tuple(l),(a,)),True,'boxedge'

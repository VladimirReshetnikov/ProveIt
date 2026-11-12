"""Untrusted generator for scalar packet examples in the restricted checker."""
from pathlib import Path
import json, importlib.util
ROOT=Path(__file__).parent
spec=importlib.util.spec_from_file_location('atoms', ROOT/'checker.py')
K=importlib.util.module_from_spec(spec);spec.loader.exec_module(K)
S=lambda a:[0,a]
I=lambda n,a,h:[n,a,h]

def refl(a):return (a,a,['r',a])
def ev(p,q):
 s,t,pp=p;b,r,qp=q
 if b!=s:
  c,a,h=b
  if c!=0:a,t=[c[1],a,h],K.opening(h,t)
  assert a==s
 return r,t,(['v',pp,['v',qp,['r',[0,s,0]]]] if b==s else ['v',pp,qp])
def sym(p):return ev(refl(p[0]),p)
def trans(p,q):
 assert p[1]==q[0],(p[:2],q[:2])
 return ev(q,sym(p))
def zero(a,h):return ev(refl(a),refl(I(0,a,h)))
def succ(n,a,h):return ev(refl(I(n,a,h)),refl(I(S(n),a,h)))
def cong(p,h):
 s,t,_=p;z=zero(s,h);zt=trans(z,p)
 whs=ev(z,refl(I(S(0),s,h)))
 return ev(zt,whs)
def hole(a,path,depth=0):
 if not path:return depth+1
 j=path[0];b=list(a)
 b[j]=hole(a[j],path[1:],depth+(len(a)==3 and j==2))
 return b

def first_redex(a,path=()):
 if type(a)is int:return None
 if len(a)==3 and (a[0]==0 or type(a[0])is list and len(a[0])==2):return path
 for i,b in enumerate(a):
  p=first_redex(b,path+(i,))
  if p is not None:return p
 return None

def node(a,path):
 for i in path:a=a[i]
 return a

def normalize(a):
 result=refl(a)
 for _ in range(100):
  path=first_redex(result[1])
  if path is None:return result
  n,b,h=node(result[1],path)
  p=zero(b,h) if n==0 else succ(n[1],b,h)
  if path:p=cong(p,hole(result[1],path))
  result=trans(result,p)
 raise AssertionError('unexpected normalization length')

def eq_normal(s,t):
 a,b=normalize(s),normalize(t)
 assert a[1]==b[1],(a[1],b[1])
 return trans(a,sym(b))
# Named source notation to eliminate hand-calculated de Bruijn offsets.
def v(n):return ('v',n)
def sc(a):return ('s',a)
def it(n,a,u,h):return ('i',n,a,u,h)
def sel(n,a,b):return it(n,a,'unused',b)
def eq(s,t):return ('eq',s,t)
def d(x,y,b):return ('d',x,y,b)
def compile(a,free=None,bound=()):
 free={} if free is None else free
 if a==0:return 0
 tag,*xs=a
 if tag=='v':return bound.index(xs[0])+1 if xs[0] in bound else free[xs[0]]
 if tag=='s':return S(compile(xs[0],free,bound))
 if tag=='i':
  n,b,u,h=xs
  return I(compile(n,free,bound),compile(b,free,bound),compile(h,free,(u,)+bound))
 if tag=='eq':return [compile(x,free,bound) for x in xs]
 if tag=='d':
  x,y,b=xs
  return [compile(b,free,(y,x)+bound)]
 raise AssertionError(tag)
def packet(n):return d('x','y',eq(sel(v('y'),0,sel(n,0,sc(v('x')))),sel(v('y'),0,n)))
def intro_packet(n,scope,witness,free=None):
 goal=compile(packet(n),free)
 body=K.opening(goal[0],witness,1)
 target=K.opening(body,S(-scope-1))
 p=eq_normal(*target)
 assert p[:2]==tuple(target)
 assert witness in (0,-scope)
 proof=['i',goal,int(witness!=0),p[2]]
 assert K.derive(proof,[],scope)==goal
 return goal,proof

def main():
 t0,p0=intro_packet(0,0,0)
 outer=compile(d('dummy','n',packet(v('n'))))
 stepgoal,stepp=intro_packet(sc(v('n')),1,-1,{'n':-1})
 outerp=['i',outer,0,stepp]
 assert K.verify({'goal':outer,'proof':outerp})
 cases={'packet_zero':{'goal':t0,'proof':p0},'packet_closure':{'goal':outer,'proof':outerp}}
 for k in (1,2):
  n=0
  for _ in range(k):n=sc(n)
  goal=compile(packet(n))
  _,p0fresh=intro_packet(0,1,0)
  branch=['u',0,compile(n),p0fresh]
  proof=['e',goal,outerp,branch]
  payload={'goal':goal,'proof':proof}
  assert K.verify(payload)
  cases[f'packet_numeral_{k}']=payload
 out=ROOT/'fixtures/generated';out.mkdir(parents=True,exist_ok=True)
 for name,payload in cases.items():(out/f'{name}.json').write_text(json.dumps(payload,indent=2)+'\n')
 print(json.dumps({k:len(json.dumps(v)) for k,v in cases.items()},indent=2))
if __name__=='__main__':main()

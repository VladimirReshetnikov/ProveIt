"""Exact BR Schur determinant diagnostics; selected runs do not prove all cases."""
from pathlib import Path
from itertools import permutations,combinations_with_replacement,product
from functools import lru_cache
from collections import Counter
from math import lcm,comb
import json,time,sys,hashlib
import sympy as s
from br_support_core import endpoint,minor_count as cnt,BASES,translate
ROOT=Path(__file__).resolve().parent
n=s.Symbol('n',positive=True);p1,p2,m1,m2,t1,t2,q=s.symbols('p1 p2 m1 m2 t1 t2 q');xs=s.symbols('N1:8')
def image(mask,perm):return sum(((mask>>i)&1)<<perm[i] for i in range(3))
def profiles():
 out=[]
 for U,types in ((1,(0,2,4,6)),(3,(0,1,4,5)),(7,(0,1,2,4,3))):
  group=[(0,1,2)] if U==3 else ([(0,1,2),(0,2,1)] if U==1 else list(permutations(range(3))))
  reps=set()
  for J in types:
   for A,B in combinations_with_replacement(types,2):
    orbit=[]
    for perm in group:
     mapped=[3 if U==7 and v.bit_count()>=2 else image(v,perm) for v in (J,A,B)]
     orbit.append((mapped[0],*sorted(mapped[1:])))
    reps.add(min(orbit))
  out.extend((U,*x) for x in sorted(reps))
 return out
@lru_cache(None)
def rdata(U,J):
 rt={1:(2,4,6),3:(1,4,5),7:(1,2,4,3)}[U]
 E=n*U.bit_count()+cnt((J,U))
 rr=s.Matrix([n*cnt((U,S))+cnt((J,U,S)) for S in rt])
 ar=s.Matrix(len(rt),len(rt),lambda i,j:3*rr[i]*rr[j]-4*E*n*cnt((U,rt[i],rt[j])))
 det=s.factor(ar.det());iv=ar.inv().applyfunc(s.cancel)
 return rt,E,rr,iv,str(det)
@lru_cache(None)
def data(U,J,C,i):
 p,m,t=(p1,m1,t1) if i==1 else (p2,m2,t2)
 rt,E,rr,iv,_=rdata(U,J)
 x=p*U.bit_count()+n*cnt((C,U))+m*cnt((J,U))-t*(cnt((J,U))+cnt((C,U))-cnt((J|C,U)))+cnt((J,C,U))
 y=s.Matrix([p*cnt((U,S))+n*cnt((C,U,S))+m*cnt((J,U,S))-t*(cnt((J,U,S))+cnt((C,U,S))-cnt((J|C,U,S))) for S in rt])
 return x,3*x*rr-4*E*y

def build(U,J,C1,C2):
 rt,E,rr,iv,rdet=rdata(U,J);x,u=data(U,J,C1,1);xx,v=data(U,J,C2,2)
 a=s.cancel((3*x*x-(u.T*iv*u)[0])/(4*E));b=s.cancel((3*xx*xx-(v.T*iv*v)[0])/(4*E));c=s.cancel((3*x*xx-4*E*q-(u.T*iv*v)[0])/(4*E))
 den=s.lcm([s.denom(z) for z in (a,b,c)])
 if any(z<0 for z in s.Poly(den,n).all_coeffs()):raise RuntimeError(('denominator sign',U,J,den))
 N={i:xs[i-1] for i in range(1,8)};nv=sum(N[i] for i in N if i&1);mv1=sum(N[i] for i in N if i&2);mv2=sum(N[i] for i in N if i&4);tv1=N[3]+N[7];tv2=N[5]+N[7]
 sub={n:nv,m1:mv1,m2:mv2,t1:tv1,t2:tv2,p1:nv*mv1-tv1*(tv1+1)/2,p2:nv*mv2-tv2*(tv2+1)/2,q:endpoint((J,C1,C2),(('B',0),('B',1),('B',2),('R',U)))}
 arr=[s.Poly(s.expand(s.cancel(z*den).subs(sub)),xs) for z in (a,b,c)]
 target=arr[0]*arr[1]-arr[2]*arr[2];mult=lcm(*(int(s.denom(v)) for v in target.coeffs()))
 poly={e:int(c*mult) for e,c in target.terms() if c}
 return poly,{'R_determinant':rdet,'denominator':str(s.factor(den)),'multiplier':mult,'degree':target.total_degree(),'base_terms':len(poly)}
def run(core):
 start=time.time();poly,meta=build(*core);records=[];negative=None
 for basis in BASES:
  shifted=translate(poly,basis);bad=[(e,c) for e,c in shifted.items() if c<0]
  text=json.dumps([[list(e),c] for e,c in sorted(shifted.items())],separators=(',',':'))
  records.append({'basis':basis,'terms':len(shifted),'minimum':min(shifted.values(),default=0),'negative':len(bad),'sha256':hashlib.sha256(text.encode()).hexdigest()})
  if bad:negative={'basis':basis,'first_negative':bad[:5]};break
 out={'core':core,**meta,'basis_count':len(records),'negative':negative,'records':records,'seconds':time.time()-start}
 (ROOT/('br_%s_%s_%s_%s.json'%core)).write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k!='records'}),flush=True);return out
if __name__=='__main__':
 if len(sys.argv)==5:run(tuple(map(int,sys.argv[1:])))
 else:
  allp=profiles();print('PROFILES',Counter(x[0] for x in allp),flush=True)
  for p in allp:
   if not (ROOT/('br_%s_%s_%s_%s.json'%p)).exists():
    result=run(p)
    if result['negative']:break

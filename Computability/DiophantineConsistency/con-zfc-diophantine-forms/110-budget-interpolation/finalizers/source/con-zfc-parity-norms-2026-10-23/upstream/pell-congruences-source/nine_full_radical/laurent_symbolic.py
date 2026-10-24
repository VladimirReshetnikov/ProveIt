"""Exact sparse Laurent expansion; exploratory construction, not a proof claim."""
from fractions import Fraction as Q
from collections import defaultdict
import json, pathlib, math, time
R=pathlib.Path(__file__).resolve().parent
def require(condition,message):
 if not condition:raise ValueError(message)
def add(a,b,fac=1):
 c=dict(a)
 for m,v in b.items():
  c[m]=c.get(m,0)+fac*v
  if not c[m]:del c[m]
 return c
def mul(a,b):
 c=defaultdict(int)
 for m,v in a.items():
  for n,w in b.items():c[tuple(x+y for x,y in zip(m,n))]+=v*w
 return {m:v for m,v in c.items()if v}
def scale(a,n=1,shift=None):return {tuple(x+y for x,y in zip(m,shift)) if shift else m:v*n for m,v in a.items()if v*n}
def const(n):return {(0,0,0,0):n}if n else {}
def mono(m,c=1):return {m:c}
def dump(p):return [[list(m),str(v)]for m,v in sorted(p.items())]
def expr_setup():
 A=mono((1,0,0,0));C=mono((0,1,0,0));i=mono((0,0,1,0));t=mono((0,0,0,1));one=const(1)
 sq=lambda p:mul(p,p)
 D=add(mul(add(sq(A),one,-1),sq(C)),one);e=mul(mul(i,add(scale(A,4),const(-5))),C)
 F=add(mul(mul(add(D,one,-1),sq(e)),sq(D)),one)
 L=add(add(mul(C,D),one),A,-1);G=add(mul(F,L),A);H=add(mul(F,t),C)
 DF=mul(D,F);I=add(mul(add(sq(G),one,-1),sq(H)),one)
 return A,C,i,t,D,e,F,L,G,H,DF,I
def series_df(DF):
 p=defaultdict(dict)
 for (a,c,i,t),v in DF.items():
  require(t==0,'unexpected t dependence in DF');p[a][(c,i)]=Q(v)
 out={5:{(5,1):Q(4)}}
 for k in range(4,-20,-1):
  r=p.get(5+k,{})
  for j,cj in out.items():
   l=5+k-j
   if l in out:r=add(r,mul(cj,out[l]),-1)
  out[k]=scale(r,Q(1,8),(-5,-1))
  print('sqrt coefficient',k,len(out[k]),flush=True)
 return out
def main():
 A,C,i,t,D,e,F,L,G,H,DF,I=expr_setup();S=series_df(DF)
 GH=mul(G,H);M={}
 for (a,c,i,t),v in GH.items():
  for k,terms in S.items():
   if a+k<0:continue
   for (cx,ix),u in terms.items():M=add(M,{(a+k,c+cx,i+ix,t):v*u})
 # Inverse L = (C^3 A^2 - A + 1+C-C^3)^-1.
 inv={-2:{(-3,0):Q(1)}}
 b={(-3,0):Q(-1)};cc={(-3,0):Q(1),(-2,0):Q(1),(0,0):Q(-1)}
 for k in range(-3,-7,-1):
  r=add(mul(b,inv.get(k+1,{})),mul(cc,inv.get(k+2,{})))
  inv[k]=scale(r,-1)
 for k,terms in S.items():
  for h,its in inv.items():
   if k+h<0:continue
   for (cx,ix),u in mul(terms,its).items():M=add(M,{(k+h,cx,ix,1):-u/2})
 print('M terms',len(M),flush=True)
 sh=[max(0,-min(m[j]for m in M))for j in range(4)]
 den=math.lcm(*(v.denominator for v in M.values()))
 require(sh[0]==sh[3]==0,'unexpected A or t denominator')
 T=scale(M,den,sh);require(all(v.denominator==1 for v in T.values()),'denominators not cleared');T={m:int(v)for m,v in T.items()}
 rad=mul(DF,I);scaledrad=scale(rad,den*den,[2*x for x in sh]);defect=add(mul(T,T),scaledrad,-1)
 print('scale',den,sh,'T',len(T),'rad',len(rad),'defect',len(defect),'Adegree',max(m[0]for m in defect),flush=True)
 result={'scale_integer':den,'scale_powers':sh,'majorant':dump(T),'defect':dump(defect),'radicand':dump(rad)}
 (R/'laurent_candidate.json').write_text(json.dumps(result))
 print('written',flush=True)
if __name__=='__main__':main()

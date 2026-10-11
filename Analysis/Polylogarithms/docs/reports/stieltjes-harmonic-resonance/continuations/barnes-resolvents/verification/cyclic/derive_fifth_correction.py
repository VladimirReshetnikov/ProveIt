"""Exact Taylor extraction of the normalized elementary fifth-jet correction.

Imported by verify_fifth_exact.py. Direct execution prints the correction
and writes generated_results/fifth_correction.txt beside this script.
"""
import sympy as s
from pathlib import Path
A,B,C,t=s.symbols('A B C t')
g,h2,h3,h4,h5=s.symbols('g h2 h3 h4 h5')
z=s.symbols('z0:6'); y=s.symbols('y0:6')
variables=(A,B,C)
def D(poly): return s.Poly(s.expand(poly),*variables).as_dict()
def P(d): return s.Add(*[c*A**i*B**j*C**k for (i,j,k),c in d.items()])
def add(*ds):
 out={}
 for d in ds:
  for k,v in d.items(): out[k]=out.get(k,0)+v
 return out
def scale(d,c): return {k:c*v for k,v in d.items()}
def mul(*ds,degree=4):
 out={(0,0,0):s.S.One}
 for d in ds:
  new={}
  for k,v in out.items():
   for l,w in d.items():
    kl=tuple(k[i]+l[i] for i in range(3))
    if sum(kl)<=degree:new[kl]=new.get(kl,0)+v*w
  out=new
 return out
def uni(coeffs,index):
 out={}
 for j,c in enumerate(coeffs):
  e=[0,0,0];e[index]=j;out[tuple(e)]=c
 return out
Gminus=[1,g,(g*g+h2)/2,(g**3+3*g*h2+2*h3)/6,(g**4+6*g*g*h2+3*h2*h2+8*g*h3+6*h4)/24,(g**5+10*g**3*h2+15*g*h2*h2+20*g*g*h3+20*h2*h3+30*g*h4+24*h5)/120]
Grecip=[c.xreplace({h2:-h2,h4:-h4}) if hasattr(c,'xreplace') else c for c in Gminus]
GA=uni(Gminus,0);GB=uni(Gminus,1);GC=uni(Grecip,2)
ZA=uni([z[j]/s.factorial(j) for j in range(6)],0);ZB=uni([z[j]/s.factorial(j) for j in range(6)],1)
YA=uni([y[j]/s.factorial(j) for j in range(6)],0);YB=uni([y[j]/s.factorial(j) for j in range(6)],1)
Dsum=D(-sum((A+B+C)**k/s.Integer(2)**(k+1) for k in range(5)))
Dac=D(-sum((A+C)**k for k in range(5)));Dbc=D(-sum((B+C)**k for k in range(5)))
def divlin(d,den):
 pp=s.expand(P(d)-1)
 qq,rr=s.div(pp,den,*variables)
 assert s.expand(rr)==0,rr
 return D(qq)
qa=divlin(mul(GA,GC,degree=5),A+C)
qb=divlin(mul(GB,GC,degree=5),B+C)
qc=divlin(GC,C)
E=add(mul(GC,GA,GB,Dsum),mul(GC,GA,ZB,Dac),mul(GC,GB,ZA,Dbc),mul(ZA,ZB,qc),scale(mul(YB,qa),-1),scale(mul(YA,qb),-1))
xi=s.expand(E.get((2,2,0),0)+2*E.get((2,1,1),0)).subs({z[0]:-s.Rational(1,2),y[0]:-s.Rational(1,12)}).expand()
if __name__ == '__main__':
 print('correction =',xi)
 print('LATEX:',s.latex(xi))
 output=Path(__file__).resolve().parent/'generated_results'
 output.mkdir(exist_ok=True)
 (output/'fifth_correction.txt').write_text(str(xi)+'\n'+s.latex(xi)+'\n',encoding='utf-8')

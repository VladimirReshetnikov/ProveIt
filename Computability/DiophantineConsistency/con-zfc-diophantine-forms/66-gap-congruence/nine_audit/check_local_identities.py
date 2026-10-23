"""Exact polynomial checks of the margin-first and refined-majorant bridges."""
import sympy as s
from pathlib import Path
import json
A,C,D,k=s.symbols('A C D k');L=C*D+1-A;F=1+k*k*D*D*(D-1);G=A+F*L
Ns=2*G+L;N1=2*k*k*D*(D-1)*L+3*C;N2=2*k*k*(D-1)*L;N3=2*k*k*(L-C);N4=2*k*k*C
T6=k*((1024*D*D-512*D-128)*Ns-64*N1-40*N2-28*N3-21*N4)
t7=2048*D**7-1024*D**6-256*D**5-128*D**4-80*D**3-56*D**2-42*D-33
E7=14*k**3*(A-1)/D-9*k**3*C/D+9*k**3*(A-1)/D**2-33*k**3*C/D**2+33*k**3*(A-1)/D**3+k*((120*C+192-64*A)/D+(84*C+120-40*A)/D**2+(63*C+84-28*A)/D**3+(63-21*A)/D**4)+s.Rational(99,2)*k*C/D**4+s.Rational(33,2)*k*(3-A)/D**5
checks={}
def check(n,e):
 if s.cancel(e)!=0: raise RuntimeError(n)
 checks[n]=True
check('exact E7 rational identity',T6-k*t7*Ns/(2*D**5)-E7)
check('collected T6 identity',T6-k*(128*(8*D*D-4*D-1)*Ns-k*k*(16*((8*D*D-4*D-1)+D)-8)*L+C*(14*k*k-192)))
check('first quotient division',(4*A-5)**3-(A+1)*(64*A*A-304*A+604)+729)
check('second quotient division',(4*A-5)**3-(A*A-1)*(64*A-240)-(364*A-365))
t,K,g,Y,W,J,n,Q,V0,V1,Om,x,y,Th=s.symbols('t K g Y W J n Q V0 V1 Om x y Th')
m=K*K*(4*t-g)-16*t*(C-K*Y)**2
check('normalized margin',8*m-((K*K-4*(C-K*Y)**2)*32*t-8*g*K*K))
check('shifted positive E0',J*(n+W*W)+3*W*C-2*(W*W-1)-(J*n+(J-2)*W*W+3*W*C+2))
check('four real factors',s.prod(Th+e*Om*x+f*Om*y for e in [-1,1] for f in [-1,1])-((Th*Th-Om*Om*(x*x+y*y))**2-4*Om**4*x*x*y*y))
check('simple Pell defect',(k*(8*D*D-4*D-1))**2-64*D*F-((8*D+1)*k*k-64*D))
result={'status':'PASS','exact_identities':checks,'t7_negative_coefficient_sum':1024+256+128+80+56+42+33}
p=Path(__file__).resolve().parent/'LOCAL_IDENTITIES.json';p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

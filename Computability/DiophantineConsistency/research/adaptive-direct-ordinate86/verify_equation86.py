"""Exact polynomial check of the equation86 displayed factors against candidate.json.

The displayed TeX block is pinned below; its mathematical expressions are
independently evaluated as sparse integer polynomials, treating all thirteen
witnesses and four ports as indeterminates. The final product is checked
factor-by-factor, avoiding expansion of the complete polynomial.
"""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[1];C=D/'adaptive-direct-ordinate86/candidate.json';T=D.parent/'equation86.tex';j=json.loads(C.read_text());assert hashlib.sha256(C.read_bytes()).hexdigest()=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'
N=len(j['witnesses'])+len(j['fixed_numerals']);zero=(0,)*N
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 @staticmethod
 def coerce(x):return x if isinstance(x,P) else P({zero:x})
 def __add__(self,other):
  d=self.d.copy()
  for k,v in P.coerce(other).d.items():d[k]=d.get(k,0)+v
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,x):return self+(-P.coerce(x))
 def __rsub__(self,x):return P.coerce(x)-self
 def __mul__(self,other):
  d={}
  for a,x in self.d.items():
   for b,y in P.coerce(other).d.items():
    k=tuple(i+j for i,j in zip(a,b));d[k]=d.get(k,0)+x*y
  return P(d)
 __rmul__=__mul__
 def __pow__(self,n):
  r=P.coerce(1)
  for _ in range(n):r=r*self
  return r
 def __eq__(self,x):return self.d==P.coerce(x).d
names=j['witnesses']+j['fixed_numerals'];v={}
for idx,n in enumerate(names):
 e=list(zero);e[idx]=1;v[n]=P({tuple(e):1})
# Evaluate the candidate DAG through the four factors; its final three
# products and subtraction are checked structurally below.
g=dict(v)
for row in j['source']:
 name,op,a,b=row
 if name in ['g86','g87','g88','P13']:continue
 x=P.coerce(a) if isinstance(a,int) else g[a];y=P.coerce(b) if isinstance(b,int) else g[b]
 g[name]=x+y if op=='+' else x-y if op=='-' else x*y
J,F,alpha,f,i,T0,X,Y,r,eta,zeta,y,gamma=[v[n] for n in j['witnesses']];beta,K,mu,omega=[v[n] for n in j['fixed_numerals']]
b=beta*J;q=1+b;C0=q-F-alpha;U=Y*q**2;E=X*Y;k=eta+zeta;ell=E*Y*k;c=eta+Y*k;a=E+Y;H=3+4*a;Delta=H+a*a;B=X+a*c;M=q**3*b;W=C0*(X+K*q)-F*q
R=(alpha+(q-F)*b)*(q*q-1)+J*(mu+omega*q)
Z=M*(ell+k+r-k*W)+Y*b-W*q**3
Dstar=U*B+H*(U*gamma+E*q+R+1-k)
I=c*c*i;Q=Delta*(f*f-1);V=f*f*(T0*c-R)-c
A=1+Z*Z-M*M*(1+ell*(ell+k));L=1+Dstar*Dstar-U*U*(1+Delta*c*c);N0=y*y-Q*(y*y-V*V);S=1+I*I-Q
checks={'b':(b,g['qm']),'q':(q,g['q']),'C':(C0,g['C']),'U':(U,g['U']),'E':(E,g['E']),'k':(k,g['k']),'ell':(ell,g['ell']),'c':(c,g['c']),'a':(a,g['a']),'H':(H,g['H']),'Delta':(Delta,g['Delta']),'B':(B,g['b0']),'M':(M,g['M']),'W':(W,g['Bt']),'R':(R,g['R']),'Z':(Z,g['Z']),'D':(Dstar,g['Dstar']),'I':(I,g['I']),'Q':(Q,g['Q']),'V':(V,g['V']),'A':(A,g['F0']),'L':(L,g['F1']),'N':(N0,g['Fa']),'S':(S,g['Fs'])}
for name,(left,right) in checks.items():assert left==right,name
assert j['source'][-4:]==[['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
text=T.read_text();begin=text.index('% BEGIN VERIFIED DISPLAY\n');end=text.index('% END VERIFIED DISPLAY\n')+len('% END VERIFIED DISPLAY\n');assert text[begin:end]==(Path(__file__).resolve().parent/'equation86-display.tex').read_text()
# Re-parse the rendered ASCII circuit independently of the TeX generator.
rename={'r':'xi','i':'g','y':'upsilon','K0':'K','MC':'mu','MF':'omega','qm':'b','Bt':'W','b0':'L','Dstar':'D','G':'rankseed','F0':'first','F1':'main','Fa':'aux','Fs':'strong','P13':'P'}
def show(x):return rename.get(str(x),str(x)).replace('_',r'\_')
lines=[line for line in text.splitlines() if line[:1].isdigit() and '. ' in line and ' = ' in line and line.endswith(r'\\')]
assert len(lines)==86
for idx,(line,(name,op,a,b)) in enumerate(zip(lines,j['source']),1):
 assert line==f'{idx}. {show(name)} = {show(a)} {op} {show(b)}'+r'\\',(idx,line)
# Preserve the complete fixed-constant specification and decimal integer from
# the existing maintained page byte-for-byte, independently of the new gates.
old=(D.parent/'equation.tex').read_text();start=r'\textbf{The four fixed integers.}';last=r'\endgroup';ref=old[old.index(start):old.index(last,old.index(r'\textbf{The integer $\mathcal A$'))+len(last)];assert ref in text
print('PASS:',len(checks),'exact sparse polynomial identities; exact final product wiring; pinned TeX display block; 86 parsed circuit gates; fixed constants copied exactly')

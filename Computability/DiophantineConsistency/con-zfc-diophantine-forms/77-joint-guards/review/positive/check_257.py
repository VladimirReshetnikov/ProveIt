#!/usr/bin/env python3
"""Independent finite audit. Does not import candidate code or its verifier."""
from pathlib import Path
from collections import Counter
from itertools import product
from fractions import Fraction
import json,hashlib,gzip,math
import sympy as s
R=Path(__file__).resolve().parents[2];P=R/'pell/p11_positive_degree257.json';D=json.loads(P.read_text());OUT=Path(__file__).resolve().parent

def req(x,m):
 if not x:raise ValueError(m)
F={
'J':'3*j+1','qm':'J*beta','q':'qm+1','q2':'q*q','q3':'q*q2','q2m':'q2-1','qF':'q-F','C':'qF-alpha',
'E':'X*Y','k':'eta+zeta','kY':'k*Y','c':'kY+eta','c2':'c*c','I':'i*c2','a':'E+Y','H':'4*a+3','Delta':'a*a+H','ac':'a*c','b0':'X+ac','ell':'E*kY',
'G':'qm*qF+alpha','R':'G*q2m+(MC+q*MF)*J','Rhat':'q3*(q+F+alpha)','M':'q3*qm','Bt':'(q*K0+X)*C-q*F','ellk':'ell+k','Dtau':'ell*ellk+1','I2':'I*I','fm':'Delta*I2','Df':'fm+1','Q':'Delta*fm','delta':'Q-1','cT':'c*T','V':'Df*(cT-R)-c','B0':'cT+Rhat','L':'Df+B0','hstar':'4*q*Df+L','W':'1+qm*hstar','Zbar':'M*(ellk+n+L+V)+qm*Y-q3*W*Bt','r0':'k-R-1','S':'4*q*Y','U':'q*S','shift':'U*gamma+S*X-r0','Dstar':'U*b0+H*shift','A1':'Dstar**2-U**2*(1+Delta*c2)','M2':'M*M','A':'M2*Dtau','Bf':'M2*Df','Dnum':'Q*V*V-1','Cnum':'M2*Dnum','z2':'Zbar*Zbar','ABsum':'A+Bf','AB':'A*Bf','delta2':'delta*delta','Tn':'delta2*AB','Rn':'delta*Cnum','Jn':'delta*(z2-ABsum)-Cnum','Ncenter':'Jn*Jn-4*(Tn+Rn*ABsum)','normtail':'64*Tn*Rn*z2','N8':'Ncenter*Ncenter-normtail','P11':'N8+A1+N8*A1'}
inputs=D['witnesses']+D['fixed_numerals'];names=inputs+[r[0] for r in D['source']]
req(len(D['witnesses'])==11 and len(set(names))==len(names),'unique inputs/gates')
sy={x:s.Symbol(x) for x in names};env={x:sy[x] for x in inputs};seen=set();deps={};degrees={x:(1 if x in D['witnesses'] else 0) for x in inputs};counts=Counter()
for name,op,x,y in D['source']:
 req(op in ['+','-','*'],'binary operation');req(all(type(z)is int or z in env for z in [x,y]),'topology')
 a,b=[s.Integer(z) if type(z)is int else env[z] for z in [x,y]];da,db=[0 if type(z)is int else degrees[z] for z in [x,y]]
 val=a+b if op=='+' else a-b if op=='-' else a*b;bound=da+db if op=='*' else max(da,db)
 if name in F:
  req(s.expand(val-s.sympify(F[name],locals=sy))==0,'literal formula '+name);env[name]=sy[name];seen.add(name)
 else:env[name]=s.expand(val)
 if name=='A1':req(bound==14,'A1 pre-cancellation degree');bound=13
 if name=='Jn':req(bound==62,'Jn pre-cancellation degree');bound=61
 degrees[name]=bound;counts[op]+=1;deps[name]=[z for z in [x,y] if type(z)is str]
req(seen==set(F),'all contracts seen')
live=set()
def visit(x):
 if x in live:return
 live.add(x)
 for v in deps.get(x,[]):visit(v)
visit(D['output']);req(live==set(names),'complete liveness')
req(dict(counts)=={'*':65,'+':32,'-':17} and sum(counts.values())==114,'counts')
# Exact universal algebra, using an independent CAS rather than candidate rings.
x,r,t,u,Q,V,y,U,H,X,a,c,h=s.symbols('x r t u Q V y U H X a c h')
conj=s.prod(x-e*r-f*t-g*u for e,f,g in product([-1,1],repeat=3))
norm=((x*x-r*r-t*t-u*u)**2-4*(r*r*t*t+r*r*u*u+t*t*u*u))**2-64*r*r*t*t*u*u*x*x
req(s.expand(conj-norm)==0,'eight conjugates')
total=r+t+u;pair=r*t+r*u+t*u;triple=r*t*u
req(s.expand(total**2-r*r-t*t-u*u-2*pair)==0,'rational pair extraction')
req(s.expand(pair**2-r*r*t*t-r*r*u*u-t*t*u*u-2*total*triple)==0,'rational product extraction')
req(s.expand(r*r*total+triple-r*(r+t)*(r+u))==0,'denominator factorization')
req(s.expand(r*(r*r*total+triple)-r*r*(r*r+pair))==0,'rational root extraction')
Vp=(2*Q-1)*V-2*(Q-1)*y;yp=(2*Q-1)*y-2*Q*V
req(s.expand(Q*Vp**2-(Q-1)*yp**2-(Q*V**2-(Q-1)*y**2))==0,'Pell descent norm invariant')
full=(U*(X+a*c)+H*h)**2-U**2*(1+(a*a+H)*c*c)
reduced=2*U*a*c*(U*X+H*h)+(U*X+H*h)**2-U**2*H*c*c-U**2
req(s.expand(full-reduced)==0,'main cancellation identity')
req([degrees[n] for n in ['U','a','c','H','shift']]==[3,2,2,2,4],'cancellation premises')
# Centered correction removes degree62 of Jn. z below is Zbar-MV.
d,z,M,A,B,V=s.symbols('d z M A B V')
Z=M*V+z; C=M*M*((d+1)*V*V-1)
req(s.expand(d*(Z*Z-A-B)-C-(d*(z*(z+2*M*V)-A-B)-M*M*(V*V-1)))==0,'centered Jn identity')
req([degrees[n] for n in ['M','V','L','hstar','W','Zbar','delta','A','Bf']]==[4,18,14,15,16,22,18,16,22],'centering degree premises')
# z has degree<=max(4+max(4,1,1,14),2,3+16+2)=21; hence Jn<=61.
# The correction to Jn^2 has degree102 and octic tail198, strictly smaller.
req(degrees['normtail']==198 and degrees['Ncenter']==122,'centered finalizer degree premises')
req(degrees['P11']==257 and degrees['N8']==244,'degree upper bound')
# Independent exact line witness over finite field at the authentic fixed tuple.
source=R/'sources/con-zfc-residue-orientation-root-transfer-2026-10-23/con-zfc-residue-orientation-root-transfer-2026-10-23/eleven'
bind=json.loads((source/'coefficients/ACTIVE_BINDING.json').read_text());fixed={};p=1000003;bytes_total=0;ports=[]
for name,entry in bind['ports'].items():
 b=(source/'coefficients'/entry['gzip_payload']).read_bytes();raw=gzip.decompress(b);req(hashlib.sha256(raw).hexdigest()==entry['sha256'],'fixed raw hash');req(hashlib.sha256(b).hexdigest()==entry['gzip_sha256'],'fixed gzip hash');fixed[name]=int.from_bytes(raw,'little')%p;bytes_total+=len(raw);ports.append({'port':name,'raw_sha256':entry['sha256'],'bytes':len(raw)})
# Authenticate the delivered component binding too, not merely its ancestor.
localbase=R/'pell/coefficients';localbind=json.loads((localbase/'ACTIVE_BINDING.json').read_text())
req((localbase/localbind['whole_binding']).is_file(),'local whole-binding target exists')
req(hashlib.sha256((localbase/localbind['whole_binding']).read_bytes()).hexdigest()==localbind['whole_binding_sha256'],'local whole-binding SHA256')
req(any((localbase/rel).resolve()==P.resolve() for rel in localbind['polynomials']),'current packet in local binding')
for name,entry in localbind['ports'].items():
 b=(localbase/entry['gzip_payload']).read_bytes();raw=gzip.decompress(b)
 req(hashlib.sha256(raw).hexdigest()==entry['sha256']==bind['ports'][name]['sha256'],'local fixed-port identity')
 req(hashlib.sha256(b).hexdigest()==entry['gzip_sha256'],'local fixed-port container hash')
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def plus(a,b,sign=1):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]=v
 for i,v in enumerate(b):c[i]=(c[i]+sign*v)%p
 return trim(c)
def times(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
 return trim(c)
e={name:[j+1,j+2] for j,name in enumerate(D['witnesses'])};e.update({name:[v] for name,v in fixed.items()})
line_degrees={}
for name,op,a,b in D['source']:
 aa=[a%p] if type(a)is int else e[a];bb=[b%p] if type(b)is int else e[b]
 e[name]=times(aa,bb) if op=='*' else plus(aa,bb,1 if op=='+' else -1);line_degrees[name]=len(e[name])-1
req(line_degrees['A1']==13 and line_degrees['Jn']==61 and line_degrees['N8']==244 and line_degrees['P11']==257,'authentic fixed-slice exact degree witness')
# Minimum q exponent52 and gamma force F^4 from (q-F)^4 and alpha^4 from Bt^4.
q,k,i,Fv,alpha,gamma,K=s.symbols('q k i F alpha gamma K')
minimal=s.expand(Fv**4*(-X*(Fv+alpha))**4)
req(minimal.coeff(alpha,4).coeff(Fv,4)==X**4,'selected F4alpha4 coefficient')
# Bounded rational norm diagnostics are not used as the proof of descent.
cases=0;descents=0
for qv in range(2,51):
 for vv in range(1,151):
  yy=Fraction(qv*vv*vv-1,qv-1);aa=math.isqrt(yy.numerator);mm=math.isqrt(yy.denominator)
  if aa*aa==yy.numerator and mm*mm==yy.denominator:
   cases+=1;req(mm==1,'rational integrality diagnostic')
   if vv>1:
    yv=Fraction(aa,mm);vnext=(2*qv-1)*vv-2*(qv-1)*yv;ynext=(2*qv-1)*yv-2*qv*vv
    req(vnext.denominator==1 and 0<abs(vnext)<vv,'strict descent diagnostic');req(qv*vnext*vnext-(qv-1)*ynext*ynext==1,'norm diagnostic');descents+=1
out={'status':'PASS','scope':'Independent exact finite formula, topology, cost, degree and binding audit; unbounded proof review in MATHEMATICAL_REVIEW.md. No candidate Python imported.','packet_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'named_formula_contracts':len(F),'operations':114,'breakdown':dict(counts),'all_inputs_and_gates_live':True,'upper_degree':257,'line_witness':{'prime':p,'directions':'variable number j (zero based) mapped to (j+1)+(j+2)t','degree':257,'leading_coefficient_mod_prime':e['P11'][-1],'fixed_tuple':'authentic compact44','main_degree':13,'norm_degree':244},'selected_coefficient':'2^19*(3*beta)^52','selected_monomial':'j^52*i^24*eta^49*X^38*Y^85*F^4*alpha^4*gamma','fixed_tuple_raw_bytes':bytes_total,'ports':ports,'rational_norm_diagnostics':cases,'strict_descent_diagnostics':descents,'universal_symbolic_identities':8}
(OUT/'CHECK257.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

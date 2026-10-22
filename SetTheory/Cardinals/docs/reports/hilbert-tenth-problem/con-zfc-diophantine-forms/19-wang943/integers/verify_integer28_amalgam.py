"""Independent checks of the normalized amalgam, using standard-library integer arithmetic."""
import json,hashlib,random
from pathlib import Path
H=Path(__file__).resolve().parent;p=json.loads((H/'integer28_normalized_amalgam128_degree258.json').read_text());rows=p['source'];known=set(p['witnesses']+p['fixed_numerals'])
for n,op,a,b in rows:
 assert n not in known and op in ('+','-','*')
 assert isinstance(a,int) or a in known
 assert isinstance(b,int) or b in known
 known.add(n)
live={p['output']}
for n,op,a,b in rows[::-1]:
 if n in live:
  live.update(x for x in [a,b] if isinstance(x,str))
assert all(n in live for n,*_ in rows) and set(p['witnesses']+p['fixed_numerals'])<=live
assert len(rows)==128 and len(p['witnesses'])==28

def run(v):
 v=v.copy()
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def formula(v):
 J,F,al,z,s,et,ze=[v[x] for x in p['positive_ports']];f,h,i,T,w,g,t=[v[x] for x in ['f','h','i','T','w','gamma','t']]
 q=v['beta']*J+1;X=w*q;Y=s*q**3;E=X*Y;k=et+ze;c=k*Y+et;a=E+Y;Hh=4*a+3;De=a*a+Hh;L=E*k*Y
 R=((q-1)*(q-F)+al)*(q*q-1)+(v['MC']+q*v['MF'])*J
 N1=(X+g*Hh)**2+2*a*c*(X+g*Hh)-Hh*c*c;Nk=k-h*E-R;Nt=(v['K0']+w)*(q-F-al)+q-F-z*(q-1)
 Ns=f*f-De*i*i*c**4;K=De*(f*f-1);A=1+L*(L+k);V=c*(T*f-1)-R*f*f;d=K-1;e=K*V*V-1;u=d*(t*t+A)-e
 res=u*u-4*d*d*t*t*A
 return N1*Nk*Nt*Ns*(1+res)-1
rng=random.Random(20261022)
for _ in range(150):
 v={x:rng.randrange(-3,4) for x in p['witnesses']};v.update({x:rng.randrange(2,9) for x in p['fixed_numerals']});v=run(v)
 assert v[p['output']]==formula(v)

# Exact identities for restoring tau and y, using rational arithmetic in checks.
from fractions import Fraction
for _ in range(300):
 tau,y,d=[rng.randrange(-20,21) for _ in range(3)];t=tau+y;A=tau*tau;e=d*y*y;u=d*(t*t+A)-e
 assert u==2*d*t*tau and u*u==4*d*d*t*t*A
 if d*t:
  assert Fraction(u,2*d*t)==tau and t-Fraction(u,2*d*t)==y

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,P,sgn=1):
 r=[0]*max(len(a),len(b))
 for j,x in enumerate(a):r[j]=x
 for j,x in enumerate(b):r[j]=(r[j]+sgn*x)%P
 return trim(r)

def mul(a,b,P):
 r=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):r[j+k]=(r[j+k]+x*y)%P
 return trim(r)

def line(P,beta,slope):
 active={'J_positive_a','h','gamma','f','i_integer','eta_positive_a','w_integer','s_positive_a'}
 v={x:([0,1] if x in active else [0]) for x in p['witnesses']};v['z_positive_a']=[0,slope]
 v.update({x:[beta if x=='beta' else 7] for x in p['fixed_numerals']})
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else [a%P];b=v[b] if isinstance(b,str) else [b%P]
  v[n]=mul(a,b,P) if op=='*' else add(a,b,P,1 if op=='+' else -1)
 return v[p['output']]
cert=[]
for P,beta in [(1000003,3),(1000033,5)]:
 a=line(P,beta,2);b=line(P,beta,0);c=line(P,beta,1);delta=add(c,b,P,-1)
 assert len(a)-1==258 and a[-1]==(-96*pow(beta,80,P))%P!=0
 assert len(delta)-1==258 and delta[-1]==(-32*pow(beta,80,P))%P
 cert.append({'prime':P,'beta':beta,'degree':258,'top_coefficient':a[-1],'isolated_coefficient':delta[-1]})
receipt={'status':'PASS','variables':28,'operations':128,'multiplications':66,'additions_subtractions':62,'exact_degree':258,
'all_gates_live':True,'all_ports_live':True,'independent_integer_evaluations':150,'restoration_identity_checks':300,'modular_degree_checks':cert,
'circuit_sha256':hashlib.sha256((H/'integer28_normalized_amalgam128_degree258.json').read_bytes()).hexdigest(),
'proof_boundary':'Finite checks supplement, not replace, the signed-domain theorem and exact compiler dependencies.'}
(H/'INTEGER28_AMALGAM_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

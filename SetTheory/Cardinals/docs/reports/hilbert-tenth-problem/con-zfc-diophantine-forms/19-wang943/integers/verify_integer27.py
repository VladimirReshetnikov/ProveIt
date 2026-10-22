"""Independent standard-library verification of the27-integer weighted norm."""
import json,hashlib,random
from pathlib import Path
H=Path(__file__).resolve().parent;p=json.loads((H/'integer27_weighted_root136_degree1116.json').read_text());rows=p['source'];known=set(p['witnesses']+p['fixed_numerals'])
for n,op,a,b in rows:
 assert n not in known and op in '+-*'
 assert isinstance(a,int) or a in known
 assert isinstance(b,int) or b in known
 known.add(n)
live={p['output']}
for n,op,a,b in rows[::-1]:
 if n in live:live.update(x for x in [a,b] if isinstance(x,str))
assert len(rows)==136 and len(p['witnesses'])==27 and all(n in live for n,*_ in rows) and set(p['witnesses']+p['fixed_numerals'])<=live

def evaluate(v):
 v=v.copy()
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def formula(v):
 J,F,al,z,s,eta,ze=[v[x] for x in p['positive_ports']];h,i,T,w,g,t=[v[x] for x in ['h','i','auxiliary_quotient','w','gamma','t']]
 q=v['Bm1']*J+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+ze;c=k*Y+eta;a=E+Y;Hh=4*a+3;De=a*a+Hh;L=E*k*Y
 R=((q-1)*(q-F)+al)*(q*q-1)+(v['MC']+q*v['MF'])*J
 N1=(X+g*Hh)**2+2*a*c*(X+g*Hh)-Hh*c*c;Nk=k-h*E-R;Nt=(v['Kconstant']+w)*(q-F-al)+q-F-z*(q-1)
 A=1+L*(L+k);Q=(De*i*c*c)**2;D=1+De*i*i*c**4;vv=c*T;b=c+R*D;d=Q-1;e=Q*(D*vv*vv+b*b)-1;M=D+vv*vv;C=d*(t*t+M*M*A)-e;B=2*Q*vv*b
 U=C*C+D*B*B-4*d*d*t*t*M*M*A;res=U*U-D*(2*C*B)**2
 return N1*Nk*Nt*(1+res)-1
rng=random.Random(20261022)
for _ in range(150):
 v={x:rng.randrange(-3,4) for x in p['witnesses']};v.update({x:rng.randrange(2,8) for x in p['fixed_numerals']});v=evaluate(v);assert v[p['output']]==formula(v)

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,P,sgn=1):
 r=[0]*max(len(a),len(b))
 for j,x in enumerate(a):r[j]=x
 for j,x in enumerate(b):r[j]=(r[j]+sgn*x)%P
 return trim(r)

def mul(a,b,P):
 n=len(a)+len(b)-1;assert min(len(a),len(b))*(P-1)**2<2**64
 aa=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in a),'little');bb=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in b),'little');raw=(aa*bb).to_bytes(8*n,'little')
 return trim([int.from_bytes(raw[j:j+8],'little')%P for j in range(0,len(raw),8)])

def line(P,beta,slope):
 active={'Jrep_positive_a','h','gamma','i_integer','eta_positive_a','w_integer','s_positive_a'}
 v={x:([0,1] if x in active else [0]) for x in p['witnesses']};v['transport_quotient_positive_a']=[0,slope];v.update({x:[beta if x=='Bm1' else 7] for x in p['fixed_numerals']})
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else [a%P];b=v[b] if isinstance(b,str) else [b%P];v[n]=mul(a,b,P) if op=='*' else add(a,b,P,1 if op=='+' else -1)
 return v[p['output']]
cert=[]
for P,beta in [(1000003,3),(1000033,5)]:
 a=line(P,beta,2);base=line(P,beta,0);one=line(P,beta,1);diff=add(one,base,P,-1);coeff=pow(2,27,P)*pow(beta,344,P)%P
 assert len(a)-1==1116 and a[-1]==3*coeff%P!=0 and len(diff)-1==1116 and diff[-1]==coeff
 cert.append({'prime':P,'Bm1':beta,'degree':1116,'top_coefficient':a[-1],'isolated_coefficient':diff[-1]})
receipt={'status':'PASS','variables':27,'operations':136,'multiplications':72,'additions_subtractions':64,'exact_degree':1116,'all_gates_live':True,'all_ports_live':True,'independent_formula_evaluations':150,'modular_degree_checks':cert,'circuit_sha256':hashlib.sha256((H/'integer27_weighted_root136_degree1116.json').read_bytes()).hexdigest()}
(H/'INTEGER27_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

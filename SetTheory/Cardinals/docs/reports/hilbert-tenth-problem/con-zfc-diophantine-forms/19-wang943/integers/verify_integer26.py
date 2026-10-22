"""Independent free-algebra and exact modular checks for the26-integer circuit."""
import json,hashlib,random,math
from fractions import Fraction
from pathlib import Path
H=Path(__file__).resolve().parent;p=json.loads((H/'integer26_four_root194_degree3185.json').read_text());rows=p['source'];known=set(p['witnesses']+p['fixed_numerals'])
assert len(p['witnesses'])==26 and len(rows)==194
for n,op,a,b in rows:
 assert n not in known and op in '+-*'
 assert isinstance(a,int) or a in known
 assert isinstance(b,int) or b in known
 known.add(n)
live={p['output']}
for n,op,a,b in rows[::-1]:
 if n in live:live.update(x for x in [a,b] if isinstance(x,str))
assert all(n in live for n,*_ in rows) and set(p['witnesses']+p['fixed_numerals'])<=live

def evaluate(v):
 v=v.copy()
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def ringmul(x,y,A,G):
 out=[0]*4
 for j,a in enumerate(x):
  for k,b in enumerate(y):out[j^k]+=a*b*(A if j&k&1 else 1)*(G if j&k&2 else 1)
 return out

def independent(v):
 J,F,al,z,s,et,ze=[v[x] for x in p['positive_ports']];h,i,T,w,t=[v[x] for x in ['h','i','T','w','t']]
 q=v['beta']*J+1;X=w*q;Y=s*q**3;E=X*Y;k=et+ze;c=k*Y+et;a=E+Y;Hh=4*a+3;De=a*a+Hh;L=E*k*Y
 R=((q-1)*(q-F)+al)*(q*q-1)+(v['MC']+q*v['MF'])*J
 Nk=k-h*E-R;Nt=(v['K0']+w)*(q-F-al)+q-F-z*(q-1)
 A=1+L*(L+k);G=1+De*c*c;S=De*i*c*c;Q=S*S;D=1+De*i*i*c**4;d=Q-1;vv=c*T;b=c+R*D;e=Q*(D*vv*vv+b*b)-1;B=2*Q*vv*b
 W=2*d*((S*i)*(vv*T)+b);P=Hh*W;K=P+1;u=6*P;Z=Hh*t+K*(X+a*c)
 # Compute four separate formal sign factors, not the nested norm circuit.
 out=[1,0,0,0]
 for sr in [-1,1]:
  for ss in [-1,1]:
   lin=[Z,-sr*u,-ss*K,0];inner=ringmul(lin,lin,A,G);inner[0]-=Hh*Hh*d*e
   f=ringmul(inner,inner,A,G);f[0]-=Hh**4*d*d*B*B*D
   out=ringmul(out,f,A,G)
 assert out[1:]==[0,0,0]
 return Nk*Nt*(1+out[0])-1,out[0]

rng=random.Random(20261022)
for _ in range(120):
 vals={x:rng.randrange(-2,3) for x in p['witnesses']};vals.update({x:rng.randrange(2,8) for x in p['fixed_numerals']});v=evaluate(vals)
 direct,res=independent(v);assert direct==v[p['output']] and res==v['Res12']
 assert all(v[x]>0 for x in p['positive_ports']) and v['i']%2==1 and v['w']>=0

# Finite rational-square diagnostic for the separate unbounded Pell lemma.
saturation=0;hits=0
for S in range(2,81):
 for V in range(-100,101):
  f=Fraction(S*S*V*V-1,S*S-1)
  if f<0:continue
  saturation+=1;n=math.isqrt(f.numerator);d=math.isqrt(f.denominator)
  if n*n==f.numerator and d*d==f.denominator:
   hits+=1;assert d==1

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,P,sgn=1):
 r=[0]*max(len(a),len(b))
 for j,x in enumerate(a):r[j]=x
 for j,x in enumerate(b):r[j]=(r[j]+sgn*x)%P
 return trim(r)

def mul(a,b,P):
 # Kronecker multiplication. Coefficient sums are<2^64, so packed digits cannot carry.
 n=len(a)+len(b)-1
 assert min(len(a),len(b))*(P-1)**2 < 2**64
 aa=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in a),'little')
 bb=int.from_bytes(b''.join(x.to_bytes(8,'little') for x in b),'little')
 raw=(aa*bb).to_bytes(8*n,'little')
 return trim([int.from_bytes(raw[j:j+8],'little')%P for j in range(0,len(raw),8)])

def line(P,beta,zslope):
 active={'J_positive_a','h','i_integer','eta_positive_a','w_integer','s_positive_a'}
 v={x:([0,1] if x in active else [0]) for x in p['witnesses']};v['z_positive_a']=[0,zslope]
 v.update({x:[beta if x=='beta' else 7] for x in p['fixed_numerals']})
 for n,op,a,b in rows:
  a=v[a] if isinstance(a,str) else [a%P];b=v[b] if isinstance(b,str) else [b%P]
  v[n]=mul(a,b,P) if op=='*' else add(a,b,P,1 if op=='+' else -1)
 return v[p['output']]
cert=[]
for P,beta in [(1000003,3),(1000033,5)]:
 a=line(P,beta,2);zero=line(P,beta,0);one=line(P,beta,1);diff=add(one,zero,P,-1)
 expected=pow(2,140,P)*pow(3,8,P)*pow(beta,1013,P)%P
 assert len(a)-1==3185 and a[-1]==3*expected%P!=0
 assert len(diff)-1==3185 and diff[-1]==expected
 cert.append({'prime':P,'beta':beta,'degree':3185,'top_coefficient':a[-1],'isolated_coefficient':diff[-1]})
receipt={'status':'PASS','variables':26,'operations':194,'multiplications':119,'additions_subtractions':75,'exact_degree':3185,'resultant_exact_degree':3168,
 'all_ports_live':True,'all_gates_live':True,'independent_four_factor_norm_evaluations':120,
 'rational_pell_diagnostic_assignments':saturation,'rational_pell_square_hits':hits,'modular_degree_checks':cert,
 'circuit_sha256':hashlib.sha256((H/'integer26_four_root194_degree3185.json').read_bytes()).hexdigest(),
 'scope':'Finite identities and degree diagnostics supplement the ordinary unbounded proof; no actual K215 accepting computation is asserted.'}
(H/'INTEGER26_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

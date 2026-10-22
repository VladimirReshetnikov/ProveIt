"""Independent, standard-library-only verification of the newly authored circuit."""
import hashlib,json,random,math
from pathlib import Path
H=Path(__file__).resolve().parent
p=json.loads((H/'integer28_gap_norm127_degree426.json').read_text())
rows=p['source'];known=set(p['witnesses']+p['fixed_numerals']);assert len(known)==32
for out,op,a,b in rows:
 assert out not in known and op in ('+','-','*')
 assert isinstance(a,int) or a in known
 assert isinstance(b,int) or b in known
 known.add(out)
live={p['output']}
for out,op,a,b in rows[::-1]:
 if out in live:
  for x in [a,b]:
   if isinstance(x,str):live.add(x)
assert all(out in live for out,*_ in rows)
assert set(p['witnesses']+p['fixed_numerals'])<=live
assert len(rows)==127 and len(p['witnesses'])==28
assert sum(op=='*' for _,op,_,_ in rows)==66

def run(v,source=rows,out=p['output']):
 v=v.copy()
 for name,op,a,b in source:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return v[out],v

def plain(a):
 J,F,al,z,s,eta,ze=[a[x] for x in p['positive_ports']]
 w=a['w'];i=a['i'];T=a['auxiliary_quotient'];h=a['h'];g=a['gamma'];ta=a['tau_root'];e=a['auxiliary_gap']
 q=a['Bm1']*J+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+ze;c=k*Y+eta
 aa=E+Y;Hh=4*aa+3;De=aa*aa+Hh;Dm=X+aa*c+g*Hh;L=E*k*Y
 R=((q-1)*(q-F)+al)*(q*q-1)+(a['MC']+q*a['MF'])*J
 N0=ta*ta-L*(L+k);N1=(X+g*Hh)**2+2*aa*c*(X+g*Hh)-Hh*c*c
 Nk=k-h*E-R;Nt=(a['Kconstant']+w)*(q-F-al)+q-F-z*(q-1)
 Q=(De*i*c*c)**2;d=1+De*i*i*c**4;b=c+R*d;v=c*T;S=Q-1;r=b+S*e
 A=d*v*v+b*b+S*e*(2*b-e)-1;K=A*A-4*d*v*v*r*r
 return N0*N1*Nk*Nt*(1+K)-1

rng=random.Random(20261022)
parent=json.loads((H/p['source_parent']).read_text())
for _ in range(150):
 values={x:rng.randrange(-3,4) for x in p['witnesses']}
 values.update({x:rng.randrange(2,9) for x in p['fixed_numerals']})
 result,v=run(values)
 transformed={x:v[x] for x in parent['witnesses']+parent['fixed_numerals']}
 assert result==run(transformed,parent['source'],parent['output'])[0]==plain(transformed)
 assert v['i']%2==1 and v['w']>=0
 assert all(v[x]>0 for x in p['positive_ports'])

# Direct independent algebraic check of the remainder identity.
for _ in range(1000):
 f,v,b,Q,e=[rng.randrange(-9,10) for _ in range(5)];d=f*f;S=Q-1;r=b+S*e
 A=d*v*v+b*b+S*e*(2*b-e)-1;V=v*f-b
 assert A-2*v*r*f==Q*(V*V-(V+e)**2)+(V+e)**2-1

# Positivity image coverage supplements, and does not replace, the three-square proof.
N=1500;covered=set()
for a in range(math.isqrt(N)+1):
 for b in range(math.isqrt(N-a*a)+1):
  for c in range(math.isqrt(N-a*a-b*b)+1):
   n=1+a*a+b*b+c*(c+1)
   if n<=N:covered.add(n)
assert set(range(1,N+1))<=covered

# Exact modular univariate evaluation: no numerical root approximations.
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def polyadd(a,b,prime,sign=1):
 r=[0]*max(len(a),len(b))
 for j,x in enumerate(a):r[j]=x
 for j,x in enumerate(b):r[j]=(r[j]+sign*x)%prime
 return trim(r)

def polymul(a,b,prime):
 r=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):r[j+k]=(r[j+k]+x*y)%prime
 return trim(r)

def line(prime,beta,zslope):
 # Isolate a sparse direction. All omitted coordinates are identically zero.
 active={'Jrep_positive_a','h','gamma','auxiliary_gap','i_integer','eta_positive_a','w_integer','s_positive_a'}
 v={x:([0,1] if x in active else [0]) for x in p['witnesses']}
 v['transport_quotient_positive_a']=[0,zslope]
 v.update({x:[beta if x=='Bm1' else 7] for x in p['fixed_numerals']})
 for name,op,a,b in rows:
  a=v[a] if isinstance(a,str) else [a%prime];b=v[b] if isinstance(b,str) else [b%prime]
  v[name]=polyadd(a,b,prime,1 if op=='+' else -1) if op!='*' else polymul(a,b,prime)
 return v[p['output']]
certs=[]
for prime,beta in [(1000003,3),(1000033,5)]:
 a=line(prime,beta,2);expected=(-3*8192*pow(beta,134,prime))%prime
 assert len(a)-1==426 and a[-1]==expected!=0
 base=line(prime,beta,0);one=line(prime,beta,1)
 diff=polyadd(one,base,prime,-1)
 assert len(diff)-1==426 and diff[-1]==(-8192*pow(beta,134,prime))%prime
 certs.append({'prime':prime,'Bm1':beta,'degree':426,'top_coefficient':a[-1],
   'isolated_monomial_coefficient_mod_prime':diff[-1]})
receipt={'status':'PASS','variables':28,'operations':127,'multiplications':66,'additions_subtractions':61,
 'exact_degree':426,'all_gates_live':True,'all_ports_live':True,'integer_formula_comparisons':150,
 'remainder_identity_comparisons':1000,'positivity_coverage':N,'univariate_checks':certs,
 'proof_boundary':'Finite algebra checks do not prove the inherited unbounded Pell/compiler theorems.',
 'circuit_sha256':hashlib.sha256((H/'integer28_gap_norm127_degree426.json').read_bytes()).hexdigest()}
(H/'INTEGER28_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

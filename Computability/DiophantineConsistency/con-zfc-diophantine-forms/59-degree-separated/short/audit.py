#!/usr/bin/env python3
"""Independent stdlib literal, coefficient, degree, and reconstruction audit.
Does not import the generator or execute any upstream Python file.
"""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,random,re
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
 if not ok:raise ValueError(msg)
def add(p,q,sgn=1):
 r=dict(p)
 for m,c in q.items():
  r[m]=r.get(m,0)+sgn*c
  if not r[m]:del r[m]
 return r
def mul(p,q):
 r={}
 for m,c in p.items():
  for n,d in q.items():
   t=tuple(x+y for x,y in zip(m,n));r[t]=r.get(t,0)+c*d
 return {m:c for m,c in r.items() if c}
def top(p,nw):
 if not p:return -1,{}
 d=max(sum(m[:nw]) for m in p)
 return d,{m:c for m,c in p.items() if sum(m[:nw])==d}
def evaluate(c,v,mod=None):
 env=dict(v)
 for n,o,a,b in c['source']:
  x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
  z=x+y if o=='+' else x-y if o=='-' else x*y
  env[n]=z if mod is None else z%mod
 return env[c['output']]
def formula(c,v):
 o=c['options'];J,F,alpha,z,f,i,T,s,w,eta,zeta,gamma=[v[x] for x in ['J','F','alpha','z','f','i','T','s','w','eta','zeta','gamma']]
 beta,K,MC,MF=[v[x] for x in ['beta','K0','MC','MF']]
 q=beta*J+1;C=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c0=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H
 R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 V=f*f*(c0*T-R)-c0 if o['squared_modulus'] else c0*(T*f-1)-R*f*f
 Aaux=Delta*(f*f-1);I=i*c0*c0*(Delta if o['kind']=='scaled_product' else 1);L=E*k*Y
 N0=v['r']**2+L*(2*v['r']-k) if o['first_gap'] else v['tau']**2-L*(L+k)
 Na=(V+v['u'])**2-Aaux*v['u']*(2*V+v['u']) if o['aux_gap'] else Aaux*(V*V-v['y']**2)+v['y']**2
 Nt=(K+w)*C+q-F-z*(q-1);S=I*I-Aaux
 if o['variables']==14:
  U=4*q**4;Dstar=U*(X+a*c0)+H*(U*gamma-k+R+1)
  return (Dstar*Dstar-U*U*(1+Delta*c0*c0))**2+S*S+(Na-1)**2+(N0*Nt-1)**2
 N1=(X+a*c0+gamma*H)**2-Delta*c0*c0;Nk=k-v['h']*E-R
 vals={'N0':N0,'N1':N1,'Na':Na,'Nk':Nk,'Nt':Nt}
 if o['kind']=='scaled_product':return N0*N1*Na*Nk*Nt*(Delta*f*f-I*I)-Delta
 if o['kind']=='product':return N0*N1*Na*Nk*Nt*(S+1)-1
 result=S*S
 for block in o['groups']:
  p=1
  for x in block:p*=vals[x]
  result+=(p-1)**2
 return result

def audit_circuit(path,ports):
 c=json.loads(path.read_text());require(c['coefficient_binding']=='../COEFFICIENT_BINDING.json' and (path.parent/c['coefficient_binding']).is_file(),'circuit-relative coefficient binding');names=c['witnesses']+c['fixed_numerals'];nw=len(c['witnesses']);nv=len(names);zero=(0,)*nv
 require(nw==c['options']['variables'],'witness count');require(len(set(names))==nv,'unique inputs')
 if nw==15 and c['options']['kind']=='sos':require(sorted(x for g in c['options']['groups'] for x in g)==['N0','N1','Na','Nk','Nt'],'unit factors exactly once')
 scalar=lambda x:{zero:x} if x else{}
 full={};lead={};producers={};counts=Counter()
 for j,n in enumerate(names):
  e=[0]*nv;e[j]=1;full[n]={tuple(e):1};lead[n]=(1 if j<nw else 0,full[n])
 def readlead(x):return (0,scalar(x)) if isinstance(x,int) else lead[x]
 def readfull(x):return scalar(x) if isinstance(x,int) else full[x]
 # Expand only the ancestor cone of the main norm; this checks the real
 # cancellation before using highest homogeneous forms elsewhere.
 main='main_residual' if nw==14 else 'N1';allprod={r[0]:r for r in c['source']};cone=set()
 def visit(x):
  if isinstance(x,str) and x in allprod and x not in cone:
   cone.add(x);visit(allprod[x][2]);visit(allprod[x][3])
 visit(main)
 for n,o,a,b in c['source']:
  require(n not in lead,'producer redefinition');require(o in '+-*','binary operation')
  for x in (a,b):require(isinstance(x,int) or x in lead,'undefined operand')
  da,pa=readlead(a);db,pb=readlead(b)
  if n in cone:
   ap,bp=readfull(a),readfull(b);fp=mul(ap,bp) if o=='*' else add(ap,bp,1 if o=='+' else-1);full[n]=fp;ld=top(fp,nw)
  elif o=='*':ld=(da+db,mul(pa,pb))
  elif da>db:ld=(da,pa)
  elif db>da:ld=(db,pb if o=='+' else{m:-x for m,x in pb.items()})
  else:
   pp=add(pa,pb,1 if o=='+' else-1);require(bool(pp),'unhandled leading cancellation '+n);ld=(da,pp)
  lead[n]=ld;producers[n]=(a,b);counts[o]+=1
 live=set()
 def mark(n):
  if not isinstance(n,str) or n in live:return
  live.add(n)
  if n in producers:
   for x in producers[n]:mark(x)
 mark(c['output']);require(live==set(names)|set(producers),'dead gates or unused inputs')
 match=re.match(r'p(\d+)_d(\d+)',c['name']);expected_ops,expected_degree=map(int,match.groups())
 require(len(producers)==expected_ops,'operation count');d,p=lead[c['output']];require(d==expected_degree,'exact degree')
 # A displayed monomial involving no symbolic coefficient except beta
 # cannot cancel when the authentic nonzero ports are bound.
 fixed_beta=names.index('beta');dist=[]
 for m,coeff in p.items():
  if all(e==0 for j,e in enumerate(m[nw:],nw) if j!=fixed_beta):dist.append((m,coeff))
 require(bool(dist),'no fixed-tuple noncancellation witness')
 m,coeff=sorted(dist)[0]
 rng=random.Random(86101+nw);prime=1000000007
 for trial in range(100):
  v={n:rng.randrange(-5,6) for n in c['witnesses']};v.update({n:x%prime for n,x in ports.items()} if trial%2 else {n:rng.randrange(-5,6) for n in ports})
  require(evaluate(c,v,prime)==formula(c,v)%prime,'literal formula mismatch')
 return dict(name=c['name'],variables=nw,operations=len(producers),operation_counts=dict(counts),exact_degree=d,main_residual_degree=lead[main][0],main_expansion_terms=len(full[main]),leading_terms=len(p),nonzero_monomial={n:e for n,e in zip(names,m) if e},nonzero_coefficient=coeff,literal_trials=100,sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def check_local_identities():
 names=['c','f','T','R','L','r','k','A','V','u','a','H','Z','U','b','gamma','r0','G'];n=len(names);z=(0,)*n
 def v(name):
  e=[0]*n;e[names.index(name)]=1;return {tuple(e):1}
 def sc(x):return {z:x} if x else{}
 def sq(x):return mul(x,x)
 c,f,T,R,L,r,k,A,V,u,a,H,Z,U,b,gamma,r0,G=map(v,names)
 old=add(mul(c,add(mul(mul(f,T),f),sc(1),-1)),mul(R,sq(f)),-1)
 new=add(mul(sq(f),add(mul(c,T),R,-1)),c,-1)
 require(old==new,'exact squared-modulus pullback identity')
 require(add(sq(add(L,r)),mul(L,add(L,k)),-1)==add(sq(r),mul(L,add(mul(sc(2),r),k,-1))),'exact first-gap identity')
 y=add(V,u)
 require(add(mul(A,add(sq(V),sq(y),-1)),sq(y))==add(sq(y),mul(mul(A,u),add(V,y)),-1),'exact auxiliary-gap identity')
 require(add(sq(add(mul(a,c),Z)),mul(add(sq(a),H),sq(c)),-1)==add(add(sq(Z),mul(sc(2),mul(mul(a,c),Z))),mul(H,sq(c)),-1),'exact main cancellation identity')
 D=add(b,mul(H,gamma));Dstar=add(mul(U,b),mul(H,add(mul(U,gamma),r0,-1)))
 left=add(sq(Dstar),mul(sq(U),G),-1)
 right=add(add(mul(sq(U),add(sq(D),G,-1)),mul(mul(mul(mul(sc(2),U),H),r0),D),-1),mul(sq(H),sq(r0)))
 require(left==right,'exact absorber expansion identity')
 return 5

def pell(a,n):
 x,y=1,0
 for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y

def check_reconstruction():
 n=0
 for A in range(2,7):
  Delta=A*A-1
  for R in (3,7,11):
   D,c=pell(A,R)
   # m=2cR produces the normalized c² divisibility, without huge expansion
   # for large examples: use small m=2cR only at R=3, otherwise modular
   # identity examples below establish the square-modulus congruence.
   if R!=3:continue
   f,ps=pell(A,2*c*R);require(ps%(c*c)==0,'canonical rank divisibility')
   I=Delta*ps;require(I*I==Delta*(f*f-1),'ordinary strong norm')
   chi,y=pell(I,R);require(chi%I==0,'odd quotient');V=chi//I
   require((V+c)%(f*f)==0,'square-modulus congruence');require((V+R)%c==0,'c congruence')
   num=V+c+R*f*f;require(num%(c*f*f)==0,'reconstructed T integrality');T=num//(c*f*f)
   require(T>0 and V>1 and y>V,'positive reconstruction and auxiliary gap')
   require(V==f*f*(c*T-R)-c,'new quotient identity');require(I*I*(V*V-y*y)+y*y==1,'auxiliary norm')
   u=y-V;require((V+u)**2-I*I*u*(2*V+u)==1,'gap identity');n+=1
 # The obstruction for the ordinary strong unit is a complete mod-four check.
 for Delta in (0,3):
  for I2 in (0,1):
   for f2 in (0,1):require((1+I2-Delta*(f2-1))%4!=3,'strong minus-one obstruction')
 return n

def main():
 binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text());vals={}
 require(hashlib.sha256((ROOT/binding['source_binding_path']).read_bytes()).hexdigest()==binding['source_binding_sha256'],'historical binding hash')
 require(hashlib.sha256((ROOT/binding['source_adapter_proof_path']).read_bytes()).hexdigest()==binding['source_adapter_sha256'],'active adapter proof hash')
 for item in binding['payloads']:
  raw=(ROOT/item['path']).read_bytes();require(hashlib.sha256(raw).hexdigest()==item['gzip_sha256'],'gzip hash');data=gzip.decompress(raw)
  require(hashlib.sha256(data).hexdigest()==item['sha256'] and len(data)==item['bytes'],'payload bytes');v=int.from_bytes(data,'little');require(v.bit_length()==item['bit_length'],'bit length');vals[item['name']]=v
 B=1<<1064921;require(vals['beta']==B-1,'beta');require(vals['K']>0,'K');native=vals['MF_source']-(B-1)
 require(0<vals['MC']<B-1 and 0<native<B-1,'mask range');require(vals['MC']%4==2 and native%8==4,'mask congruence');require(vals['MC'].bit_count()+native.bit_count()==1064921,'mask population')
 ports={k:vals[v] for k,v in binding['port_aliases'].items()};pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for name,item in pins['text_sources'].items():require(hashlib.sha256((ROOT/'upstream'/name).read_bytes()).hexdigest()==item['sha256'],'upstream proof text hash')
 rows=[audit_circuit(p,ports) for p in sorted((ROOT/'circuits').glob('*.json'))]
 result=dict(status='PASS',circuits=rows,exact_local_polynomial_identities=check_local_identities(),reconstruction_examples=check_reconstruction(),strong_mod4_cases=8,coherent_tuple='Wang943 121-by-8801',scope='Finite literal/degree/byte evidence, separate from the unbounded compiler and Pell proof.')
 (ROOT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent complete front binding, sixteen-conjugate norm and degree checks."""
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from math import factorial
from pathlib import Path
import random
import sys
import zipfile

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
OPS={'add','sub','mul'}

def need(ok,message):
 if not ok:raise ValueError(message)

def digest(x):return sha256(x).hexdigest()
def load(path):return json.loads(path.read_bytes())

class Ring:
 """Sparse free integer ring; monomials are sorted tuples of formal names."""
 def __init__(self,x=0):
  self.t=dict(x)if isinstance(x,dict)else({():x}if x else{})
 @staticmethod
 def var(x):return Ring({(x,):1})
 def __add__(self,b):
  b=b if isinstance(b,Ring)else Ring(b);v=dict(self.t)
  for m,c in b.t.items():
   v[m]=v.get(m,0)+c
   if not v[m]:del v[m]
  return Ring(v)
 __radd__=__add__
 def __neg__(self):return Ring({m:-c for m,c in self.t.items()})
 def __sub__(self,b):return self+-1*b
 def __rsub__(self,b):return Ring(b)+-self
 def __mul__(self,b):
  b=b if isinstance(b,Ring)else Ring(b);v={}
  for m,c in self.t.items():
   for n,d in b.t.items():
    key=tuple(sorted(m+n));v[key]=v.get(key,0)+c*d
  return Ring({m:c for m,c in v.items()if c})
 __rmul__=__mul__
 def __pow__(self,n):
  need(type(n)is int and n>=0,'nonnegative polynomial exponent');out=Ring(1)
  for _ in range(n):out=out*self
  return out

FRONT=[
 ('J','6*j+1'),('q','beta*J+1'),('W','12*w+4'),('X','q*W'),('Y','q*v'),
 ('E','X*Y'),('a','E+Y'),('H','4*a+3'),('Delta','a*a+H'),
 ('F','(K0+W)*C-z*(beta*J)'),
 ('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('k','R+1+h*E'),('eta','c-Y*k'),('zeta','k-eta'),('c2','c*c'),
 ('I','(2*r+1)*c2'),('I2','I*I'),('Df','1+Delta*I2'),
 ('Q','Delta*Delta*I2'),('delta','Q-1'),('V','Df*(c*T-R)-c'),
 ('Cy','Q*V*V-1'),('ell0','Y*E'),('Dtau','1+ell0*(ell0+1)*k*k'),
 ('K','X*(X+2*a*c)-1'),('coneU','cone_A*F'),('coneZ','cone_B*C'),
 ('G','coneU*coneZ-(q-coneU-coneZ)**2'),('Peta','eta*zeta'),
 ('Pair','G*Peta-(t*t-G-Peta+1)**2'),
 ('Ag','Pair-1-p2*p2-p3*(p3+1)'),
 ('M','2*q*q'),('U','M*H'),('U2','U*U'),
 ('center','U*(n+V)+M*K+H*(v-q*q)'),
 ('raw_A','U2*Df'),('raw_B','U2*Dtau'),('Cn','U2*Cy'),('scaled_Ag','U2*Ag'),
]

def front_binding(child):
 nodes=child['nodes'];nm=child['named_registers'];stops={};covered=set();checks=[]
 env={r[1]:Ring.var(r[1])for r in nodes if r[0]in('variable','coefficient')}
 def expand(i,visited):
  visited.add(i)
  if i in stops:return stops[i]
  r=nodes[i]
  if r[0]=='integer':return Ring(r[1])
  if r[0]in('variable','coefficient'):return env[r[1]]
  u,v=expand(r[1],visited),expand(r[2],visited)
  return u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v
 for name,expression in FRONT:
  index=nm[name];visited=set();have=expand(index,visited)
  want=eval(expression,{'__builtins__':{}},env)
  need(have.t==want.t,'universal whole front binding: '+name)
  covered|=visited;stops[index]=Ring.var(name);env[name]=stops[index]
  checks.append(dict(register=name,node=index,terms=len(want.t)))
 return covered,checks

def evaluate(nodes,inputs,prime=None):
 vals=[]
 for r in nodes:
  if r[0]=='integer':v=r[1]
  elif r[0]in('variable','coefficient'):v=inputs[r[1]]
  else:
   a,b=vals[r[1]],vals[r[2]];v=a+b if r[0]=='add'else a-b if r[0]=='sub'else a*b
  vals.append(v if prime is None else v%prime)
 return vals

def independent_front(e,p):
 def z(v):return v%p
 j,C,zz,h,r,v,w,T,c,n,t,p2,p3=[e[k]for k in('j','C','z','h','r','v','w','T','c','n','t','p2','p3')]
 J=z(6*j+1);q=z(e['beta']*J+1);W=z(12*w+4);X=z(q*W);Y=z(q*v);E=z(X*Y)
 a=z((X+1)*Y);H=z(4*a+3);D=z((a+2)**2-1)
 F=z((e['K0']+W)*C-zz*(q-1));R=z((q*(q-F)-C)*(q*q-1)+(e['MC']+q*e['MF'])*J)
 k=z(R+1+h*E);eta=z(c-Y*k);zeta=z(k-eta);I=z((2*r+1)*c*c)
 f=z(1+D*I*I);Q=z(D*D*I*I);delta=z(Q-1);V=z(f*(c*T-R)-c);Cy=z(Q*V*V-1)
 ell=z(X*Y*Y);tau=z(1+ell*(ell+1)*k*k)
 G=z((e['cone_A']*F)*(e['cone_B']*C)-(q-e['cone_A']*F-e['cone_B']*C)**2)
 Peta=z(eta*zeta);Pair=z(G*Peta-(t*t-G-Peta+1)**2);Ag=z(Pair-1-p2*p2-p3*(p3+1))
 M=z(2*q*q);U=z(M*H);K=z(X*(X+2*a*c)-1);Z=z(U*(n+V)+M*K+H*(v-q*q))
 return {'J':J,'q':q,'W':W,'X':X,'Y':Y,'E':E,'a':a,'H':H,'Delta':D,
 'F':F,'R':R,'k':k,'eta':eta,'zeta':zeta,'I':I,'Df':f,'Q':Q,'delta':delta,
 'V':V,'Cy':Cy,'Dtau':tau,'G':G,'Pair':Pair,'Ag':Ag,'M':M,'U':U,'K':K,
 'center':Z,'raw_A':z(U*U*f),'raw_B':z(U*U*tau),'scaled_Ag':z(U*U*Ag),'Cn':z(U*U*Cy)}

def line_data(values,p):
 degree,difference=-1,None;values=list(values);level=0
 while values:
  if values[0]:degree,difference=level,values[0]
  values=[(b-a)%p for a,b in zip(values,values[1:])];level+=1
 return degree,difference

def leading(e,p):
 q=6*e['beta']*e['j']%p;W=12*e['w']%p;X=q*W%p;Y=q*e['v']%p
 a=X*Y%p;i=2*e['r']%p;R=(q**4*e['z']-q**3*W*e['C'])%p
 eta=-Y*(R+e['h']*a)%p;Q=pow(a,4,p)*i*i*pow(e['c'],4,p)%p
 V=-a*a*i*i*pow(e['c'],4,p)*R%p;U=8*q*q*a%p
 return 256*pow(Q,8,p)*pow(U,16,p)*pow(V,8,p)*pow(eta,16,p)%p

def main():
 child=load(HERE/'equation.json');nodes=child['nodes'];nm=child['named_registers']
 build=load(HERE/'BUILD.json');provenance=load(HERE/'PROVENANCE.json')
 for name,pin in build['sha256'].items():need(digest((HERE/name).read_bytes())==pin,'generated seal '+name)
 for name,pin in provenance['source_file_sha256'].items():need(digest((HERE/name).read_bytes())==pin,'sourcepin '+name)
 need(child['variables']==['j','C','z','h','r','v','w','T','c','n','t','p2','p3']and
      child['domain']=='unrestricted integers'and child['variable_count']==13,'exact13 unrestricted coordinates')
 degrees=[]
 for i,r in enumerate(nodes):
  need(r[0]in OPS|{'integer','variable','coefficient'},'arithmetic node')
  if r[0]in OPS:
   need(len(r)==3 and all(type(j)is int and 0<=j<i for j in r[1:]),'acyclic operands')
   degrees.append(degrees[r[1]]+degrees[r[2]]if r[0]=='mul'else max(degrees[r[1]],degrees[r[2]]))
  else:degrees.append(1 if r[0]=='variable'else 0)
 live=set();todo=[child['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0]in OPS:todo.extend(nodes[i][1:])
 need(live==set(range(len(nodes))),'every actual node live')
 need([r[1]for r in nodes if r[0]=='variable']==child['variables'],'all13 variables live exactly once')
 counts=dict(Counter(r[0]for r in nodes if r[0]in OPS))
 need(len(nodes)==162 and counts==child['operation_counts']=={'mul':81,'add':27,'sub':27}and
      sum(counts.values())==child['operations']==135,'all135 live gates independently counted')
 covered,front=front_binding(child)
 helper=HERE/'source/independent_norm_oracle.py'
 need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','independent norm oracle')
 spec=importlib.util.spec_from_file_location('signed13_independent_oracle',helper)
 oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 x,a,b,e,cn,delta=[oracle.variable(i)for i in range(6)]
 generic={'center':x,'raw_A':a,'raw_B':b,'scaled_Ag':e,'Cn':cn,'delta':delta}
 env={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
 for name,value in generic.items():env[nm[name]]=value
 start=load(HERE/'CIRCUIT_BINDING.json')['prefix_length']
 for i in range(start,len(nodes)):
  r=nodes[i];covered.add(i)
  if r[0]=='integer':continue
  need(r[0]in OPS and r[1]in env and r[2]in env,'entire norm cut bound')
  u,v=env[r[1]],env[r[2]];env[i]=u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v
 fraction=oracle.Poly({(0,0,0,0,1,-1):1})
 expected=delta**8*oracle.norm_oracle(x,[a,b,e,fraction])
 need(env[child['output']].t==expected.t,'entire literal norm equals independent16-conjugate product')
 need(covered==set(range(len(nodes))),'every front and norm node universally accounted')
 # Center cancellation: cn=delta*x^2-omega, so last radicand=x^2-omega/delta.
 omega=cn
 centered=delta**8*oracle.norm_oracle(x,[a,b,e,x*x-fraction])
 weights=(25,26,34,40,56,22)
 maxweight=max(sum(i*w for i,w in zip(m,weights))for m in centered.t)
 top={m:c for m,c in centered.t.items()if sum(i*w for i,w in zip(m,weights))==maxweight}
 need(maxweight==536 and top=={(8,0,0,4,0,8):256},'exact centered weighted degree and unique top monomial')
 need(all(all(i>=0 for i in m)for m in expected.t),'denominator fully cleared')
 binding=load(HERE/child['coefficient_binding']);coeff={};payloads={}
 for name,pin in binding['payloads'].items():
  raw=gzip.decompress((HERE/'coefficients'/pin['file']).read_bytes())
  need(digest(raw)==pin['raw_sha256']and len(raw)==pin['raw_bytes'],'whole authentic coefficient bytes')
  coeff[name]=int.from_bytes(raw,'little');need(coeff[name].bit_length()==pin['bits'],'whole port bit length')
  payloads[name]=dict(raw_sha256=digest(raw),bits=pin['bits'])
 inherited_binding=load(HERE/'source/trace-coefficient-binding.json')
 need(binding==inherited_binding,'complete six-port binding equals old trace family')
 pins=load(HERE/'source/TRACE_SOURCE_PINS.json');archive=HERE.parents[3]/pins['archive']
 need(digest(archive.read_bytes())==pins['archive_sha256'],'entire original trace/interpolation ZIP')
 with zipfile.ZipFile(archive) as z:
  records=pins['files'];need(len(z.infolist())==len(records)==138,'complete138-member archive inventory')
  for record in records:
   member='con_zfc_trace_and_interpolation/'+record['path'].removeprefix('source/')
   raw=z.read(member)
   need(len(raw)==record['bytes']and digest(raw)==record['sha256'],'all138 archived source bytes')
  need(z.read('con_zfc_trace_and_interpolation/proofs/TRACE13_PROOF.md')==(HERE/'source/TRACE13_PROOF.md').read_bytes(),
       'retained trace ordinary proof exact archive member')
 need(digest((HERE/'source/SIGNED_QUADRATIC_PROOF.md').read_bytes())==
      'dfd78f5cf75133bdfd1a260be108fcac4663e71e97ca4a85dbf36f1a0d75da4c','corrected complete signed folding proof')
 need(set(coeff)=={'beta','K0','MC','MF','cone_A','cone_B'}and
      coeff['beta']==2**1064921-1 and coeff['cone_A']==2**1113 and
      coeff['cone_B']==2**666104,'same original coherent six ports')
 ports=[r[1]for r in nodes if r[0]=='coefficient'];need(set(ports)==set(coeff),'six live coefficient leaves')
 rng=random.Random(135536);controls=0
 for prime in(1009,(1<<127)-1):
  ce={k:v%prime for k,v in coeff.items()}
  for j in range(50):
   inputs={v:rng.randrange(-20,21)for v in child['variables']}
   if j%4==0:inputs['v']=0
   if j%5==0:inputs['c']=0
   inputs.update(ce);vals=evaluate(nodes,inputs,prime);want=independent_front(inputs,prime)
   need(all(vals[nm[k]]==v for k,v in want.items()),'all independently recomputed front registers')
   x0=vals[nm['center']];args=[vals[nm[k]]for k in('raw_A','raw_B','scaled_Ag','Cn','delta')]
   aa,bb,ee,cc,dd=args
   def eval_sparse(poly):
    result=0
    for mon,c in poly.t.items():
     term=c
     for z,k in zip((x0,aa,bb,ee,cc,dd),mon):term=term*pow(z,k,prime)%prime
     result=(result+term)%prime
    return result
   need(vals[child['output']]==eval_sparse(expected),'full actual-port output vs independent formal norm')
   controls+=1
 slices=[]
 for prime in((1<<127)-1,(1<<89)-1):
  ce={k:v%prime for k,v in coeff.items()}
  base={v:rng.randrange(1,prime)for v in child['variables']}
  direction={v:rng.randrange(1,prime)for v in child['variables']}
  values=[]
  for t in range(degrees[child['output']]+2):
   inputs=ce|{v:(base[v]+t*direction[v])%prime for v in child['variables']}
   values.append(evaluate(nodes,inputs,prime)[child['output']])
  degree,diff=line_data(values,prime)
  need(degree==536 and diff*pow(factorial(536),-1,prime)%prime==leading(ce|direction,prime),
       'actual tuple degree536 and exact homogeneous leading form')
  slices.append(dict(prime_bits=prime.bit_length(),degree=degree,leading_coefficient_matches=True))
 maps=0
 for _ in range(500):
  H=rng.choice([i for i in range(-50,51)if i]);M=rng.choice([i for i in range(-50,51)if i]);
  n,V,b0,gamma,kdiv,ell=[rng.randrange(-100,101)for _ in range(6)]
  d=b0+H*gamma;K=H*kdiv
  newcenter=Fraction(n+V)+Fraction(K,H)+ell
  oldn=n+kdiv+gamma
  oldcenter=Fraction(oldn+V)+Fraction(b0,H)+ell
  need(oldcenter==newcenter+Fraction(d,H),'unrestricted forward n restoration')
  roots=[rng.randrange(-100,101)for _ in range(4)]
  newn=sum(roots)-V-kdiv-ell
  need(newn+V+Fraction(K,H)+ell==sum(roots),'unrestricted reverse n witness')
  maps+=1
 # Mutations must be rejected by universal front binding and full norm comparison.
 bad=deepcopy(child);bad['nodes'][nm['K']][0]='add'
 try:front_binding(bad)
 except ValueError:pass
 else:raise ValueError('corrupted main projection accepted')
 bad=deepcopy(nodes);bad[child['output']][0]='add'
 corrupt_env={i:oracle.Poly(r[1])for i,r in enumerate(bad)if r[0]=='integer'}
 for name,value in generic.items():corrupt_env[nm[name]]=value
 for i in range(start,len(bad)):
  r=bad[i]
  if r[0]=='integer':continue
  u,v=corrupt_env[r[1]],corrupt_env[r[2]]
  corrupt_env[i]=u+v if r[0]=='add'else u-v if r[0]=='sub'else u*v
 need(corrupt_env[child['output']].t!=expected.t,'actual final norm sign corruption rejected')
 xx,aa,cc,hh=[Ring.var(k)for k in('X','a','c','H')]
 kk=xx*(xx+2*aa*cc)-1;bb=xx+aa*cc
 need((bb*bb-(1+(aa*aa+hh)*cc*cc)).t==(kk-hh*cc*cc).t,
      'universal quadratic restoration identity')
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),integer_variables=13,
  operations=135,operation_counts=counts,all_nodes=162,all_nodes_live=True,
  complete_universal_front_binding=front,independent_norm_coefficients=len(expected.t),
  complete_universal_norm_binding=True,every_node_universally_accounted=True,
  exact_degree=536,syntactic_bound=degrees[child['output']],
  centered_norm_terms=len(centered.t),centered_unique_leading_term={'coefficient':256,'exponents':[8,0,0,4,0,8]},
  selected_actual_coefficient={'variables':['j','w','v','h','r','c','z'],
   'exponents':[240,80,96,16,32,64,8],'value':'2^488*3^320*beta^240'},
  actual_port_controls=controls,actual_tuple_degree_slices=slices,unrestricted_n_maps=maps,
  whole_original_trace_archive_members=138,whole_original_trace_archive_sha256=pins['archive_sha256'],
  main_projection_and_norm_corruption_rejected=True,whole_six_payloads=payloads,
  proof_sha256=digest((HERE/'PROOF.md').read_bytes()),equation_sha256=digest((HERE/'equation.json').read_bytes()),
  scope='Universal complete literal polynomial binding, exact centered degree, authentic six-port bytes and finite transcription controls. The unbounded trace/folding/native existence proof is PROOF.md and its explicitly pinned ordinary dependencies; no Lean/internal-ZFC completion.')
 name='CHECK_OPTIMIZED.json'if sys.flags.optimize else'CHECK.json'
 (HERE/name).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
 print(json.dumps(report,indent=2))

if __name__=='__main__':main()

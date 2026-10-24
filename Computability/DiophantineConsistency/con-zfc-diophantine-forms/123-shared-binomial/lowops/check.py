#!/usr/bin/env python3
"""Independent exact audit of the two eleven-integer product polynomials.

Uses only the Python standard library. Does not import or execute the producer. Statements about
unbounded Pell witnesses remain ordinary proofs in PROOF.md.
"""
import ast
import copy
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
import exact_poly as sp

ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']

def need(test,message):
 if not test:raise ValueError(message)

def formulas(short):
 f=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q*q*q'),
    ('W','12*w+4'),('X','q*W'),('Y','(2*v+1)*q*q*q'),('E','X*Y'),
    ('a','(X+1)*Y'),('H','4*a+3'),('Delta','(a+2)**2-1'),
    ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J')]
 if short:f+=[('q2four','4*q*q'),('index_modulus','4*q**4')]
 else:f+=[('index_modulus','X*Y')]
 f += [('k','R+1+h*index_modulus'),('c2','c*c'),('eta','c-Y*k'),
       ('coneF','cone_A*F'),('coneC','cone_B*C'),
       ('Derr','(coneF-q)**2+(coneC-q)**2'),
       ('Budget','k*k*(q*q-Derr)-4*q*q*eta*eta'),
       ('ell','X*Y*Y'),('L','ell*k'),('Dt','1+ell*(ell+1)*k*k'),
       ('D','3*Budget-4'),('s2','2*s'),('guard_scale','2*Dt*s'),
       ('P','Dt*(1+4*D*Dt*s*s)'),('Amain','a+2'),('Dm','1+Delta*c*c'),
       ('U','r*c*c*Amain*Dm'),('UP','U*P'),('strong','Delta*U*U*P'),
       ('Df','1+Delta*U*U*P'),('Q','Delta*Delta*U*U*P'),('delta','Q-1'),
       ('b','c-R+4*U*P*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
       ('K','X*(3*c-2*X)+2'),('H2','H*H'),('H3','H**3'),
       ('S','s*r*H'),('S2','S*S'),('zc','H*T+K'),('zc2','zc*zc'),
       ('Ac','(zc*zc+3*H*H)*(zc**3-19*H**3)'),
       ('Z','S*n-Ac'),('output','delta*Z*Z-S*S*P*Df*Cy')]
 return f

def local_checks(packet):
 nodes=packet['nodes'];nm=dict(packet['named_registers'])
 nm.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ['variable','coefficient']})
 nm['output']=packet['output'];covered=set();checked=[]
 for name,expr in formulas(packet['short_index']):
  need(name in nm,'missing displayed register '+name)
  refs=sorted({n.id for n in ast.walk(ast.parse(expr,mode='eval')) if isinstance(n,ast.Name)})
  syms={n:sp.Symbol(n) for n in refs};cut={nm[n]:v for n,v in syms.items()};memo=dict(cut)
  def rec(i):
   covered.add(i)
   if i in memo:return memo[i]
   row=nodes[i]
   if row[0]=='integer':val=sp.Integer(row[1])
   else:
    need(row[0] in ['add','sub','mul'],'unbound local input '+str(row))
    a,b=rec(row[1]),rec(row[2]);val=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
   memo[i]=val;return val
  expected=eval(expr,{'__builtins__':{}},syms)
  need(sp.expand(rec(nm[name])-expected)==0,'local polynomial identity '+name)
  checked.append(name)
 missing=[i for i,r in enumerate(nodes) if r[0] in ['add','sub','mul'] and i not in covered]
 need(not missing,'uncovered arithmetic gates '+str(missing))
 return {'registers':checked,'all_live_arithmetic_covered':True}

def topology(packet):
 nodes=packet['nodes'];degree=[]
 for i,row in enumerate(nodes):
  tag=row[0]
  if tag in ['add','sub','mul']:
   need(len(row)==3 and all(type(j) is int and 0<=j<i for j in row[1:]),'DAG topology')
   degree.append(degree[row[1]]+degree[row[2]] if tag=='mul' else max(degree[row[1]],degree[row[2]]))
  else:
   need(tag in ['variable','coefficient','integer'] and len(row)==2,'leaf format')
   if tag=='integer':need(type(row[1]) is int,'integer literal')
   degree.append(int(tag=='variable'))
 live=set();stack=[packet['output']]
 while stack:
  i=stack.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0] in ['add','sub','mul']:stack.extend(nodes[i][1:])
 need(live==set(range(len(nodes))),'no dead nodes')
 need([r[1] for r in nodes if r[0]=='variable']==VARS,'all eleven variables, in order')
 need([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'complete six-port tuple')
 counts=Counter(r[0] for r in nodes if r[0] in ['add','sub','mul'])
 want=112 if packet['short_index'] else 111
 need(dict(counts)==packet['operation_counts'] and sum(counts.values())==want==packet['operations'],'operation census')
 need(degree[packet['output']]==packet['exact_degree']==packet['syntactic_degree_bound'],'global degree upper bound')
 return {'live_nodes':len(nodes),'operations':want,'counts':dict(counts),'upper_bound':degree[packet['output']]}

def exact_leading(packet):
 # A highest monomial in a multiplicative graded lexicographic order is
 # enough at each gate because the checker rejects every zero leading
 # coefficient. This is exact, not a specialization to a test ray.
 order=['h','T','j','w','v','s','r','c','C','z','n'];zero=(0,)*11
 coeff={p:sp.Symbol(p) for p in PORTS};vals=[]
 def key(a):return (sum(a[0]),)+a[0]
 for i,row in enumerate(packet['nodes']):
  tag=row[0]
  if tag=='variable':
   ex=[0]*11;ex[order.index(row[1])]=1;v=(tuple(ex),sp.Integer(1))
  elif tag=='coefficient':v=(zero,coeff[row[1]])
  elif tag=='integer':v=(zero,sp.Integer(row[1]))
  else:
   a,b=vals[row[1]],vals[row[2]]
   if tag=='mul':v=(tuple(x+y for x,y in zip(a[0],b[0])),sp.expand(a[1]*b[1]))
   elif key(a)>key(b):v=a
   elif key(a)<key(b):v=(b[0],-b[1] if tag=='sub' else b[1])
   else:v=(a[0],sp.expand(a[1]-b[1] if tag=='sub' else a[1]+b[1]))
  need(v[1]!=0,'nonzero leading coefficient at gate '+str(i));vals.append(v)
 ex,co=vals[packet['output']];short=packet['short_index']
 want_ex={'j':588,'w':70 if short else 112,'v':112 if short else 154,'h':42,'s':16,'r':12,'c':40,'T':2}
 need(dict(zip(order,ex))=={n:want_ex.get(n,0) for n in order},'selected leading monomial')
 two,three=(960,665) if short else (1002,707)
 expected=2**two*3**three*coeff['beta']**588
 need(sp.expand(co-expected)==0,'actual exact leading coefficient')
 need(sum(ex)==packet['exact_degree'],'attained degree')
 return {'degree':sum(ex),'monomial':want_ex,'coefficient':f'2^{two} * 3^{three} * beta^588','all_gates_checked':len(vals),'nonzero_at_authentic_beta':True}

def algebra():
 A,c,U,P,b,f,H,K,T,Dt,D,s,r,p0,Delta,q,v,w=sp.symbols('A c U P b f H K T Dt D s r p0 Delta q v w')
 checks={}
 def verify(name,expr):
  need(sp.expand(expr)==0,name);checks[name]=True
 Df=1+Delta*U**2*P;Q=Delta**2*U**2*P;V=Df*b-c;Da=(Q-1)*(Q*V**2-1)
 verify('Df remainder modulo P',Df.subs(P,0)-1)
 verify('Da remainder modulo P',Da.subs(P,0)-1)
 # Free f is the Df coordinate: the verified prefix gives Q=Delta(f-1).
 dfQ=(A**2-1)*(f-1);dfV=f*b-c
 dfDa=(dfQ-1)*(dfQ*dfV**2-1)
 verify('Da remainder modulo Df',dfDa.subs(f,0)-A**2*(1+(A**2-1)*c**2))
 d=sp.Symbol('d')
 verify('Df remainder modulo A',(1+Delta*(r*c*c*A*d)**2*P).subs(A,0)-1)
 verify('Df remainder modulo Dm',(1+Delta*(r*c*c*A*d)**2*P).subs(d,0)-1)
 verify('coprime product evaluator',Dt+D*(2*Dt*s)**2-Dt*(1+4*D*Dt*s*s))
 verify('strong saturation',(1+Delta*U*U*P).subs(P,p0*p0)-(1+Delta*(U*p0)**2))
 verify('auxiliary saturation',(4*U*P*T).subs(P,p0*p0)-4*(U*p0)*(p0*T))
 zc=H*T+K;Ac=(zc*zc+3*H*H)*(zc**3-19*H**3)
 verify('carrier modulo H',Ac.subs(H,0)-K**5)
 X=q*(12*w+4);Y=(2*v+1)*q**3
 verify('smaller index modulus',2*X*Y*Y-4*q**4*(6*w+2)*(2*v+1)**2*q**3)
 xx,aa,cc=sp.symbols('xx aa cc')
 verify('short projector',(4*aa+3)*xx*cc-2*(xx*(xx+2*aa*cc)-1)-(xx*(3*cc-2*xx)+2))
 # Derive the entire highest homogeneous part independently of the DAG.
 q0,X0,Y0,k0,rr,ss,cc,tt=sp.symbols('q0 X0 Y0 k0 rr ss cc tt')
 a0=X0*Y0;P0=-48*q0**2*X0**4*Y0**10*k0**6*ss**2
 U0=rr*a0**3*cc**4;S0=4*ss*rr*a0
 Df0=a0*a0*U0*U0*P0;Q0=a0**4*U0*U0*P0
 V0=4*a0*a0*U0**3*P0**2*tt;Cy0=Q0*V0*V0
 expected=2**36*3**7*q0**14*X0**70*Y0**112*k0**42*ss**16*rr**12*cc**40*tt**2
 verify('whole highest homogeneous form',-S0*S0*P0*Df0*Cy0-expected)
 return checks

def coefficients():
 loc=ROOT/'../norm/coefficients';binding=json.loads((loc/'BINDING.json').read_text());values={};checks=[]
 need(list(binding['payloads'])==PORTS,'coefficient port ordering')
 for name,info in binding['payloads'].items():
  raw=gzip.decompress((loc/info['file']).read_bytes());value=int.from_bytes(raw,'little')
  need(len(raw)==info['raw_bytes'],'coefficient byte count '+name)
  need(hashlib.sha256(raw).hexdigest()==info['raw_sha256'],'coefficient digest '+name)
  need(value.bit_length()==info['bits'],'coefficient bit count '+name)
  values[name]=value;checks.append({'port':name,'bits':info['bits'],'sha256':info['raw_sha256']})
 need(values['beta']==2**1064921-1,'authentic beta')
 need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'authentic cones')
 return checks

def controls(packet):
 controls=[]
 for name in ['U','P','b','S','Ac']:
  damaged=copy.deepcopy(packet);idx=damaged['named_registers'][name];row=damaged['nodes'][idx]
  need(row[0] in ['mul','add','sub'],'mutation target arithmetic')
  row[0]='add' if row[0]=='mul' else 'mul'
  try:local_checks(damaged)
  except ValueError:controls.append(name)
  else:raise ValueError('unrejected mathematical corruption '+name)
 return {'rejected_modified_local_formulas':controls}

def main():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for name,info in pins['files'].items():
  raw=(ROOT/name).read_bytes()
  need(len(raw)==info['bytes'] and hashlib.sha256(raw).hexdigest()==info['sha256'],'source pin '+name)
 result={'status':'PASS','scope':'Finite polynomial, coefficient, source-binding and algebra checks; ordinary semantic proof remains separate.',
         'source_pins':len(pins['files']),'coefficient_payloads':coefficients(),'universal_identities':algebra(),'equations':[]}
 for degree in [966,882]:
  p=json.loads((ROOT/f'product11_degree{degree}.json').read_text())
  need(p['coefficient_binding']=='../norm/coefficients/BINDING.json','complete shared binding')
  result['equations'].append({'name':p['name'],'topology':topology(p),'literal_formulas':local_checks(p),'leading':exact_leading(p),'controls':controls(p)})
 output=ROOT/('CHECK.json' if __debug__ else 'CHECK_OPTIMIZED.json')
 output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','equations':[{k:r[k] for k in ['name','topology','leading','controls']} for r in result['equations']]},indent=2))
if __name__=='__main__':main()

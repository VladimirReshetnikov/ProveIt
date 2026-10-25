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

ROOT=Path(__file__).resolve().parent.parent
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
       ('D','Budget-4'),('s2','s'),('guard_scale','Dt*s'),
       ('P','Dt*(1+D*Dt*s*s)'),('U','r*c*c'),('UP','U*P'),('strong','Delta*U*U*P'),
       ('Df','1+Delta*U*U*P'),('Q','Delta*Delta*U*U*P'),('delta','Q-1'),
       ('b','c-R+4*U*P*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
       ('K','X*(3*c-2*X)+2'),('H2','H*H'),('H3','H**3'),
       ('S','s*r*H'),('S2','S*S'),('zc','H*T+K'),('zc2','zc*zc'),
       ('Ac','(zc*zc+3*H*H)*(zc**3-19*H**3)'),
       ('Z','S*(n+V)-Ac'),('Aux','S*S*Cy'),('Guard','S*S*P*Df'),('Inner','delta*(Z*Z-Guard)-Aux'),('output','Inner*Inner-4*delta*Aux*Guard')]
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
 need(degree[packet['output']]==packet['syntactic_degree_bound'],'syntactic bound consistency')
 return {'live_nodes':len(nodes),'operations':want,'counts':dict(counts),'syntactic_upper_bound':degree[packet['output']],'certified_exact_degree':packet['exact_degree']}

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
  if i==packet['named_registers']['Inner']:
   # The universal centering identity is checked in algebra().
   # Its unique highest term is -S^2 V^2. Independent register degrees
   # prove the competing terms strictly lower, not just a test ray.
   nm=packet['named_registers']; ss=vals[nm['S']]; vv=vals[nm['V']]; dd=vals[nm['delta']]
   sd=sum(ss[0]);vd=sum(vv[0]);delta_degree=sum(dd[0]);wd=35
   center_degree=2*sd+2*vd
   competitor_degrees=[delta_degree+2*wd,delta_degree+sd+vd+wd,2*sd,delta_degree+sum(vals[nm['Guard']][0])]
   need(max(competitor_degrees)<center_degree,'unique centered leading term')
   v=(tuple(2*a+2*b for a,b in zip(ss[0],vv[0])),-ss[1]**2*vv[1]**2)
  need(v[1]!=0,'nonzero leading coefficient at gate '+str(i));vals.append(v)
 ex,co=vals[packet['output']];short=packet['short_index']
 want_ex={'j':552,'w':50 if short else 98,'v':98 if short else 146,'h':48,'s':20,'r':16,'c':24,'T':2}
 need(dict(zip(order,ex))=={n:want_ex.get(n,0) for n in order},'selected leading monomial')
 two,three=(876,602) if short else (924,650)
 expected=-2**two*3**three*coeff['beta']**552
 need(sp.expand(co-expected)==0,'actual exact leading coefficient')
 need(sum(ex)==packet['exact_degree'],'attained degree')
 return {'degree':sum(ex),'monomial':want_ex,'coefficient':f'-2^{two} * 3^{three} * beta^552','all_gates_checked':len(vals),'nonzero_at_authentic_beta':True}

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
 verify('coprime product evaluator',Dt+D*(Dt*s)**2-Dt*(1+D*Dt*s*s))
 verify('strong saturation',(1+Delta*U*U*P).subs(P,p0*p0)-(1+Delta*(U*p0)**2))
 verify('auxiliary saturation',(4*U*P*T).subs(P,p0*p0)-4*(U*p0)*(p0*T))
 zc=H*T+K;Ac=(zc*zc+3*H*H)*(zc**3-19*H**3)
 verify('carrier modulo H',Ac.subs(H,0)-K**5)
 X=q*(12*w+4);Y=(2*v+1)*q**3
 verify('smaller index modulus',2*X*Y*Y-4*q**4*(6*w+2)*(2*v+1)**2*q**3)
 xx,aa,cc=sp.symbols('xx aa cc')
 verify('short projector',(4*aa+3)*xx*cc-2*(xx*(xx+2*aa*cc)-1)-(xx*(3*cc-2*xx)+2))
 # Full denominator-cleared two-root identity and its integral center.
 Z,S,DeltaQ,PP,FF,CY,VV,W=sp.symbols('Z S DeltaQ PP FF CY VV W')
 Q=DeltaQ+1
 scalar=(DeltaQ*(Z**2-S**2*PP*FF)-S**2*CY)**2-4*DeltaQ*S**4*CY*PP*FF
 verify('zero-center obstruction',scalar.subs(Z,0)-S**4*(CY-DeltaQ*PP*FF)**2)
 centered=(DeltaQ*(Z**2-S**2*PP*FF)-S**2*CY).subs(Z,W+S*VV).subs(CY,Q*VV**2-1)
 verify('complete center identity',centered-(DeltaQ*W**2+2*DeltaQ*S*VV*W+S**2*(1-VV**2-DeltaQ*PP*FF)))
 zz,aa,bb=sp.symbols('zz aa bb')
 verify('two radical norm',(zz**2-aa-bb)**2-4*aa*bb-((zz**2+aa-bb)**2-4*zz**2*aa))
 q0,X0,Y0,k0,rr,ss,cc,tt=sp.symbols('q0 X0 Y0 k0 rr ss cc tt')
 a0=X0*Y0;P0=-4*q0**2*X0**4*Y0**10*k0**6*ss**2
 U0=rr*cc**2;S0=4*ss*rr*a0
 Df0=a0*a0*U0*U0*P0;Q0=a0**4*U0*U0*P0
 V0=4*a0*a0*U0**3*P0**2*tt;Cy0=Q0*V0*V0
 expected=-2**30*q0**16*X0**50*Y0**98*k0**48*ss**20*rr**16*cc**24*tt**2
 verify('whole highest homogeneous form',-4*Q0*S0**4*Cy0*P0*Df0-expected)
 return checks

def coefficients():
 loc=ROOT/'coefficients';binding=json.loads((loc/'BINDING.json').read_text());values={};checks=[]
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
 for name in ['U','P','b','S','Ac','Aux','Guard','Inner','output']:
  damaged=copy.deepcopy(packet);idx=damaged['output'] if name=='output' else damaged['named_registers'][name];row=damaged['nodes'][idx]
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
 # Exhaust the complete residue rings used by the new parity lemma.
 residues={(-q*q*k*k-4*q*q*eta*eta)%16 for q in range(0,16,2) for k in range(16) for eta in range(16)}
 need(residues=={0,12},'Budget modulo sixteen')
 need({(b-4)%16 for b in residues}=={8,12},'guard nonsquare residues')
 need(not ({8,12}&{x*x%16 for x in range(16)}),'guard never square')
 need(all((1+ell*(ell+1)*k*k)%8==1 for ell in range(0,64,8) for k in range(8)),'Dt modulo eight')
 result={'status':'PASS','parity_lemma':{'Budget_mod16':sorted(residues),'D_mod16':[8,12],'positive_canonical_D_minimum':60},'scope':'Finite polynomial, coefficient, source-binding and algebra checks; ordinary semantic proof remains separate.',
         'source_pins':len(pins['files']),'coefficient_payloads':coefficients(),'universal_identities':algebra(),'equations':[]}
 for degree in [810]:
  p=json.loads((ROOT/'two_root'/f'two_root11_degree{degree}.json').read_text())
  need(p['coefficient_binding']=='../coefficients/BINDING.json','complete shared binding')
  result['equations'].append({'name':p['name'],'topology':topology(p),'literal_formulas':local_checks(p),'leading':exact_leading(p),'controls':controls(p)})
 output=ROOT/'two_root'/('CHECK.json' if __debug__ else 'CHECK_OPTIMIZED.json')
 output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','equations':[{k:r[k] for k in ['name','topology','leading','controls']} for r in result['equations']]},indent=2))
if __name__=='__main__':main()

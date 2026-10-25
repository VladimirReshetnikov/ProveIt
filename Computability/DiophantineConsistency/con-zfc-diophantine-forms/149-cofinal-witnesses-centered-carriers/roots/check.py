#!/usr/bin/env python3
"""Independent polynomial cuts, full leading forms, signed identities and mutations.
Never imports build.py or circuit.py. Retained audit formulas are inert AST data.
"""
import ast,copy,gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(b,m):
 if not b:raise ValueError(m)
def literal(p,name):
 for n in ast.parse(p.read_text()).body:
  if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id==name:return ast.literal_eval(n.value)
 raise ValueError('missing literal '+name)
CASES={}
for tag,part,degree,counts,mon,coef in [
 ('integer14_degree88_ops110','',88,{'mul':64,'add':23,'sub':23},dict(j=56,w=8,v=8,z=5,r=2,c=4,f=4,y=1),'-2**87*3**64*beta**56'),
 ('integer13_degree156_ops117','thirteen/',156,{'mul':70,'add':23,'sub':24},dict(j=106,w=14,v=14,z=9,r=4,c=8,y=1),'2**171*3**120*beta**106')]:
 path=ROOT/('inherited/baseline/'+part+'review/audit.py')
 vs=literal(path,'V');fs=literal(path,'FORMS');forms=[]
 drop={'carrier','UG','U2','ga','db','fc','gc','inner','N','P','Dt'}
 for n,f in fs:
  if n in drop:continue
  if n in ('strong','auxiliary'):f='('+f+')+1'
  forms.append((n,f))
 forms += [('Dt','1+L*L+L*k'),('U2','U*U'),('ga','G*U2'),('db','4*Dt*U2')]
 if degree==88:forms += [('N','Z**4-2*Z*Z*ga-2*Z*Z*db+ga*ga-2*ga*db+db*db'),('P','N*strong*auxiliary+strong*auxiliary-1')]
 else:forms += [('fc','16*Fs*U2'),('gad','ga*db'),('gab','ga+db'),('Z2','Z*Z'),('inner','Z2*Z2-2*Z2*gab-2*Z2*fc+gab*gab-2*gab*fc+fc*fc-4*gad'),('N','inner*inner-64*gad*fc*Z2'),('P','N*auxiliary+auxiliary-1')]
 CASES[tag]={'variables':vs,'forms':forms,'degree':degree,'counts':counts,'monomial':mon,'coefficient':coef}

def validate(tag,g):
 c=CASES[tag];vs=c['variables'];forms=c['forms'];sy={n:S.Symbol(n) for n in set(vs+PORTS+[n for n,_ in forms])}
 need(g['variables']==vs and g['variable_count']==len(vs),'variables')
 need(g['fixed_numerals']==PORTS,'ports');need(g['coefficient_binding']=='inherited/baseline/coefficients/BINDING.json','binding')
 nodes=g['nodes'];cuts={};covered=set()
 for i,n in enumerate(nodes):
  need(n[0] in ['integer','variable','coefficient','add','sub','mul'],'node type')
  if n[0] in ['add','sub','mul']:need(len(n)==3 and all(type(k)==int and 0<=k<i for k in n[1:]),'topology')
 def rec(i,memo):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  covered.add(i);n=nodes[i];op=n[0]
  if op=='integer':v=S.Integer(n[1])
  elif op in ('variable','coefficient'):v=sy[n[1]]
  else:
   a,b=rec(n[1],memo),rec(n[2],memo);v=a+b if op=='add' else a-b if op=='sub' else a*b
  memo[i]=v;return v
 for n,f in forms:
  i=g['named_registers'][n];need(S.expand(rec(i,{})-S.sympify(f,locals=sy))==0,'incorrect cut '+n);cuts[i]=sy[n]
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i)
  if nodes[i][0] in ['add','sub','mul']:
   walk(nodes[i][1]);walk(nodes[i][2])
 need(g['output']==g['named_registers']['P'],'output');walk(g['output'])
 need(seen==covered==set(range(len(nodes))),'liveness and cut coverage')
 for op,names in [('variable',vs),('coefficient',PORTS)]:need({n[1] for n in nodes if n[0]==op}==set(names),'live '+op)
 counts=Counter(n[0] for n in nodes if n[0] in ['add','sub','mul'])
 need(counts==c['counts'] and g['operation_counts']==c['counts'] and g['operations']==sum(counts.values()),'counts')
 return sy

def leading(tag,g,sy):
 c=CASES[tag];top=[];deg=[]
 for n in g['nodes']:
  op=n[0]
  if op=='integer':d=0;t=S.Integer(n[1])
  elif op=='variable':d=1;t=sy[n[1]]
  elif op=='coefficient':d=0;t=sy[n[1]]
  else:
   i,j=n[1:]
   if op=='mul':d=deg[i]+deg[j];t=top[i]*top[j]
   elif deg[i]>deg[j]:d=deg[i];t=top[i]
   elif deg[j]>deg[i]:d=deg[j];t=top[j] if op=='add' else -top[j]
   else:d=deg[i];t=S.expand(top[i]+top[j] if op=='add' else top[i]-top[j])
  need(t!=0,'unresolved top cancellation');top.append(t);deg.append(d)
 need(deg[g['output']]==g['exact_degree']==c['degree'],'degree')
 q=6*sy['beta']*sy['j'];x=12*q*sy['w'];y=sy['v'];r=q**4*sy['z']-12*q**3*sy['w']*sy['C'];u=8*q**3*x*y
 expected=u**4*r**4*(q**8+4*x*x*y**4)**2 if c['degree']==88 else 256*u**8*r**8*(q**8+x*x*y**4)**4
 need(S.expand(top[g['named_registers']['N']]-expected)==0,'complete norm top')
 p=S.Poly(S.expand(top[g['output']]),*[sy[v] for v in c['variables']]);cf=p.coeff_monomial(tuple(c['monomial'].get(v,0) for v in c['variables']))
 need(S.expand(cf-S.sympify(c['coefficient'],locals=sy))==0,'actual coefficient')
 return {'degree':c['degree'],'monomial':c['monomial'],'coefficient':c['coefficient'],'complete_output_top_terms':len(p.terms())}

def identities():
 Z,U,L,k,G,Fs=S.symbols('Z U L k G Fs');D=1+L*(L+k);b=2*L+k
 carrier=lambda z:(z+U*k)**2+4*U*(L*z-U)
 need(S.expand(carrier(Z-U*b)-(Z*Z-4*U*U*D))==0,'centered carrier shear')
 ga=U*U*G;db=4*U*U*D;fc=16*U*U*Fs
 old2=(carrier(Z-U*b)-ga)**2-16*U**4*G*D
 new2=(Z*Z-ga-db)**2-4*ga*db
 need(S.expand(old2-new2)==0,'whole two-root shear norm')
 oldinner=(carrier(Z-U*b)-ga-fc)**2-4*(ga*fc+db*(ga+fc))
 newinner=(Z*Z-ga-db-fc)**2-4*(ga*db+ga*fc+db*fc)
 old3=oldinner**2-64*ga*db*fc*(carrier(Z-U*b)+db)
 new3=newinner**2-64*ga*db*fc*Z*Z
 need(S.expand(oldinner-newinner)==0 and S.expand(old3-new3)==0,'whole three-root shear norm')
 x,a,d,f=S.symbols('x a d f');prod=1
 for signs in itertools.product([-1,1],repeat=3):prod*=x-signs[0]*a-2*signs[1]*d-4*signs[2]*f
 norm=((x*x-a*a-4*d*d-16*f*f)**2-4*(4*a*a*d*d+16*a*a*f*f+64*d*d*f*f))**2-4096*a*a*d*d*f*f*x*x
 need(S.expand(prod-norm)==0,'all signed factors')
 # Soundness carrier identity and inverse affine shifts, with integral root tau.
 g,tau,ff,n=S.symbols('g tau ff n')
 need(S.expand(carrier(U*(2*tau-b))-4*U*U*(tau*tau-D))==0,'restored carrier')
 need(S.expand((n-b-g-4*ff)+b+g+4*ff-n)==0,'signed inverse shift')
 rho,A=S.symbols('rho A');norm2=(rho*rho-A-G)**2-4*A*G
 need(S.expand((rho*rho+G-A)**2-4*rho*rho*G-norm2)==0,'rational extraction identity')
 # Exact top-form rigidity at arbitrary degree-nine shear H; no finite search substituted for proof.
 H,R,q,ell=S.symbols('H R q ell');gg=-4*R*R*q**8;dd=4*ell*ell
 inner=(H*H-gg-dd)**2-4*gg*dd
 need(S.expand(inner-((H*H+4*R*R*q**8-4*ell*ell)**2+(8*R*q**4*ell)**2))==0,'degree rigidity SOS')
 residue=0
 for aa,ii,ff in itertools.product(range(8),repeat=3):
  need((ff*ff-(aa*aa-1)*ii*ii-1)%4!=2,'strong residue');residue+=1
 # Finite diagnostics include G=0 in the two-root lift and negative signs.
 lifts=0
 for gg,tt,ff in itertools.product(range(-5,6),repeat=3):
  rr=gg+2*tt+4*ff
  if gg%2:
   need(int(norm.subs({x:rr,a:gg,d:tt,f:ff}))==0,'signed triple diagnostic');lifts+=1
 return {'exact_identities':8,'residue_cases':residue,'signed_triple_lifts':lifts,'all_signs_factorization':True,'zero_carrier_boundary':'Full proof uses odd/even square-class extraction; no root is discarded by division.'}

def main():
 pins=json.loads((ROOT/'INHERITED_PINS.json').read_text())
 for p,h in pins.items():need(hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,'inherited bytes '+p)
 binding=json.loads((ROOT/'inherited/baseline/coefficients/BINDING.json').read_text())
 trusted=literal(ROOT/'inherited/baseline/thirteen/review/audit.py','TRUSTED_RAW_SHA256');rawbytes=0
 for port in PORTS:
  b=binding['payloads'][port];raw=gzip.decompress((ROOT/'inherited/baseline/coefficients'/b['file']).read_bytes());rawbytes+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==b['raw_sha256']==trusted[port],'coefficient hash '+port)
  val=int.from_bytes(raw,'little');need(val.bit_length()==b['bits'],'coefficient bits')
  if port=='beta':need(val==2**1064921-1,'beta')
 rows=[]
 for tag,c in CASES.items():
  g=json.loads((ROOT/(tag+'.json')).read_text());sy=validate(tag,g);ld=leading(tag,g,sy);mutations=0
  for i,n in enumerate(g['nodes']):
   if n[0] not in ['add','sub','mul']:continue
   bad=copy.deepcopy(g);bad['nodes'][i][0]='sub' if n[0]=='add' else 'add'
   try:validate(tag,bad)
   except ValueError:mutations+=1
   else:raise ValueError('accepted mutation '+str(i))
  rows.append({'name':tag,'variables':len(c['variables']),'operations':sum(c['counts'].values()),'operation_counts':c['counts'],**ld,'rejected_gate_mutations':mutations,'sha256':hashlib.sha256((ROOT/(tag+'.json')).read_bytes()).hexdigest()})
 out={'status':'PASS','optimized':not __debug__,'rows':rows,'inherited_files_pinned':len(pins),'six_coefficient_raw_bytes':rawbytes,'local_identities':identities(),'boundary':'Finite algebra and metrics only; signed/native/refutation theorem remains retained ordinary proof dependency.'}
 path=ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
if __name__=='__main__':main()

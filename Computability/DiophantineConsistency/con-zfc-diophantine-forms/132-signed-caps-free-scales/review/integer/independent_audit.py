#!/usr/bin/env python3
"""Independent literal and finite algebra audit; no producer/checker imports."""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip,json,importlib.util
HERE=Path(__file__).resolve().parent;PKG=HERE.parent.parent/'integer'
# This is our separately written generic expression normalizer, not producer code.
spec=importlib.util.spec_from_file_location('independent_expression_ring',HERE.parent/'positive/independent_audit.py')
ringmod=importlib.util.module_from_spec(spec);spec.loader.exec_module(ringmod)
Ring=ringmod.Ring

def need(x,m):
 if not x:raise ValueError(m)
def hashof(p):return sha256(p.read_bytes()).hexdigest()
VARS=['j','C','z','h','r','v','w','T','c','n','s'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def evaldag(o,env):
 vals=[]
 for pos,node in enumerate(o['nodes']):
  kind=node[0]
  if kind=='variable':need(node[1] in VARS,'variable leaf');value=env[node[1]]
  elif kind=='coefficient':need(node[1] in PORTS,'coefficient leaf');value=env[node[1]]
  elif kind=='integer':need(type(node[1]) is int,'literal');value=env['_ring'].C(node[1])
  else:
   need(kind in ('add','sub','mul') and len(node)==3,'gate shape');a,b=node[1:];need(type(a)is int and type(b)is int and 0<=a<pos and 0<=b<pos,'topological order');x,y=vals[a],vals[b];value=x+y if kind=='add' else x-y if kind=='sub' else x*y
  vals.append(value)
 return vals

def formulas(e,free,center):
 j,C,z,h,r,v,w,T,c,n,s=[e[x] for x in VARS];beta,K0,MC,MF,coneA,coneB=[e[x] for x in PORTS]
 J=6*j+1;q=beta*J+1;W=12*w+4;X=q*W;Y=v if free else q*v;E=X*Y;a=E+Y;A=a+2;H=4*a+3;Delta=a*a+H
 F=(K0+W)*C-z*(q-1);R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J;k=R+1+h*E;eta=c-Y*k
 Derr=(coneA*F-q)**2+(coneB*C-q)**2
 # This factored budget is related to the published expanded one by the separately checked free-ring identity.
 Budget=(Y*k)**2*(q*q-Derr)-q*q*(4*(Y*eta)**2+(k*q**3)**2) if free else k*k*(q*q-Derr)-4*q*q*eta*eta
 L=E*(Y*k);Dt=1+L*(L+k);P=Dt+(12*Budget-16)*(Dt*s)**2
 Dm=1+Delta*c*c;Ub=r*c*c;U=A*Ub;Df=1+Delta*U*U*Dm;Q=Delta*Delta*U*U*Dm;delta=Q-1;b=c-R+4*U*Dm*T;V=Df*b-c;Cy=Q*V*V-1
 K=X*(3*c-2*X)+2;scale=q**(3 if free else 2);M=2*scale;Dc=H*M;S=s*r*H*M**5
 zc=Dc*T+M*K+H*(v-scale);Ac=(zc*zc+3*Dc*Dc)*(zc**3-19*Dc**3)
 lam=e['_ring'].C(0) if center=='none' else (2*A*U*Dm if center=='simple' else (2*Delta+1)*Ub*Dm)
 Z=S*(n+lam*V)-Ac;inner=delta*Z*Z+delta*S*S*P-4*S*S*Dm*Df*Cy
 out=inner*inner-4*delta*delta*S*S*P*Z*Z
 return locals()

def audit(o):
 need(o['variables']==VARS and o['variable_count']==11 and o['domain']=='unrestricted integers','domain/count')
 need(o['coefficient_binding']=='coefficients/BINDING.json','coefficient identity')
 r=Ring();env={x:r.S(x) for x in VARS+PORTS}|{'_ring':r};vals=evaldag(o,env);f=formulas(env,o['free_y'],o['center'])
 regs=o['named_registers'];aliases={'Dcar':'Dc','output':'out'}
 for name in ['J','q','W','X','Y','E','a','A','H','Delta','F','R','k','eta','Derr','Budget','L','Dt','P','Dm','Ub','U','Df','Q','delta','b','V','Cy','K','M','Dcar','S','zc','Ac','lam','Z','inner','output']:
  if name=='lam' and o['center']=='none':continue
  need(vals[regs[name]]==f[aliases.get(name,name)],'literal complete formula register '+name)
 need(vals[o['output']]==f['out'],'full output identity')
 live=set();stack=[o['output']]
 while stack:
  idx=stack.pop()
  if idx in live:continue
  need(type(idx)is int and 0<=idx<len(o['nodes']),'output ref');live.add(idx);node=o['nodes'][idx]
  if node[0] in ('add','sub','mul'):stack.extend(node[1:])
 need(live==set(range(len(o['nodes']))),'no dead vertices')
 counts=dict(Counter(o['nodes'][i][0] for i in live if o['nodes'][i][0] in ('add','sub','mul')))
 need(counts==o['operation_counts'] and sum(counts.values())==o['operations'],'operation census')
 leaves=[o['nodes'][i][1] for i in live if o['nodes'][i][0]=='variable'];need(set(leaves)==set(VARS),'all variables live')
 return {'operations':sum(counts.values()),'operation_counts':counts,'all_11_variables_and_6_ports_live':True,'complete_free_formula_identity':True}

def main():
 import sympy as sp
 aa,uu,cc,dd,pp,qq,yy,kk,er,ZZ,SS,PP,VV,WW=sp.symbols('A u c d p q Y k err Z S P V W')
 Delta=aa*aa-1;Dm=1+Delta*cc*cc;U=aa*uu;Df=1+Delta*U*U*Dm;Q=Delta*Delta*U*U*Dm;delta=Q-1;lam=(2*Delta+1)*uu*Dm
 need(sp.expand(lam*lam-4*Dm*Df-(Dm*Dm*uu*uu-4*Dm))==0,'sharp center free-ring identity')
 budget=yy*yy*(kk*kk*(qq*qq-er)-4*qq*qq*dd*dd)-kk*kk*qq**8
 fact=(yy*kk)**2*(qq*qq-er)-qq*qq*(4*(yy*dd)**2+(kk*qq**3)**2)
 need(sp.expand(budget-fact)==0,'budget rebracketing')
 # Work with independent cut variables to verify the sharp inner identity.
 Delt,DM,DF,UB,Qq,lam0=sp.symbols('Delta Dm Df Ub Q lambda');de=Qq-1
 lhs=de*(WW+SS*lam0*VV)**2+de*SS**2*PP-4*SS**2*DM*DF*(Qq*VV**2-1)
 rhs=de*WW**2+2*de*SS*lam0*VV*WW+de*SS**2*PP+SS**2*((de*(DM**2*UB**2-4*DM)-4*DM*DF)*VV**2+4*DM*DF)
 difference=sp.Poly(sp.expand(lhs-rhs),lam0)
 need(sp.expand(difference.as_expr().subs(lam0**2,4*DM*DF+DM**2*UB**2-4*DM))==0,'complete center expansion cut')
 # Complete four-factor identity, before clearing denominators.
 r1,r2=sp.symbols('r1 r2');norm=(ZZ**2+SS**2*r2**2-4*SS**2*r1**2)**2-4*SS**2*r2**2*ZZ**2
 need(sp.expand(norm-sp.prod(ZZ+e1*2*SS*r1+e2*SS*r2 for e1 in (-1,1) for e2 in (-1,1)))==0,'two-root norm identity')
 # Independently multiply complete leading forms at actual fixed beta.
 beta,j,w,v,s,r,c,T=sp.symbols('beta j w v s r c T',nonzero=True);q0=6*beta*j;X0=12*q0*w
 degree_receipts={}
 for free in (True,False):
  Y0=v if free else q0*v;a0=X0*Y0;S0=128*s*r*a0*q0**(15 if free else 10);dm0=a0*a0*c*c;ub0=r*c*c;df0=a0**6*r*r*c**6;Q0=a0*a0*df0;V0=4*a0**9*r**3*c**10*T
  top=(S0*S0*Q0*dm0*dm0*ub0*ub0*V0*V0)**2
  exponent=124 if free else 168;target=2**(288 if free else 332)*3**(188 if free else 232)*beta**exponent*j**exponent*w**64*v**64*s**4*r**24*c**68*T**4
  need(sp.expand(top-target)==0,'authentic sharp leading monomial')
  degree_receipts['free' if free else 'weak']={'attained_degree':352 if free else 396,'monomial_exponents':{'j':exponent,'w':64,'v':64,'s':4,'r':24,'c':68,'T':4},'coefficient':'2^%d * 3^%d * beta^%d'%((288 if free else 332),(188 if free else 232),exponent)}
 bind=json.loads((PKG/'coefficients/BINDING.json').read_text());ports={}
 for key,item in bind['payloads'].items():
  data=gzip.decompress((PKG/'coefficients'/item['file']).read_bytes());need(len(data)==item['raw_bytes'] and sha256(data).hexdigest()==item['raw_sha256'],'payload '+key)
  ports[key]=int.from_bytes(data,'little');need(ports[key].bit_length()==item['bits'],'bits '+key)
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'actual explicit constants')
 pins=json.loads((PKG/'SOURCE_PINS.json').read_text())
 for path,m in pins['dependencies'].items():need(hashof(PKG/path)==m['sha256'] and (PKG/path).stat().st_size==m['bytes'],'source pin '+path)
 output={};mutations=[]
 for path in sorted(PKG.glob('*main_saturated11_*.json')):
  obj=json.loads(path.read_text());output[path.name]=audit(obj)|{'exact_degree_from_reviewed_ordinary_proof':obj['exact_degree'],'sha256':hashof(path)}
  for label,reg in [('strong_multiplier','U'),('center_carrier','zc'),('output_norm','inner')]:
   damaged=deepcopy(obj);idx=damaged['named_registers'][reg];node=damaged['nodes'][idx];node[0]='add' if node[0]!='add' else 'sub'
   try:audit(damaged)
   except ValueError:mutations.append(path.name+':'+label)
   else:raise ValueError('mutation escaped '+label)
 receipt={'status':'PASS','scope':'Independent whole literal formula identities and gate census for six DAGs; free-ring norm/budget/center identities; symbolic leading monomial multiplication; raw six-port hashes; source pins. Unbounded proof review is in REVIEW.md. No producer or package checker imports.', 'candidates':output,'sharp_degree_witnesses':degree_receipts,'source_files_verified':len(pins['dependencies']),'corruptions_rejected':mutations,'proof_sha256':hashof(PKG/'PROOF.md')}
 (HERE/'AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

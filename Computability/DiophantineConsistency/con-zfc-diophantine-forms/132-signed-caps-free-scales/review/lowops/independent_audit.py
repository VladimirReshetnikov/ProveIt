#!/usr/bin/env python3
"""Independent low-ops audit. Imports only our earlier generic ring, never producer code."""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip,json,importlib.util
HERE=Path(__file__).resolve().parent;PKG=HERE.parent.parent/'integer_lowops'
spec=importlib.util.spec_from_file_location('own_generic_ring',HERE.parent/'positive/independent_audit.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
Ring=mod.Ring
VARS=['j','C','z','h','r','v','w','T','c','n','s'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(x,m):
 if not x:raise ValueError(m)
def hashof(p):return sha256(p.read_bytes()).hexdigest()
def formulas(e,short):
 j,C,z,h,r,v,w,T,c,n,s=[e[x] for x in VARS];beta,K0,MC,MF,ca,cb=[e[x] for x in PORTS]
 J=6*j+1;qm=beta*J;q=qm+1;q2=q*q;q3=q**3;W=12*w+4;X=q*W;Y=(2*v+1)*q3;E=X*Y;a=E+Y;A=a+2;H=4*a+3;Delta=a*a+H
 F=(K0+W)*C-z*(q-1);R=(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J;q24=4*q2
 k=R+1+h*(4*q**4 if short else E);Yk=Y*k;eta=c-Yk;Derr=(ca*F-q)**2+(cb*C-q)**2;Budget=k*k*(q*q-Derr)-4*q*q*eta*eta
 L=E*Yk;Dt=1+L*(L+k);D4=12*Budget-16;Pg=Dt*s;P=Dt+D4*Pg*Pg;c2=c*c;Dm=1+Delta*c*c;BP=Dm*P;U=A*r*c*c;UBP=U*BP;strong=Delta*U*U*BP;Df=1+strong;Q=Delta*strong;delta=Q-1
 V=Df*(c-R+4*U*BP*T)-c;Cy=Q*V*V-1;K=X*(3*c-2*X)+2;H2=H*H;H3=H**3;zc=H*T+K;zc2=zc*zc;Ac=(zc**2+3*H**2)*(zc**3-19*H**3);S=s*r*H;Z=S*n-Ac;output=delta*Z*Z-S*S*BP*Df*Cy
 return locals()
def audit(o):
 need(o['variables']==VARS and o['variable_count']==11 and o['domain']=='unrestricted integers','domain/variables')
 need(o['coefficient_binding']=='coefficients/BINDING.json','binding')
 ring=Ring();env={x:ring.S(x) for x in VARS+PORTS};vals=[];degrees=[]
 for i,row in enumerate(o['nodes']):
  op=row[0]
  if op=='variable':need(row[1] in VARS,'var');v=env[row[1]];d=1
  elif op=='coefficient':need(row[1] in PORTS,'port');v=env[row[1]];d=0
  elif op=='integer':need(type(row[1])is int,'integer');v=ring.C(row[1]);d=0
  else:
   need(op in ('mul','add','sub') and len(row)==3,'gate');a,b=row[1:];need(type(a)is int and type(b)is int and 0<=a<i and 0<=b<i,'topology');v=vals[a]*vals[b] if op=='mul' else vals[a]+vals[b] if op=='add' else vals[a]-vals[b];d=degrees[a]+degrees[b] if op=='mul' else max(degrees[a],degrees[b])
  vals.append(v);degrees.append(d)
 f=formulas(env,o['short'])
 for name,idx in o['named_registers'].items():need(name in f and vals[idx]==f[name],'independent complete register '+name)
 need(vals[o['output']]==f['output'],'whole equation identity')
 live=set();pending=[o['output']]
 while pending:
  i=pending.pop()
  if i in live:continue
  live.add(i);row=o['nodes'][i]
  if row[0] in ('mul','add','sub'):pending.extend(row[1:])
 need(live==set(range(len(vals))),'dead gate')
 census=dict(Counter(row[0] for row in o['nodes'] if row[0] in ('mul','add','sub')))
 need(census==o['operation_counts'] and sum(census.values())==o['operations']==(110 if o['short'] else 109),'operation count')
 degree=840 if o['short'] else 924
 need(degrees[o['output']]==o['syntactic_degree_bound']==o['exact_degree']==degree,'universal degree upper bound')
 return {'operations':sum(census.values()),'operation_counts':census,'all_vertices_live':True,'full_register_and_output_identity':True,'universal_degree_upper_bound':degree}
def ray(o,ports,weights,p):
 vals=[]
 for row in o['nodes']:
  op=row[0]
  if op=='variable':v=[0,weights[row[1]]%p]
  elif op=='coefficient':v=[ports[row[1]]%p]
  elif op=='integer':v=[row[1]%p]
  else:
   a,b=[vals[i] for i in row[1:]];v=mod.mul(a,b,p) if op=='mul' else mod.add(a,b,p,1 if op=='add' else -1)
  vals.append(v)
 return vals[o['output']]
def top_value(w,beta,short,p):
 q=6*beta*w['j']%p;X=12*q*w['w']%p;Y=2*w['v']*pow(q,3,p)%p;a=X*Y%p
 F=(12*w['w']*w['C']-q*w['z'])%p;k=(4*w['h']*pow(q,4,p)-pow(q,3,p)*F)%p if short else w['h']*a%p
 return pow(2,36,p)*pow(3,7,p)*pow(q,14,p)*pow(X,64,p)*pow(Y,106,p)*pow(k,42,p)*pow(w['s'],16,p)*pow(w['r'],12,p)*pow(w['c'],34,p)*pow(w['T'],2,p)%p

def main():
 import sympy as sp
 # Complete algebraic cofactors, without assuming positivity or prior squareness.
 A,u,c,P,b,z,R,T=sp.symbols('A u c P b z R T');Delta=A*A-1;Dm=1+Delta*c*c;U=A*u;BP=Dm*P
 Df=1+Delta*U*U*BP;Q=Delta*Delta*U*U*BP;de=Q-1;V=Df*(c-R+4*U*BP*T)-c;Cy=Q*V*V-1
 need(sp.rem(sp.Poly(Df-1,P),sp.Poly(BP,P)).is_zero,'Df mod BP')
 # At the strong cut z=Delta U^2 BP, reduction modulo Df means z=-1.
 qred=-Delta;dred=qred-1;vred=-c;cyred=qred*vred*vred-1
 need(sp.expand(dred*cyred-A*A*Dm)==0,'Da modulo Df')
 need(sp.expand(cyred+Dm)==0 and sp.expand(dred+A*A)==0,'strong remainders')
 p0,yo,Z,S=sp.symbols('p0 y Z S');need(sp.expand((p0*U)**2-U*U*p0*p0)==0,'strong scaling')
 need(sp.expand(4*(U*p0)*(p0*T)-4*U*p0*p0*T)==0,'auxiliary scaling')
 # Full leading form, computed from unique dominant terms independently.
 q,X,Y,k,s,r,cc,tt=sp.symbols('q X Y k s r c T');a=X*Y
 bu=-4*q*q*Y*Y*k*k;dt=(X*Y*Y*k)**2;pp=12*bu*dt*dt*s*s;dm=a*a*cc*cc;bp=dm*pp;uu=a*r*cc*cc;df=a*a*uu*uu*bp;qq=a*a*df;vv=4*df*uu*bp*tt;ss=4*s*r*a
 top=-ss*ss*bp*df*qq*vv*vv
 expected=2**36*3**7*q**14*X**64*Y**106*k**42*s**16*r**12*cc**34*tt**2
 need(sp.expand(top-expected)==0,'whole dominant form')
 beta,j,w,v,h=sp.symbols('beta j w v h');q0=6*beta*j;X0=12*q0*w;Y0=2*v*q0**3;a0=X0*Y0
 monomials={}
 for short in (False,True):
  k0=4*h*q0**4 if short else h*a0
  # In short graph h^42 selects this term uniquely from k0_full^42.
  specialized=expected.subs({q:q0,X:X0,Y:Y0,k:k0},simultaneous=True)
  coefficient=2**(918 if short else 960)*3**(635 if short else 677)*beta**564
  target=coefficient*j**564*w**(64 if short else 106)*v**(106 if short else 148)*h**42*s**16*r**12*cc**34*tt**2
  need(sp.expand(specialized-target)==0,'attained authentic coefficient')
  monomials['short' if short else 'native']={'degree':840 if short else 924,'exponents':{'j':564,'w':64 if short else 106,'v':106 if short else 148,'h':42,'s':16,'r':12,'c':34,'T':2},'coefficient':'2^%d * 3^%d * beta^564'%((918 if short else 960),(635 if short else 677))}
 binding=PKG/'coefficients/BINDING.json';need(binding.read_bytes()==(PKG.parent/'integer/coefficients/BINDING.json').read_bytes(),'unchanged authenticated six-port binding')
 ports={};payloads={}
 for key,entry in json.loads(binding.read_text())['payloads'].items():
  data=(PKG/'coefficients'/entry['file']).read_bytes();raw=gzip.decompress(data);need(sha256(raw).hexdigest()==entry['raw_sha256'] and len(raw)==entry['raw_bytes'],'payload hash '+key)
  ports[key]=int.from_bytes(raw,'little');need(ports[key].bit_length()==entry['bits'],'payload bits '+key)
  need(data==(PKG.parent/'integer/coefficients'/entry['file']).read_bytes(),'byte-identical primary payload '+key);payloads[key]={'bits':entry['bits'],'raw_sha256':entry['raw_sha256']}
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'fixed powers')
 pins=json.loads((PKG/'SOURCE_PINS.json').read_text())
 for name,entry in pins['dependencies'].items():need(hashof(PKG/name)==entry['sha256'] and (PKG/name).stat().st_size==entry['bytes'],'source pin '+name)
 output={};mutations=[]
 for path in sorted(PKG.glob('product_main_guard11_*.json')):
  o=json.loads(path.read_text());receipt=audit(o);rays=[]
  for shift in (1,3):
   weights={x:i+shift for i,x in enumerate(VARS)};p=65521;poly=ray(o,ports,weights,p);topc=top_value(weights,ports['beta']%p,o['short'],p)
   need(topc!=0 and len(poly)-1==o['exact_degree'] and poly[-1]==topc,'actual-port full polynomial ray')
   rays.append({'prime':p,'weights':weights,'degree':len(poly)-1,'leading_coefficient':poly[-1]})
  receipt.update({'sha256':hashof(path),'rays':rays});output[path.name]=receipt
  for reg in ('BP','U','V','zc','output'):
   damaged=deepcopy(o);node=damaged['nodes'][damaged['named_registers'][reg]];node[0]='add' if node[0]!='add' else 'sub'
   try:audit(damaged)
   except ValueError:mutations.append(path.name+':'+reg)
   else:raise ValueError('escaped corruption '+reg)
 result={'status':'PASS','scope':'Independent full literal register/output identities, topology/liveness/census, universal degree upper bounds, whole symbolic leading forms and exact authentic coefficients, full modular polynomial lower witnesses, raw payloads and source hashes. Unbounded theorem review is separate. No producer imports or execution.','candidates':output,'attained_monomials':monomials,'ports':payloads,'source_files':len(pins['dependencies']),'corruptions_rejected':mutations,'proof_sha256':hashof(PKG/'PROOF.md')}
 (HERE/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()

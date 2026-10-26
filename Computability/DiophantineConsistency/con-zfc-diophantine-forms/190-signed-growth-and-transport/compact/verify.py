#!/usr/bin/env python3
"""Independent exact checker for the 119-gate degree-190 polynomial.

This does not import the circuit producer. Unbounded arithmetic is in PROOF.md.
"""
from pathlib import Path
from collections import defaultdict,Counter
import json,hashlib,gzip,importlib.util,sys
ROOT=Path(__file__).resolve().parent
def require(p,msg):
 if not p:raise ValueError(msg)
class Ring:
 def __init__(self,n):self.n=n
 def c(self,c):return {(0,)*self.n:c} if c else {}
 def v(self,i):m=[0]*self.n;m[i]=1;return {tuple(m):1}
 def add(self,*ps):
  o=defaultdict(int)
  for p in ps:
   for m,c in p.items():o[m]+=c
  return {m:c for m,c in o.items() if c}
 def scale(self,a,p):return {m:a*c for m,c in p.items() if a*c}
 def mul(self,p,q):
  o=defaultdict(int)
  for m,a in p.items():
   for n,b in q.items():o[tuple(x+y for x,y in zip(m,n))]+=a*b
  return {m:c for m,c in o.items() if c}
 def sq(self,p):return self.mul(p,p)
 def pow(self,p,n):
  z=self.c(1)
  for _ in range(n):z=self.mul(z,p)
  return z
 def op(self,o,a,b):return self.add(a,b) if o=='+' else self.add(a,self.scale(-1,b)) if o=='-' else self.mul(a,b)
 def degree(self,p,w):return max((sum(x*y for x,y in zip(m,w)) for m in p),default=-1)
 def top(self,p,w):
  d=self.degree(p,w);return {m:c for m,c in p.items() if sum(x*y for x,y in zip(m,w))==d}
 def ser(self,p):return [[c,list(m)] for m,c in sorted(p.items())]
def inspect(e):
 rows=e['source'];env=set(e['witnesses'])|set(e['fixed_numerals']);lookup={}
 for name,op,a,b in rows:
  require(name not in env,'Duplicate node '+name);require(op in '+-*','Unknown operation')
  require(all(isinstance(x,int) or x in env for x in (a,b)),'Non-topological node '+name)
  env.add(name);lookup[name]=(op,a,b)
 used=set();pending=[e['output']]
 while pending:
  x=pending.pop()
  if isinstance(x,int) or x in used:continue
  used.add(x)
  if x in lookup:pending.extend(lookup[x][1:])
 require(used==env,'Dead nodes, inputs, or fixed ports')
 require(len(rows)==119 and e['operations']==119,'Incorrect operation count')
 require(Counter(r[1] for r in rows)==Counter({'*':74,'+':24,'-':21}),'Incorrect operator counts')
 return lookup
def check():
 e=json.loads((ROOT/'equation.json').read_text());p=json.loads((ROOT/'source/parent172.json').read_text())
 parent_hash=hashlib.sha256((ROOT/'source/parent172.json').read_bytes()).hexdigest()
 require(parent_hash=='6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449','Immutable source172 polynomial changed')
 require(e['parent']['sha256']==parent_hash,'Parent hash mismatch')
 require(e['domain']=='strictly positive integers' and e['witnesses']==p['witnesses'] and len(e['witnesses'])==10,'Domain/input mutation')
 require(e['fixed_numerals']==p['fixed_numerals'],'Fixed ports changed')
 require(e['coefficient_binding']['ports']==p['coefficient_binding']['ports'],'Coherent coefficient binding changed')
 g=inspect(e);old={r[0]:tuple(r[1:]) for r in p['source']}
 for name,record in old.items():
  if name not in ('L','center','RG'):require(g[name]==record,'Unapproved parent-row change '+name)
 for name,record in {
  'pc_b2':('*','cTR','cTR'),'L':('*','UE','pc_b2'),
  'pc_n_minus_LB':('-','n','LBt'),'center':('-','pc_n_minus_LB','pc_Omega'),
  'pc_G16':('*',16,'Dg'),'RG':('*','M2','pc_G16')}.items():
  require(g[name]==record,'Wrong transform '+name)
 # Direct independent sparse collection of the actual center gates.
 r=Ring(6);A,Y,k,U,b,c=[r.v(i) for i in range(6)]
 one=r.c(1);e2=r.mul(r.sq(k),r.sq(Y));v=r.mul(Y,r.add(A,r.scale(-1,Y),r.c(-1)))
 E=r.add(one,r.mul(r.mul(v,r.add(v,one)),r.sq(k)))
 Delta=r.add(r.sq(A),r.c(-1));f=r.add(one,r.scale(2,r.mul(r.mul(Delta,r.sq(U)),E)))
 V=r.add(r.mul(f,b),r.scale(-1,c));F=r.mul(E,V);G=r.mul(E,r.add(one,r.mul(r.mul(Delta,r.sq(U)),E)))
 env={'Am1':r.add(A,r.c(-1)),'qY':Y,'k':k,'U':U,'cTR':b,'c':c,'Dtau':E,'V':V,'V0kk':r.mul(k,r.add(v,one))}
 def get(x):return r.c(x) if isinstance(x,int) else env[x]
 center_names=[]
 for name,op,a,z in e['source']:
  if name.startswith('pc_') and name not in ('pc_b2','pc_n_minus_LB','pc_G16'):
   env[name]=r.op(op,get(a),get(z));center_names.append(name)
 require(len(center_names)==29,'Wrong center gate count')
 quotient=lambda j:{(m[0]-j,)+m[1:]:a for m,a in F.items() if m[0]>=j}
 Q1,Q3=quotient(1),quotient(3)
 require(all(a%2==0 for a in Q3.values()),'Nonintegral center quotient')
 expected=r.mul(U,r.add(r.scale(4,r.mul(A,F)),r.scale(-2,Q1),{m:-a//2 for m,a in Q3.items()}))
 Omega=env['pc_Omega'];require(Omega==expected,'Center is not the formal quotient identity')
 defect=r.add(r.sq(Omega),r.scale(-16,r.mul(G,r.sq(V))))
 weights=[4,2,1,5,4,2]
 require(len(Omega)==84 and len(defect)==594,'Sparse exact identity changed')
 require(r.degree(Omega,weights)==59 and r.degree(defect,weights)==94,'Weighted degree mismatch')
 expected_top=r.scale(8,r.mul(r.mul(r.mul(r.mul(r.pow(A,6),r.pow(Y,8)),r.pow(k,8)),r.mul(r.pow(U,6),r.sq(b))),r.add(r.sq(A),r.scale(-6,r.pow(Y,4)))))
 require(r.top(defect,weights)==expected_top,'Norm-defect leading form mismatch')
 # Verify the whole norm decomposition freely in six abstract quantities.
 rr=Ring(6);Q,M,Gc,Vc,Z0,Wc=[rr.v(i) for i in range(6)]
 Z=rr.add(Z0,rr.scale(-1,rr.mul(M,Wc)));mg=rr.scale(16,rr.mul(rr.sq(M),Gc))
 out=rr.add(rr.mul(Q,rr.add(rr.sq(Z),rr.scale(-1,rr.mul(mg,rr.sq(Vc))))),mg,rr.scale(-1,rr.sq(Z)))
 df=rr.add(rr.sq(Wc),rr.scale(-16,rr.mul(Gc,rr.sq(Vc))))
 dec=rr.add(rr.mul(Q,rr.add(rr.sq(Z0),rr.scale(-2,rr.mul(rr.mul(M,Z0),Wc)),rr.mul(rr.sq(M),df))),mg,rr.scale(-1,rr.sq(Z)))
 require(out==dec,'Full-output decomposition mismatch')
 # Tropical bounds for unchanged data and the uncentered new carrier.
 deg={x:1 for x in e['witnesses']};deg.update({x:0 for x in e['fixed_numerals']})
 for name,op,a,z in e['source']:
  da=0 if isinstance(a,int) else deg[a]
  dz=0 if isinstance(z,int) else deg[z]
  if name=='center':deg[name]=deg['pc_n_minus_LB'];continue
  deg[name]=max(da,dz) if op in '+-' else da+dz
 expected_degrees={'Q':72,'Mtot':12,'Dg':46,'V':36,'Znum':41,'pc_Omega':59,'L':27}
 require({x:deg[x] for x in expected_degrees}==expected_degrees,'Carrier/port degree bounds mismatch')
 upper=[72+2*41,72+12+41+59,72+24+94,24+46,2*(12+59)]
 require(upper==[154,184,190,70,142],'Wrong full-degree bounds')
 # Substitute actual highest forms, treating beta as a fixed degree-zero symbol.
 s=Ring(11);J,Fv,alpha,iv,T,w,sv,n,eta,zeta,beta=[s.v(i) for i in range(11)]
 q0=s.mul(beta,J);k0=s.add(eta,zeta);A0=s.mul(s.sq(q0),s.mul(w,sv));Y0=s.mul(q0,sv)
 U0=s.mul(iv,s.sq(s.mul(k0,sv)));b0=s.scale(-1,s.mul(s.pow(q0,3),s.add(q0,s.scale(-1,Fv))))
 E0=s.mul(s.sq(k0),s.mul(s.pow(q0,6),s.mul(s.sq(w),s.pow(sv,4))))
 Q0=s.scale(4,s.mul(s.pow(A0,6),s.mul(s.pow(U0,4),s.sq(E0))))
 M0=s.scale(24,s.mul(s.pow(q0,8),A0))
 def substitute(poly,vals):
  accum=s.c(0)
  for ex,cc in poly.items():
   term=s.c(cc)
   for vv,nn in zip(vals,ex):term=s.mul(term,s.pow(vv,nn))
   accum=s.add(accum,term)
  return accum
 d0=substitute(expected_top,[A0,Y0,k0,U0,b0,s.mul(k0,sv)])
 leading=s.mul(Q0,s.mul(s.sq(M0),d0))
 formula=s.scale(9*2**11,s.mul(s.pow(q0,74),s.mul(s.pow(w,18),s.mul(s.pow(sv,52),s.mul(s.pow(iv,10),s.mul(s.pow(k0,32),s.mul(s.sq(s.add(q0,s.scale(-1,Fv))),s.add(s.sq(w),s.scale(-6,s.sq(sv))))))))))
 require(leading==formula and s.degree(leading,[1]*10+[0])==190,'Actual-coordinate leading polynomial mismatch')
 # Authenticate the actual four numerals and independently reconstruct their bytes.
 spec=importlib.util.spec_from_file_location('numeral_recipe',ROOT/'source/rebuild_coefficients.py');recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
 constants=recipe.reconstruct();payloads=[]
 for name,meta in e['coefficient_binding']['ports'].items():
  raw=gzip.decompress((ROOT/'source/coefficients'/meta['file']).read_bytes())
  require(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Numeral payload changed '+name)
  value=int.from_bytes(raw,'little');require(value==constants[name] and value.bit_length()==meta['bits'],'Numeral reconstruction mismatch '+name)
  payloads.append({'port':name,'bits':value.bit_length(),'sha256':meta['raw_sha256']})
 require(constants['beta']>0,'Leading coefficient not known nonzero')
 # Nonzero modular derivatives prove genuine dependence on all ten variables.
 prime=1000000007;derivatives={}
 for target in e['witnesses']:
  ev={x:(j+2,int(x==target)) for j,x in enumerate(e['witnesses'])};ev.update({x:(constants[x]%prime,0) for x in e['fixed_numerals']})
  for name,op,a,z in e['source']:
   av,ad=(a%prime,0) if isinstance(a,int) else ev[a];bv,bd=(z%prime,0) if isinstance(z,int) else ev[z]
   if op=='+':value,diff=av+bv,ad+bd
   elif op=='-':value,diff=av-bv,ad-bd
   else:value,diff=av*bv,ad*bv+av*bd
   ev[name]=(value%prime,diff%prime)
  derivatives[target]=ev[e['output']][1];require(derivatives[target]!=0,'Derivative certificate vanished '+target)
 receipt={'status':'PASS','domain':e['domain'],'variables':10,'operations':119,'operation_breakdown':e['operation_breakdown'],'degree':190,'center_terms':len(Omega),'defect_terms':len(defect),'center_weighted_degree':59,'defect_weighted_degree':94,'decomposition_degree_bounds':upper,'leading_form':'9*2^11*q0^74*w^18*s^52*i^10*k^32*(q0-F)^2*(w^2-6*s^2), q0=beta*J, k=eta+zeta','explicit_nonzero_coefficient':'[J^74 w^20 s^52 i^10 eta^32 F^2] = 9*2^11*beta^74','coefficient_payloads':payloads,'modular_nonzero_partial_derivatives':{'prime':prime,'point':[j+2 for j in range(10)],'values':derivatives},'proof_boundary':'Finite exact algebra and fixed numerals; unbounded arithmetic and inherited calibration are separate.'}
 (ROOT/'CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n')
 (ROOT/'exact_center_polynomials.json').write_text(json.dumps({'variables':['A','Yprime','k','U','b','c'],'weights':weights,'center':r.ser(Omega),'defect':r.ser(defect),'defect_top':r.ser(expected_top)},indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':check()

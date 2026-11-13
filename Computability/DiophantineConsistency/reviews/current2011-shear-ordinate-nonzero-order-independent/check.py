#!/usr/bin/env python3
"""Source pins, exact graph wiring, polynomial identity and bounded diagnostics."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-ordinate-nonzero-order-draft/README.md':'dcd813b1e87dc59bad958598407d688fbda679f7738ecbfd6ca52341f9ccbe8f',
'research/current2011-shear-ordinate-nonzero-order-draft/ShearNonzero.lean.src':'c67931ea31c2fbedc6d0976f5d188fe9bf5633bfe4a51062a0c64e81dd1a66f3',
'research/current2011-shear-ordinate-nonzero-order-draft/check.py':'3efcd7f2103f9416cf330214fa422c36ece2f89ca6b816badfc2ff08f90d92a2',
'research/current2011-shear-ordinate-nonzero-order-draft/result.json':'a5615a2acb3fe608150d01c4357be234d235d942d8afd47c210dcce3cc0c55dc',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
'research/current2011-sheared72-46-proof-draft/ShearDraft.lean':'a479640aa326cb2190d530bb806d199f29c77796acd8f93edaffe609e5a8af2a',
'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154'}
def need(b,msg):
 if not b:raise RuntimeError(msg)
for path,d in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==d,'pin '+path)
g=json.loads((root/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes()); rows={x[0]:x for x in g['source']}
need(len(g['source'])==len(rows)==72 and g['output']=='polynomial','literal count/output')
expected=[['I','*','i','c2'],['I2','*','I','I'],['f2m1','-','f2',1],['Aaux','*','Delta','f2m1'],['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux'],['strong_residual','-','I2','Aaux'],['P2','*','N0','N0'],['Na2','*','Na','Na'],['QW','*','N1','Nt'],['rQW','-','QW',1],['rQW2','*','rQW','rQW'],['strong2','*','strong_residual','strong_residual'],['sum1','+','P2','Na2'],['sum2','+','sum1','rQW2'],['sum3','+','sum2','strong2'],['polynomial','-','sum3',2]]
for r in expected:need(rows.get(r[0])==r,'row '+r[0])
# Formal expansion in Z[A,V,y] of both auxiliary-factor forms.
def add(p,q,k=1):
 z=p.copy()
 for m,v in q.items():z[m]=z.get(m,0)+k*v
 return {m:v for m,v in z.items() if v}
def mul(p,q):
 z={}
 for x,a in p.items():
  for y,b in q.items():
   m=tuple(i+j for i,j in zip(x,y));z[m]=z.get(m,0)+a*b
 return {m:v for m,v in z.items() if v}
A={(1,0,0):1};V={(0,1,0):1};y={(0,0,1):1};vy=add(V,y)
lhs=add(mul(A,add(mul(V,V),mul(vy,vy),-1)),mul(vy,vy))
rhs=add(mul(vy,vy),mul(mul(A,y),add(vy,V)),-1)
need(lhs==rhs,'exact auxiliary polynomial identity')
checks=0
for a in range(-15,16):
 for i in range(2,15):
  for yval in range(1,12):
   u=a*yval*yval;h=i*i-a
   need(u*u+h*h>=4,'unrestricted-A inequality');checks+=1
need(1+1**2+(1**2-1)**2==2,'I-bound counterexample')
print(json.dumps({'pins_verified':len(pins),'candidate_rows':72,'factor_and_output_rows_checked':len(expected),'exact_auxiliary_polynomial_identity':True,'integer_controls_including_negative_A':checks,'I_bound_essential_control':True,'scope':'source/graph and bounded controls; no Lean or all-model witness bridge'},sort_keys=True,indent=2))

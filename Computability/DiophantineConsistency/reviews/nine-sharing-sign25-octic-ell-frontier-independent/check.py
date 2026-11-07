#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-octic-ell-candidate';S=D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for q,h in [(P/'build.py','df39c9f1e0602a990c98d7174ee28b2cc27510626fcbdbd3d14bfb39e632a7f5'),(P/'check.py','df5dcf60ffb5691d103a163ed089f00dcec7f668a959dd57246933ccac5e955e'),(P/'seed.json','c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8'),(P/'result.json','791c69bac4270d0157a816ed2626259716b86a942930e081ebbcaf1f87405c03'),(S,'36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25')]:assert H(q)==h
a=json.loads(S.read_text());b=json.loads((P/'seed.json').read_text());assert a['witness_count']==26 and a['total_coordinates']==27 and b['witness_count']==25 and b['total_coordinates']==26 and b['distinguished_input_coordinate']==0 and b['fixed_ports']==a['fixed_ports'] and b['coefficient_binding']==a['coefficient_binding'];old=a['residuals'];new=b['residuals'];assert len(old)==17 and len(new)==16 and next(x['expr'] for x in old if x['gate']=='ell')==['sub',['var',19],['mul',['var',17],['var',18]]]
# Compare all ASTs simultaneously by a stack, using old-coordinate interpretation
# old i<19 -> new i, old 19 -> new 17*18, old i>19 -> new i-1.
def same(x,y):
 todo=[(x,y)]
 while todo:
  u,v=todo.pop();op=u[0]
  if op=='var':
   i=u[1];assert v==(['mul',['var',17],['var',18]] if i==19 else ['var',i if i<19 else i-1])
  elif op in ('num','port'):assert u==v
  else:assert op in ('add','sub','mul') and len(u)==len(v)==3 and op==v[0];todo.extend([(u[1],v[1]),(u[2],v[2])])
for x,y in zip([x for x in old if x['gate']!='ell'],new):assert x['gate']==y['gate'] and x['kind']==y['kind'];same(x['expr'],y['expr'])
def degree(tree,special=False):
 todo=[(tree,False)];vals=[]
 while todo:
  t,done=todo.pop();op=t[0]
  if op in ('num','port'):vals.append(0)
  elif op=='var':assert 0<=t[1]<26;vals.append(int(t[1] in (17,18)) if special else 1)
  elif not done:assert op in ('add','sub','mul');todo.extend([(t,True),(t[2],False),(t[1],False)])
  else:
   z=vals.pop();w=vals.pop();vals.append(w+z if op=='mul' else max(w,z))
 assert len(vals)==1;return vals[0]
assert all(degree(r['expr'])<=4 for r in new);N=next(r['expr'] for r in new if r['gate']=='N0');assert degree(N,True)<=4 and all(degree(r['expr'],True)<=2 for r in new if r['gate']!='N0')
def eval_(t,x):
 op=t[0]
 if op=='num':return t[1]
 if op=='var':return x if t[1] in (17,18) else 0
 if op=='port':raise AssertionError('N0 unexpectedly uses a port')
 a,c=eval_(t[1],x),eval_(t[2],x)
 return a+c if op=='add' else a-c if op=='sub' else a*c
# Degree ≤4 plus five exact values imply the stated N0 polynomial identically.
assert all(eval_(N,t)==-t**4-2*t*t-1 for t in range(5))
coeff=P/b['coefficient_binding']['path'];assert coeff.resolve()==(S.parent/a['coefficient_binding']['path']).resolve()
for rec in b['coefficient_binding']['ports'].values():assert H(coeff/rec['file'])==rec['gzip_sha256']
assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(P/'build.py'),'--check'],check=True,capture_output=True,text=True,timeout=120).stdout)['status']=='PASS';assert json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],check=True,capture_output=True,text=True,timeout=120).stdout)==json.loads((P/'result.json').read_text())
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','structural_transfers':16,'residual_degree_upper_bound':4,'square_sum_exact_total_degree':8,'N0_specialization':'-t^4-2*t^2-1','scope':'external fixed-port AST only; natural lift is product; no Lean bridge or endpoint'},sort_keys=True,indent=2))

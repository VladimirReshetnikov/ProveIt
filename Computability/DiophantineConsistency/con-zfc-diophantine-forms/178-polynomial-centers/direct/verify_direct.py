#!/usr/bin/env python3
"""Independent algebra, nonnegative restoration, and literal expansion audit.

Does not import either construction/discovery script. The canonical CRT lift
argument is a separately supplied unbounded proof, not a finite computation.
"""
from pathlib import Path
import json,sys,copy,hashlib,argparse
sys.dont_write_bytecode=True
import audit_projection as a
ROOT=Path(__file__).resolve().parent
def load(p):return json.loads(p.read_text())
def need(ok,msg):
 if not ok:raise ValueError(msg)
def pol(eq,terms):return a.polynomial(terms,len(eq['variables']))

def natural_domains(source,steps):
 current=source;out=[]
 for j,c in enumerate(steps):
  ns={v['name']:i for i,v in enumerate(current['variables'])};direction=dict(c['direction'])
  solution=pol(current,c['sheared_pivot_solution'])
  need(all(coef>=0 for coef in solution.values()),'deleted pivot has no coefficientwise natural proof')
  if j==0:
   need(direction=={ns['mul.363']:1,ns['mul.369']:1},'wrong first natural direction')
   need(c['pivot']==ns['mul.363'],'wrong first pivot')
   expected={():1,(ns['crt.encoded.Sp'],):1,(ns['mul.361'],):1,tuple(sorted([ns['crt.encoded.Sp'],ns['mul.361']])):1}
   need(solution==expected,'first product restoration mismatch')
   out.append({'step':1,'soundness':'both changed old coordinates are nonnegative polynomials in new naturals','completeness':'canonical CRT lifts ensure mul369>=mul363 (source164 PROOF section3.2)'})
  elif j==1:
   need(direction=={ns['mul.372']:1,ns['mul.373']:1},'wrong second natural direction')
   need(c['pivot']==ns['mul.373'],'wrong second pivot')
   expected={():1,(ns['crt.encoded.S'],):1,(ns['mul.361'],):1,tuple(sorted([ns['crt.encoded.S'],ns['mul.361']])):1}
   need(solution==expected,'second product restoration mismatch')
   out.append({'step':2,'soundness':'both changed old coordinates are nonnegative polynomials in new naturals','completeness':'canonical CRT lifts ensure mul372>=mul373 (source164 PROOF section3.3)'})
  elif j==2:
   need(direction=={ns['mul.299']:1,ns['mul.304']:-4},'wrong third natural direction')
   need(c['pivot']==ns['mul.299'],'wrong third natural pivot')
   k=ns['add.302'];q={(ns['mul.304'],):1,(k,):-1,(k,k):-1}
   need(any(pol(current,r['terms'])==q for r in current['residuals']),'missing retained nonnegative-square defining row')
   out.append({'step':3,'soundness':'retained row restores mul304=add302*(add302+1)>=0; pivot is coefficientwise nonnegative','completeness':'all natural parent zeros map to y304=mul304+4*mul299>=0','bijection':'pointwise on the complete natural zero sets for this step'})
  else:raise ValueError('unreviewed natural projection')
  current=a.one_step(current,c)
 return out

def rows_audit(parent,folder):
 c=load(folder/'row_certificate.json');e=load(folder/'equation.json')
 need(c['input_sha256']==a.sha(parent),'row input hash');n=len(parent['variables'])
 rows=[a.polynomial(r['terms'],n) for r in parent['residuals']]
 for i,j,k in c['operations']:
  need(i!=j and 0<=i<len(rows) and 0<=j<len(rows) and type(k) is int,'bad row operation')
  rows[i]=a.linear_combine(rows[i],k,rows[j])
 need([a.serial(r) for r in rows]==[r['terms'] for r in e['residuals']],'row result differs')
 need(parent['variables']==e['variables'] and parent['domain']==e['domain'],'row change moved coordinates')
 need(a.sha(e)==c['output_sha256'],'row output hash')
 for i,j,k in reversed(c['operations']):rows[i]=a.linear_combine(rows[i],-k,rows[j])
 need([a.serial(r) for r in rows]==[r['terms'] for r in parent['residuals']],'inverse row operations fail')
 expanded=a.expanded_sos(e);need(polynomial4(folder,e)==expanded,'row expansion differs')
 m=a.metrics(e,expanded);need(load(folder/'metrics.json')==m,'row metrics differ')
 return {'status':'PASS','operations':len(c['operations']),'metrics':m,'inverse_rows_checked':True}

def polynomial4(folder,e):return a.polynomial(load(folder/'expanded_polynomial.json')['terms'],len(e['variables']),4)

def main():
 result={}
 for name,src in [('radical233','integer_source239.json'),('radical234_sparse','integer_source240_sparse.json'),('natural204','natural_source206.json'),('natural203','natural_source206.json')]:
  result[name]=a.audit(ROOT/src,ROOT/name)
  if name.startswith('natural'):
   result[name]['natural_domain_lemmas']=natural_domains(load(ROOT/src),load(ROOT/name/'projection_certificate.json')['steps'])
 for name,parent in [('natural203_reduced','natural203'),('natural203_sparse','natural203'),('integer233_reduced','radical233')]:
  if (ROOT/name/'equation.json').exists():result[name]=rows_audit(load(ROOT/parent/'equation.json'),ROOT/name)
 result['scope']='Exact coefficients, domain-restoration identities, expansions and deliberate algebra mutations; unbounded CRT completeness and inherited C222 calibration are proved in prose.'
 print(json.dumps({k:({'status':v['status'],'metrics':v.get('output_metrics',v.get('metrics'))} if isinstance(v,dict) else v) for k,v in result.items()},indent=2))
 p=argparse.ArgumentParser();p.add_argument('--receipt',type=Path);args=p.parse_args()
 if args.receipt:args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
if __name__=='__main__':main()

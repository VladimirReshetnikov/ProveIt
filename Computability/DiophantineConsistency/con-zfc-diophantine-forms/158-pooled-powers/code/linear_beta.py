"""Cofinal beta-base change followed by exact integer wire elimination."""
import json,hashlib,argparse
from pathlib import Path
from collections import defaultdict

def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def main(parent,out):
 raw=parent.read_bytes();a=json.loads(raw);names={v['name']:i for i,v in enumerate(a['variables'])};old=names['y'];target=names['pow0.output'];n=len(a['variables'])
 hits=[j for j,r in enumerate(a['residuals']) if r['label']=='cofinal.beta_base']
 if len(hits)!=1:raise ValueError('beta row not unique')
 j=hits[0];expected=terms({():-1,(old,):1,(target,):1,(target,target):-1})
 if a['residuals'][j]['terms']!=expected:raise ValueError('unexpected beta row')
 keep=[i for i in range(n) if i!=old];ren={i:k for k,i in enumerate(keep)};rows=[]
 for k,rr in enumerate(a['residuals']):
  if k==j:continue
  p=defaultdict(int)
  for c,m in rr['terms']:p[tuple(sorted(ren[target if i==old else i] for i in m))]+=c
  rows.append({'label':rr['label'],'terms':terms(p)})
 equation=dict(a,schema='conzfc-linear-beta-v1',variant=f'linear_beta{n-1}',variables=[a['variables'][i] for i in keep],residuals=rows,parent_equation_sha256=hashlib.sha256(raw).hexdigest())
 p=defaultdict(int)
 for rr in rows:
  for c,m in rr['terms']:
   for d,mm in rr['terms']:p[tuple(sorted(m+mm))]+=c*d
 ex=terms(p);met={'variables':n-1,'rows':len(rows),'degree':max(len(m) for c,m in ex),'monomials':len(ex),'height':max(abs(c) for c,m in ex),'row_height':max(abs(c) for rr in rows for c,m in rr['terms'])}
 cert={'schema':'linear_beta_certificate_v1','parent_equation_sha256':hashlib.sha256(raw).hexdigest(),'semantic_row':j,'old_terms':a['residuals'][j]['terms'],'new_terms':terms({(old,):1,(target,):-1}),'eliminated_variable':old,'restoration_variable':target,'old_to_new':[[i,k] for i,k in ren.items()]}
 out.mkdir(parents=True,exist_ok=True)
 for fn,x in [('equation.json',equation),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','domain':'unrestricted integers','variables':n-1,'terms':ex}),('METRICS.json',met),('beta_certificate.json',cert)]:
  (out/fn).write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')
 print(json.dumps(met))
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();main(a.parent,a.output)

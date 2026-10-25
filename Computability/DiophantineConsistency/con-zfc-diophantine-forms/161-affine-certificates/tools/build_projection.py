#!/usr/bin/env python3
"""Exact monic projection with reversible polynomial residual operations."""
import argparse,hashlib,json
from pathlib import Path
from search_projection import add,mul,sub,emit,attempt

def canonical(d):return (json.dumps(d,sort_keys=True,indent=2)+'\n').encode()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('row',type=int);ap.add_argument('variable',type=int);ap.add_argument('output');a=ap.parse_args()
 raw=Path(a.source).read_bytes();source=json.loads(raw)
 if source['domain']!='unrestricted integers':raise ValueError('Integer domain required')
 rows=[{tuple(m):c for c,m in r['terms']} for r in source['residuals']]
 ri,v=a.row,a.variable
 if rows[ri].get((v,)) not in (-1,1) or any(v in m for m in rows[ri] if m!=(v,)):raise ValueError('Not monic')
 result=attempt(rows,ri,v)
 if result is None:raise ValueError('No degree-preserving reduction')
 projected,replacement,ops=result
 keep=[i for i in range(len(source['variables'])) if i!=v];ren={i:j for j,i in enumerate(keep)}
 def rename(p):return {tuple(ren[i] for i in m):c for m,c in p.items()}
 newrows=[rename(p) for i,p in enumerate(projected) if i!=ri]
 if any(max(map(len,p),default=0)>2 for p in newrows):raise ValueError('Degree increase')
 poly={}
 for p in newrows:poly=add(poly,mul(p,p))
 equation={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':'monic_modulo_retained_gate_rows','variables':[source['variables'][i] for i in keep],'residuals':[{'label':r['label'],'terms':emit(p)} for r,p in zip([r for i,r in enumerate(source['residuals']) if i!=ri],newrows)]}
 degree=max(map(len,poly),default=0)
 metrics={'variables':len(keep),'rows':len(newrows),'degree':degree,'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for p in newrows for c in p.values()),'row_support':sum(map(len,newrows))}
 cert={'schema':'monic_projection_modulo_retained_rows_v1','source_sha256':hashlib.sha256(raw).hexdigest(),'pivot_row':ri,'deleted_variable':v,'deleted_variable_name':source['variables'][v]['name'],'replacement_in_source_indices':emit(replacement),'post_substitution_residual_operations':[{'target_row':i,'retained_reducer_row':j,'subtract_multiplier':h} for i,j,h in ops],'retained_source_variables':keep,'retained_source_rows':[i for i in range(len(rows)) if i!=ri],'restoration_in_final_coordinates':[emit(rename(replacement if i==v else {(i,):1})) for i in range(len(source['variables']))]}
 out=Path(a.output);out.mkdir(parents=True,exist_ok=True)
 (out/'source_equation.json').write_bytes(raw)
 for name,d in [('equation.json',equation),('expanded_polynomial.json',{'schema':'expanded_integer_polynomial_v1','terms':emit(poly)}),('METRICS.json',metrics),('projection_certificate.json',cert)]:
  (out/name).write_bytes(canonical(d))
 print(json.dumps(metrics,sort_keys=True))
if __name__=='__main__':main()

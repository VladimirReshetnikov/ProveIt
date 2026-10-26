"""Odd-linear beta multiplier, with exact monic contraction after semantic edit.
Arithmetic credit: source157 Linear CRT; signed-mod-four bootstrap in PROOF.md.
"""
import argparse,copy,hashlib,json
from pathlib import Path
from reduce_radical import norm,terms,subst,V,add,canonical,metric,mul

def main(src,out):
 old=json.loads(src.read_text());names={v['name']:i for i,v in enumerate(old['variables'])};m=names['beta.odd_square_multiplier'];w=names['beta.odd_square_root_half'];f=names['crt.growth_majorant_F'];y=names['y'];rs=[norm(r['terms'])for r in old['residuals']]
 guard=add(V(m),{():-1,(w,):-4,(w,w):-4});hits=[i for i,r in enumerate(rs) if r==guard]
 if len(hits)!=1:raise ValueError('literal odd-square guard')
 g=hits[0];replacement=add({():1},{(w,):2});keep=[i for i in range(len(old['variables']))if i!=m];rename={i:j for j,i in enumerate(keep)}
 edited=add(V(m),{():-1,(w,):-2});pre=[subst(r,{m:replacement})for i,r in enumerate(rs)if i!=g]
 if any(len(mon)>2 for r in pre for mon in r):raise ValueError('nonquadratic contraction')
 eq=copy.deepcopy(old);eq['variant']+=':odd_linear_beta';eq['variables']=[old['variables'][i]for i in keep];eq['variables'][rename[w]]={'name':'beta.odd_linear_parameter','kind':'unrestricted_integer'}
 eq['residuals']=[dict(row,terms=terms({tuple(rename[i]for i in mon):c for mon,c in p.items()}))for row,p in zip([r for i,r in enumerate(old['residuals'])if i!=g],pre)]
 cert={'schema':'odd_linear_beta_v1','source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'old_guard_row':g,'old_guard':terms(guard),'edited_guard':terms(edited),'multiplier_coordinate':m,'parameter_coordinate':w,'F_coordinate':f,'stored_y_coordinate':y,'actual_y':terms(add(V(y),{():-1})),'replacement':terms(replacement),'retained_coordinates':keep,'semantic_scope':'zero existence; not a pointwise inverse of the original square guard','old_witness_parameter_map':terms({(w,):2,(w,w):2})}
 pol=add(*(mul(norm(r['terms']),norm(r['terms']))for r in eq['residuals']));out.mkdir(parents=True,exist_ok=True)
 for fn,obj in [('equation.json',eq),('beta_certificate.json',cert),('METRICS.json',metric(eq,True)),('expanded_polynomial.json',{'domain':'unrestricted integers','schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':terms(pol)})]:(out/fn).write_bytes(canonical(obj))
 print(metric(eq,True))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('out',type=Path);a=p.parse_args();main(a.source,a.out)

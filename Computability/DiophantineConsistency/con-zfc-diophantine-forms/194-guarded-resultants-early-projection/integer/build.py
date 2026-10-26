#!/usr/bin/env python3
"""Frozen209-quartic constructor. No search, network or nonstandard imports."""
from pathlib import Path
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import polynomial as P
V=P.V
C=lambda n:{():n}if n else{}
def dump(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(P.canonical(o))
def require(b,s):
 if not b:raise ValueError(s)
def build(dest):
 raw=(ROOT/'sources/parent210.json').read_bytes();eq=json.loads(raw);old=[P.norm(r['terms'])for r in eq['residuals']]
 require(len(eq['variables'])==210 and len(old)==150,'source dimensions')
 require(eq['variables'][0]['name']=='t0'and eq['variables'][178]['name']=='cofinal.horizon_root','coordinate bindings')
 require(old[125]==P.add(C(-16),V(0),P.scale(P.mul(V(178),V(178)),-4)),'old horizon')
 require(all(178 not in m for i,r in enumerate(old)if i!=125 for m in r),'private old root')
 actual_t=P.add(P.scale(V(0),4),C(2));rows=[P.subst(r,{0:actual_t})for r in old]
 keep=[i for i in range(210)if i!=178];ren={i:j for j,i in enumerate(keep)};rkeep=[i for i in range(150)if i!=125]
 variables=copy.deepcopy(eq['variables']);variables[0]={'name':'horizon.affine_parameter','kind':'unrestricted_integer'}
 out=copy.deepcopy(eq);out.update(schema='conzfc-even-affine-pell209-v1',variant='even_affine_horizon209',variables=[variables[i]for i in keep],residuals=[dict(eq['residuals'][i],terms=P.terms({tuple(ren[j]for j in m):c for m,c in rows[i].items()}))for i in rkeep])
 out['semantic_parent_sha256']=hashlib.sha256(raw).hexdigest();out['horizon']='t=4*x0+2'
 require(all(len(m)<=2 for r in out['residuals']for c,m in r['terms']),'quadratic degree')
 edits=[{'old_row':i,'label':eq['residuals'][i]['label'],'before':P.terms(old[i]),'after_before_renumbering':P.terms(rows[i])}for i in rkeep if rows[i]!=old[i]]
 cert={'schema':'even_affine_horizon_v1','source':'sources/parent210.json','source_sha256':hashlib.sha256(raw).hexdigest(),'old_t_coordinate':0,'actual_t':P.terms(actual_t),'deleted_coordinate':178,'deleted_row':125,'old_horizon':P.terms(old[125]),'changed_retained_rows':edits,'retained_old_coordinates':keep,'retained_old_rows':rkeep,'old_to_new':[[i,j]for i,j in ren.items()],'source_frame_row':124,'source_growth_rows':[147,148,149],'scope':'semantic cofinal zero-existence change; retained coordinates are affine substitution, not an arbitrary old-witness bijection'}
 atoms=[('t',V(0)),('t+1',P.add(V(0),C(1))),('F+t',P.add(V(2),V(0))),('x',V(1)),('obsolete_growth_base_duplicate',V(0)),('B',V(3)),('F',V(2)),('y+1',V(4)),('a',V(8))]
 atoms += [(name,V(i))for name,i in zip(['b','c','d','S','Sp','u','vq'],range(9,16))]
 atoms += [('C',P.scale(V(16),2)),('N',V(17)),('q',P.add(V(94),C(-1))),('q+1',V(94)),('affine_radix_base',P.add(P.scale(V(16),4),P.scale(V(2),2),C(2)))]
 atoms += [('pow'+str(k)+'.output',V(i))for k,i in [(3,95),(4,96),(5,100),(7,103),(8,106),(9,109),(10,112),(11,113),(12,116),(13,119),(14,120),(15,124),(16,127)]]
 require(old[124]==P.add(V(130),C(-2),*(P.scale(P.mul(a,a),-1)for _,a in atoms)),'exact actual square frame')
 dump(dest/'frame_certificate.json',{'schema':'actual_square_frame_v1','source_row':124,'output_row':124,'atoms':[{'label':label,'parent_terms':P.terms(a),'actual_terms':P.terms(P.subst(a,{0:actual_t}))}for label,a in atoms],'constant':2,'old_frame':P.terms(old[124]),'new_frame':P.terms(rows[124]),'power_requests':15,'power_ports':45,'extra_duplicate_note':'The source retains an obsolete growth-base copy of t; it is harmless and preserved exactly.'})
 ps=[P.norm(r['terms'])for r in out['residuals']];pol=P.add(*(P.mul(r,r)for r in ps))
 dump(dest/'semantic_certificate.json',cert);dump(dest/'integer209/equation.json',out);dump(dest/'integer209/expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':209,'terms':P.terms(pol)});dump(dest/'integer209/metrics.json',P.metric(out,True))
 dump(dest/'coordinate_map.json',{'actual_t':P.terms(actual_t),'retained_old_coordinates':keep,'retained_old_rows':rkeep,'old_to_new':cert['old_to_new'],'old_root':'discarded semantic horizon witness, no pointwise reconstruction claimed','forward_on_physical_tuples_with_t_congruent_2_mod4':'new_x0=(old_t-2)/4; other coordinates retained','physical_front_map':'old_t=4*new_x0+2; other retained physical coordinates agree'})
 print(json.dumps(P.metric(out,True),sort_keys=True))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();build(a.out)

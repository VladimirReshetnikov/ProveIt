#!/usr/bin/env python3
"""Frozen literal constructor; Python standard library only; relative source paths."""
from pathlib import Path
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import polynomial as P
D=2**20
C=lambda n:{():n} if n else {}
V=P.V
sq=lambda a:P.mul(a,a)
def require(a,m):
 if not a:raise ValueError(m)
def dump(p,a):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(P.canonical(a))
def construct():
 path='sources/parent213.json';raw=(ROOT/path).read_bytes();e=json.loads(raw);old=[P.norm(r['terms']) for r in e['residuals']];rs=copy.deepcopy(old)
 require(len(e['variables'])==213 and len(rs)==152,'source dimensions')
 t=V(0);F=V(2);A=P.add(V(131),C(1));d=P.add(P.scale(t,4),C(2));W=V(130);w=V(180);z=V(181);Z=V(182)
 require(old[96]==P.add(V(138),sq(t),C(1),P.scale(P.mul(A,t),-2)),'source growth modulus')
 require(old[97]==P.add(F,P.scale(V(180),-1),P.scale(P.mul(t,V(181)),-1),P.mul(V(138),V(139))),'source growth power')
 require(old[127]==P.add(sq(w),P.scale(P.mul(w,Z),2),sq(z),C(-1)),'source growth norm')
 require(old[130]==P.add(t,C(-16),P.scale(sq(V(184)),-4)),'source horizon')
 require(all(184 not in m for i,r in enumerate(old) if i!=130 for m in r),'private horizon root')
 rs[96]=P.add(V(138),sq(d),C(1),P.scale(P.mul(A,d),-2))
 rs[97]=P.add(F,C(-1),P.scale(w,-D),P.scale(Z,D),P.scale(P.mul(d,z),-D),P.mul(V(138),V(139)))
 rs[127]=P.add(P.scale(w,2),P.scale(sq(w),D),P.scale(sq(z),D),P.scale(sq(Z),-D))
 old_growth_error=P.add(C(2),P.scale(w,-2),P.scale(Z,-2),sq(Z),P.scale(sq(t),D*D),P.scale(P.mul(t,z),-2*D))
 new_growth_error=P.add(sq(w),sq(P.add(z,P.scale(t,-1))))
 rs[141]=P.add(old[141],P.scale(old_growth_error,-1),new_growth_error)
 atoms=[('t',t),('t+1',P.add(t,C(1))),('F+t',P.add(F,t)),('x',V(1)),('growth_base',d),('B',V(3)),('F',F),('y+1',V(4)),('a',P.add(V(8),C(-1)))]
 atoms += [(name,V(i))for name,i in zip(['b','c','d','S','Sp','u','vq'],range(9,16))]
 atoms += [('C',P.scale(V(16),2)),('N',V(17)),('growth_index',P.scale(t,D)),('q',P.add(V(94),C(-1))),('q+1',V(94)),('BH',V(183))]
 atoms += [('pow'+str(k)+'.output',V(i))for k,i in [(3,95),(4,96),(5,100),(7,103),(8,106),(9,109),(10,112),(11,113),(12,116),(13,119),(14,120),(15,124),(16,127)]]
 weights={}
 for _,a in atoms:
  require(max(map(len,a),default=0)<=1,'affine atom')
  for m,c in a.items():
   if m:weights[m[0]]=max(weights.get(m[0],0),abs(c))
 require(len(atoms)==35 and weights[0]==D and weights[16]==2,'atom census')
 rs[128]=P.add(W,C(-22),*(P.scale(sq(V(i)),-c)for i,c in sorted(weights.items())))
 rs[91]=P.add(V(133),P.scale(W,4),P.scale(P.mul(W,V(132)),-8))
 rs[92]=P.add(V(134),P.scale(P.mul(W,V(133)),-4),P.scale(V(133),-1))
 edits=[{'row':i,'old':P.terms(old[i]),'new':P.terms(rs[i])}for i in range(len(rs))if rs[i]!=old[i]]
 semantic={'schema':'scaled_dyadic_growth_pair_v1','source':path,'source_sha256':hashlib.sha256(raw).hexdigest(),'D':D,'growth_base':P.terms(d),'growth_index':P.terms(P.scale(t,D)),'atoms':[{'label':s,'terms':P.terms(a)}for s,a in atoms],'frame_weights':[[i,c]for i,c in sorted(weights.items())],'frame_constant':22,'frame_scale':4,'old_growth_error':P.terms(old_growth_error),'new_growth_error':P.terms(new_growth_error),'edits':edits,'deleted_row':130,'deleted_coordinate':184,'scaled_coordinates':{'w':180,'z':181,'Az':182},'physical_pair':{'X':P.terms(P.add(C(1),P.scale(w,D))),'Y':P.terms(P.scale(z,D))},'cap_row':144,'cap_change':'same literal row, replacing physical growth ordinate squared by scaled ordinate squared','scope':'semantic zero-existence equivalence via signed Pell theorem; not an arbitrary old-witness bijection'}
 vs=copy.deepcopy(e['variables'])
 for i,n in [(180,'growth.scaled_abscissa'),(181,'growth.scaled_ordinate'),(182,'growth.A_times_scaled_ordinate')]:vs[i]={'name':n,'kind':'scaled_pell'}
 vs[0]={'name':'horizon.t','kind':'unrestricted_integer'}
 base=dict(e,variables=vs,residuals=[dict(r,terms=P.terms(s))for r,s in zip(e['residuals'],rs)],variant='dyadic_scaled_growth_affine_horizon')
 base.pop('parent_equation_sha256',None)
 base.update(schema='conzfc-scaled-semantic-staging-v1',inactive_rows=[130],inactive_coordinates=[184],polynomial='sum(square(row) for row_index,row in enumerate(residuals) if row_index != 130)')
 operations=json.loads((ROOT/'operations.json').read_text())
 for op in operations:
  if op['type']=='row':
   i,j,k=op['target'],op['source'],op['multiple'];require(i!=j and k!=0,'row operation');rs[i]=P.add(rs[i],P.scale(rs[j],k))
  else:
   i=op['coordinate'];p=P.norm(op['image']);require(p.get((i,))==1 and all(i not in m for m in p if m!=(i,)),'unit affine coordinate operation');rs=[P.subst(r,{i:p})for r in rs]
 require(all(184 not in m for i,r in enumerate(rs)if i!=130 for m in r),'private root after operations')
 keep=[i for i in range(213)if i!=184];ren={i:j for j,i in enumerate(keep)};rkeep=[i for i in range(152)if i!=130]
 out=dict(base,variables=[vs[i]for i in keep],residuals=[dict(e['residuals'][i],terms=P.terms({tuple(ren[j]for j in m):c for m,c in rs[i].items()}))for i in rkeep],variant='integer212_scaled_dyadic_growth')
 out.pop('inactive_rows',None);out.pop('inactive_coordinates',None);out.update(schema='conzfc-scaled-dyadic212-v1',polynomial='sum(square(row) for row in residuals)')
 for row in out['residuals']:require(all(len(m)<=2 for c,m in row['terms']),'degree')
 maps={'schema':'elementary_integral_chart_with_private_deletion_v1','operations':operations,'retained_old_coordinates':keep,'retained_old_rows':rkeep,'deleted_coordinate':184,'deleted_row':130,'semantic_note':'Deleted old cofinal square root is not reconstructed: the new cofinal horizon is a semantic change.'}
 return base,out,semantic,maps

def build(dest):
 base,eq,semantic,maps=construct()
 dump(dest/'base213/equation.json',base);dump(dest/'semantic_certificate.json',semantic);dump(dest/'coordinate_map.json',maps)
 dump(dest/'integer212/equation.json',eq)
 ps=[P.norm(r['terms'])for r in eq['residuals']];pol=P.add(*(sq(p)for p in ps))
 dump(dest/'integer212/expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':P.terms(pol)})
 dump(dest/'integer212/metrics.json',P.metric(eq,True))
 dump(dest/'row_certificate.json',{'input_sha256':P.digest(base),'operations':maps['operations'],'output_sha256':P.digest(eq),'omitted_private_coordinate':184,'omitted_private_row':130})
 print(json.dumps(P.metric(eq,True),sort_keys=True))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();build(a.out)

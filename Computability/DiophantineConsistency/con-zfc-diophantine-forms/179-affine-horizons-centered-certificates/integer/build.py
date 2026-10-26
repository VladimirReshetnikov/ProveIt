#!/usr/bin/env python3
"""Frozen construction; no search, optimization, network, or nonstandard imports."""
from pathlib import Path
import argparse,copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'));sys.path.insert(0,str(ROOT/'credited'))
import polynomial as P
from check_parent_frame import check as check_parent_frame

def require(condition,msg):
 if not condition:raise ValueError(msg)
def dump(path,obj):path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(P.canonical(obj))
def construct():
 source=ROOT/'sources/parent217.json';eq=json.loads(source.read_text());ns={v['name']:i for i,v in enumerate(eq['variables'])};labels={r['label']:i for i,r in enumerate(eq['residuals'])};old=[P.norm(r['terms'])for r in eq['residuals']];rs=copy.deepcopy(old)
 V=lambda s:P.V(ns[s]);C=lambda n:{():n}if n else{}
 t=V('t0');F=V('crt.growth_majorant_F');A=P.add(V('shared.A'),C(1));d=P.add(t,C(2));Y=V('index0.Y');Yb=V('index2.Y');W=V('shared.W');U=V('mul.450');Z=V('shared.Zminus1')
 frame=check_parent_frame(source);frame['path']='sources/parent217.json';atoms=[(a['label'],P.norm(a['terms']))for a in frame['actual_atoms']]
 require(rs[99]==P.add(V('base0.T'),P.mul(t,t),C(1),P.scale(P.mul(A,t),-2)),'growth modulus source')
 require(rs[133]==P.add(t,C(-16),P.scale(P.mul(V('cofinal.horizon_root'),V('cofinal.horizon_root')),-1)),'old horizon source')
 rs[99]=P.add(V('base0.T'),P.mul(d,d),C(1),P.scale(P.mul(A,d),-2));rs[100]=P.add(rs[100],P.scale(Y,-2))
 eold=P.add(Yb,P.scale(t,-1),P.scale(F,-1));enew=P.add(Yb,P.scale(Y,-1),P.scale(F,-1))
 rs[144]=P.add(rs[144],P.mul(enew,enew),P.scale(P.mul(eold,eold),-1))
 substitution={0:P.scale(t,8)};rs=[P.subst(r,substitution)for r in rs]
 atoms=[(label,P.subst(a,substitution))for label,a in atoms]+[('growth_base',P.subst(d,substitution))]
 underlying=sorted({m[0]for _,a in atoms for m in a if m});bounds=[{'label':label,'terms':P.terms(a),'constant_bound':abs(a.get((),0))+sum(c*c//4 for m,c in a.items()if m)}for label,a in atoms]
 constant=max(z['constant_bound']for z in bounds)+1
 require(constant==22 and len(underlying)==43,'weak-frame census')
 rs[131]=P.add(W,C(-constant),*(P.scale(P.mul(P.V(i),P.V(i)),-1)for i in underlying))
 rs[94]=P.add(U,P.scale(W,4),P.scale(P.mul(W,Z),-8));rs[95]=P.add(V('mul.451'),P.scale(P.mul(W,U),-4),P.scale(U,-1))
 # Semantic horizon replacement is followed by exact deletion of its private coordinate.
 root=ns['cofinal.horizon_root'];require(all(root not in m for i,r in enumerate(rs)if i!=133 for m in r),'private old root')
 semantic_edits=[{'row':i,'old':P.terms(P.subst(old[i],substitution)),'new':P.terms(rs[i])}for i in [94,95,99,100,131,144]]
 semantic={'schema':'affine_weak_frame_v1','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'horizon_substitution':[[0,P.terms(substitution[0])]],'deleted_horizon_row':133,'deleted_root':root,'old_horizon':P.terms(old[133]),'edits':semantic_edits,'old_frame':frame,'atoms':bounds,'underlying_coordinates':underlying,'frame_constant':constant,'strong_frame_scale':4,'orientation_old_error':P.terms(eold),'orientation_new_error':P.terms(enew),'semantic_scope':'zero existence via newly proved signed arithmetic; not an old-witness bijection'}
 # Credited source158 private-consumer identity, specialized after prior projections.
 n=len(eq['variables']);J=P.V(n);S=V('crt.encoded.S');Sp=V('crt.encoded.Sp');K=V('mul.314');a=V('crt.encoded.a');b=V('crt.encoded.b');s=V('mul.40');p=ns['mul.337'];q=ns['mul.340']
 require(old[47]==P.add(K,P.scale(P.mul(F,Sp),-1)),'shared K source')
 require(old[60]==P.add(P.V(p),C(-1),P.scale(P.mul(F,b),-1)),'first private factor')
 require(old[62]==P.add(P.V(q),C(-1),F,P.scale(P.mul(F,a),-1)),'second private factor')
 consumers={61:P.add(P.scale(Sp,-1),P.scale(P.mul(K,b),-1),P.mul(V('mul.342'),V('mul.344')),V('sqd.13')),
 64:P.add(P.scale(S,-1),P.scale(P.mul(J,P.add(a,C(-1))),-1),V('mul.344')),
 65:P.add(S,P.mul(J,b),P.scale(Sp,-1),P.scale(P.mul(K,P.add(P.scale(a,2),P.scale(b,4),P.scale(s,2))),-1),V('sqd.14'))}
 for i,r in consumers.items():rs[i]=r
 rs.append(P.add(J,P.scale(P.mul(F,S),-1)))
 reverse={p:P.add(C(1),P.mul(F,b)),q:P.add(C(1),P.mul(F,P.add(a,C(-1))))};forward={n:P.mul(F,S)}
 contract={'schema':'shared_consumer_contraction_v1','deleted_coordinates':[p,q],'deleted_rows':[60,62],'new_coordinate':n,'forward':[[i,P.terms(a)]for i,a in forward.items()],'reverse':[[i,P.terms(a)]for i,a in reverse.items()],'edited_consumers':[[i,P.terms(a)]for i,a in consumers.items()],'new_row':P.terms(rs[-1]),'retained_K_row':47,'retained_factor_row':63,'scope':'integral polynomial zero-set bijection'}
 variables=copy.deepcopy(eq['variables'])+[{'kind':'shared_product','name':'horn.F_times_S'}];variables[0]={'kind':'unrestricted_integer','name':'affine.horizon_parameter'}
 allrows=eq['residuals']+[{'label':'shared F times S'}];removed={root,p,q};omitted={133,60,62};keep=[i for i in range(n+1)if i not in removed];ren={i:j for j,i in enumerate(keep)}
 require(all(i not in removed for j,r in enumerate(rs)if j not in omitted for m in r for i in m),'removed coordinate survives')
 out={'schema':'conzfc-affine-pooled-215-v1','domain':'unrestricted integers','polynomial':'sum(square(row) for row in residuals)','variant':'affine_weak_frame_shared_consumers215','variables':[variables[i]for i in keep],'residuals':[dict(allrows[j],terms=P.terms({tuple(ren[i]for i in m):c for m,c in r.items()}))for j,r in enumerate(rs)if j not in omitted]}
 maps={'retained_old_coordinates':keep,'old_to_new':[[i,j]for i,j in ren.items()],'retained_old_rows':[j for j in range(len(rs))if j not in omitted]}
 return out,semantic,contract,maps

def build(out):
 base,semantic,contract,maps=construct();dump(out/'semantic_certificate.json',semantic);dump(out/'consumer_certificate.json',contract);dump(out/'coordinate_map.json',maps);dump(out/'base215/equation.json',base)
 for tag in ['integer215','integer215_sparse']:
  eq=copy.deepcopy(base);rs=[P.norm(r['terms'])for r in eq['residuals']];ops=json.loads((ROOT/tag/'operations.json').read_text())
  for i,j,k in ops:
   require(i!=j and type(k)is int and k!=0,'row operation');rs[i]=P.add(rs[i],P.scale(rs[j],k))
  eq['variant']+=':'+tag;eq['residuals']=[dict(r,terms=P.terms(p))for r,p in zip(eq['residuals'],rs)]
  polynomial=P.add(*(P.mul(r,r)for r in rs));dump(out/tag/'equation.json',eq);dump(out/tag/'expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':215,'terms':P.terms(polynomial)});dump(out/tag/'metrics.json',P.metric(eq,True));dump(out/tag/'row_certificate.json',{'schema':'unimodular_row_operations_v1','input_sha256':P.digest(base),'operations':ops,'output_sha256':P.digest(eq)})
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args();build(a.out)

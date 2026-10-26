#!/usr/bin/env python3
"""Relocate the semantic Pell anchor to the existing even CRT index.

The exact semantic changes are justified by the accompanying unbounded
arithmetic proof. This file emits a literal quartic, not an exponentiation
expression or an unspecified universal-polynomial instance.
"""
from pathlib import Path
import argparse,copy,hashlib,json
from polynomial import add,scale,sub,mul,const,var,terms,poly,subst,degree,canonical,compact,expand
ROOT=Path(__file__).resolve().parents[1]
AMPLIFIER=1<<20

def build(out,explicit_index=False,quartic_index=False):
    explicit_index = explicit_index or quartic_index
    src=ROOT/'source/parent225/equation.json'
    raw=src.read_bytes();old=json.loads(raw)
    vs=copy.deepcopy(old['variables'])
    rows=[poly(r['terms']) for r in old['residuals']]
    nv=len(vs);vs.append({'name':'beta.odd_multiplier_half','kind':'signed_witness'})
    t2=None
    if quartic_index:
        t2=len(vs);vs.append({'name':'growth.t_squared','kind':'gate'})
    # Before the final even-index substitution, C is coordinate 17.
    t,x,F,B,yplus,C=map(var,[0,1,2,4,5,17])
    A=add(var(142),const(1));q=sub(var(102),const(1))
    K=var(100) if explicit_index else scale(AMPLIFIER,t)
    edits={}
    deleted={0,86,99,155,156}
    # (1) An authenticated positive majorant: F=t^(D*t).
    edits[105]=add(var(149),mul(t,t),scale(-2,mul(A,t)),const(1))
    edits[106]=add(F,scale(-1,var(191)),scale(-1,mul(t,var(192))),mul(var(149),var(150)))
    # (2) Nonunit self radix and cofinal even horizon.
    actual_representatives=add(*(var(i) for i in range(9,18)),const(-1))
    H=add(const(2),scale(4,actual_representatives))
    edits[138]=sub(var(194),mul(B,H))
    horizon_min=128 if quartic_index else 16
    edits[139]=add(t,const(-horizon_min),scale(-4,mul(var(195),var(195))))
    # (3) Reuse the C principal pair (indices188,189,190) as anchor.
    edits[144]=sub(var(208),mul(var(189),var(189)))
    edits[148]=add(var(198),scale(-1,var(188)),scale(-1,var(190)),scale(-1,mul(var(196),var(204))))
    edits[149]=add(var(199),scale(-1,C),scale(-4,mul(var(189),var(205))))
    cap=add(rows[153],mul(var(100),var(100)),scale(2,mul(var(189),var(189))),scale(-2,mul(var(192),var(192))),scale(-1,mul(C,C)))
    edits[153]=cap
    # New old-h principal pair authenticates exponent D*t.
    old_h_terms=add(mul(var(100),var(100)),scale(-2,mul(var(100),var(192))))
    edits[150]=add(sub(rows[150],old_h_terms),mul(K,K),scale(-2,mul(K,var(192))))
    # Delete the normalized factorial error from the common bound.
    edits[154]=add(rows[154],scale(4,mul(var(219),var(219))),scale(4,mul(var(140),var(140))))
    # Reconstruct the actual frame directly, including every requested atom.
    atoms=[('t',t),('t+1',add(t,const(1))),('F+t',add(F,t)),('x',x),
      ('growth_base',t),('B',B),('F',F),('y+1',yplus),
      ('a',sub(var(9),const(1)))]
    atoms += [(name,var(i)) for name,i in zip(['b','c','d','S','Sp','u','vq'],range(10,17))]
    atoms += [('C',C),('N',var(18)),('D*t',K),('q',q),('q+1',var(102)),('BH',var(194))]
    for pno,ix in [(3,103),(4,104),(5,108),(7,111),(8,114),(9,117),(10,120),(11,121),(12,124),(13,127),(14,128),(15,132),(16,135)]:
        atoms.append(('pow'+str(pno)+'.output',var(ix)))
    edits[137]=add(var(141),const(-2),*(scale(-1,mul(p,p)) for _,p in atoms))
    # Ten q+1 requests. The old h request is absent; no power for D*t at q+1.
    plus=[(103,155,156,157,0),(108,158,159,160,-1),(111,161,162,163,0),
      (114,164,165,166,0),(117,167,168,169,0),(120,170,171,172,0),
      (124,176,177,178,0),(127,179,180,181,0),(132,185,186,187,0),
      (135,188,189,190,0)]
    hp={};sp={};members=[]
    for mi,di,yi,zi,ys in plus:
        m=var(mi);d=var(di);Y=add(var(yi),const(ys));Z=var(zi);X=add(d,Z)
        hp=add(hp,mul(Y,sub(m,X)))
        sp=add(sp,mul(sub(m,d),sub(m,d)),scale(-1,mul(Y,Y)))
        members.append({'output':terms(m),'X':terms(X),'Y':terms(Y),'Z':terms(Z)})
    edits[158]=add(var(221),scale(-2,hp),scale(-1,mul(sub(scale(2,A),var(102)),var(222))))
    edits[159]=add(sp,scale(-1,mul(var(102),var(221))),var(222))
    # Every remaining use of R=F^2 becomes R=F, C becomes even, and
    # the historical V coordinate now means y+1 rather than a power output.
    newrows=[];changes=[]
    for i,row in enumerate(old['residuals']):
        if i in deleted:continue
        p=edits.get(i,rows[i])
        p=subst(p,3,F)
        p=subst(p,17,scale(2,var(17)))
        if degree(p)>2:raise ValueError(('raised degree',i))
        new=dict(row,terms=terms(p))
        newrows.append(new)
        if p!=rows[i]: changes.append({'parent_row':i,'before':terms(rows[i]),'after':terms(p)})
    beta=add(yplus,const(-1),scale(-1,mul(F,add(scale(2,var(nv)),const(1)))))
    newrows.append({'label':'beta.odd_multiplier','terms':terms(beta)})
    if quartic_index:
        newrows.append({'label':'growth.t_squared','terms':terms(sub(var(t2),mul(t,t)))})
        newrows.append({'label':'growth.index','terms':terms(sub(K,mul(var(t2),var(t2))))})
    elif explicit_index:
        newrows.append({'label':'growth.index','terms':terms(sub(K,scale(AMPLIFIER,t)))})
    vs[2]['name']='growth.F';vs[5]['name']='beta.y_plus_one';vs[17]['name']='crt.even_index_half'
    vs[100]['name']='growth.index' if explicit_index else 'deleted.derived_label'
    for ix,suffix in [(191,'X_minus_AY'),(192,'Y'),(193,'AY')]:vs[ix]['name']='growth.index_pair.'+suffix
    eq={'schema':'conzfc-relocated-anchor-v1','domain':'unrestricted integers',
      'polynomial':'sum(square(row) for row in residuals)','variables':vs,'residuals':newrows,
      'parent_equation_sha256':hashlib.sha256(raw).hexdigest(),'growth_multiplier':AMPLIFIER,
      'variant':'quartic_growth_index' if quartic_index else 'explicit_growth_index' if explicit_index else 'affine_growth_index'}
    final,ren=compact(eq)
    pol=expand(final)
    metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':degree(pol),
      'monomials':len(pol),'height':max(map(abs,pol.values())),
      'row_height':max(abs(c) for r in final['residuals'] for c,_ in r['terms'])}
    finalatoms=[{'label':name,'terms':terms(subst(p,17,scale(2,var(17))))} for name,p in atoms]
    cert={'schema':'relocated_anchor_graft_v1','parent_sha256':hashlib.sha256(raw).hexdigest(),
      'D':AMPLIFIER,'explicit_index':explicit_index,'quartic_index':quartic_index,
      'horizon_minimum':horizon_min,'t_squared_coordinate':t2,'deleted_rows':sorted(deleted),
      'changed_rows':changes,'new_rows':newrows[-(3 if quartic_index else 2 if explicit_index else 1):],
      'plus_members_before_even_chart':members,'frame_atoms_before_renumbering':finalatoms,
      'original_to_final':[[i,j] for i,j in ren.items()],
      'new_beta_multiplier':nv,'anchor':{'nominal_before_even_chart':17,'D':188,'Y':189,'Z':190},
      'new_growth_pair':{'index':terms(K),'D':191,'Y':192,'Z':193}}
    out.mkdir(parents=True,exist_ok=True)
    for fn,ob in [('equation.json',final),('uncontracted.json',eq),('certificate.json',cert),('metrics.json',metrics),
      ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(final['variables']),'terms':terms(pol)})]:
        (out/fn).write_bytes(canonical(ob))
    print(json.dumps(metrics))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--explicit-index',action='store_true');p.add_argument('--quartic-index',action='store_true')
    a=p.parse_args();build(a.output,a.explicit_index,a.quartic_index)

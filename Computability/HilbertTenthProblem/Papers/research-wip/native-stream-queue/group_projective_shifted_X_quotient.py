"""Shift the positive X quotient by the paid factor of the packed index.

For r=(q-1)S, X=q(w+S) gives X-r=qw+S>0. One existing addition
is repurposed and the separate positive bound coordinate/equation vanish.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_factored_native_index as parent

execute=parent.execute
residuals=parent.residuals
former_sos_source=parent.former_sos_source


def rewrite(old):
    assert old['variant']=='six' and old['factored_native_index']
    rows={row[0]:row for row in old['source']}
    pair=('selection__bs_X_bound','selection__wn2')
    assert pair in old['comparisons']
    assert rows['selection__bs_packed']==('selection__bs_packed','*','packed_q_minus','packed_top_sum')
    assert rows['packed_q_minus']==('packed_q_minus','-','selection__q',1)
    assert rows['selection__bs_X_bound']==('selection__bs_X_bound','+','selection__bs_packed','selection__bound_beta')
    assert rows['selection__wn2']==('selection__wn2','*','selection__w','selection__q')
    assert not any('selection__bs_X_bound' in (a,b) for _,_,a,b in old['source'])
    assert {name for name,_,a,b in old['source'] if 'selection__bound_beta' in (a,b)}=={'selection__bs_X_bound'}
    assert ('selection__ic22','selection__R16') in old['comparisons']
    assert rows['selection__L17']==('selection__L17','*','selection__R16','selection__aux_square_gap')
    source=[]
    for name,op,a,b in old['source']:
        if name=='selection__bs_X_bound':
            source.append(('shifted_native_quotient','+','selection__w','packed_top_sum'))
        elif name=='selection__wn2':source.append((name,'*','shifted_native_quotient','selection__q'))
        elif name=='selection__L17':
            source.append((name,'*','selection__ic22','selection__aux_square_gap'))
        else:source.append((name,op,a,b))
    aux=[name for name in old['auxiliaries'] if name!='selection__bound_beta']
    pairs=[p for p in old['comparisons'] if p!=pair]
    source=parent.index.parent.sort_source(source,{'x',*aux})
    assert Counter(row[1] for row in source)==Counter(row[1] for row in old['source'])
    packet=dict(old,source=source,comparisons=pairs,auxiliaries=aux,
                positive_witnesses=len(aux),equations=len(pairs),shifted_X_quotient=True,
                strong_norm_coefficient=False,
                removed_X_bound_comparison=old['comparisons'].index(pair),
                strong_comparison_index=pairs.index(('selection__ic22','selection__R16')),
                unit_comparison_index=pairs.index(('six_units',1)))
    assert len(source)==old['operations'] and len(aux)==old['positive_witnesses']-1
    return packet


def build(codes,alpha=24,beta=12,controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,'six',controller_mask,compute_length))


def polynomial_source(packet):
    """The same integer-product finalizer, independent of auxiliary coefficient."""
    source=list(packet['source']);squares=[]
    for index,(a,b) in enumerate(packet['comparisons']):
        if (a,b)==('six_units',1):continue
        name=f'outer_product_residual{index}';square=f'outer_product_square{index}'
        source += [(name,'-',a,b),(square,'*',name,name)];squares.append(square)
    total=squares[0]
    for index,square in enumerate(squares[1:],1):
        name=f'outer_product_sum{index}';source.append((name,'+',total,square));total=name
    source += [('outer_product_positive','+',total,1),
               ('outer_product_product','*','six_units','outer_product_positive'),
               ('outer_product_output','-','outer_product_product',1)]
    return source,'outer_product_output'


def lift(z,env):
    S=env['packed_top_sum'];q=env['selection__q']
    return dict(z,selection__w=z['selection__w']+S,
                selection__bound_beta=q*z['selection__w']+S)


def degree_top(packet,w):
    m,L=packet['m'],packet['scale_exponent'];nu=1+packet['compute_length']
    P=(16*(packet['alpha']*w['x']+w['height_slack'])*sum(w[f'controller__edge_hat{i}'] for i in range(m))
       if packet['compute_length'] else w['P'])
    q=16*P**L;s=2*w['selection__odd_half'];k=w['selection__eta']+w['selection__zeta']
    # r* is unchanged; X*=q*S*=r*, and a*=Y*X*.
    r=16**4*w['H2']*P**(3*L+m+15);a=s*q*r;c=k*s*q
    Q=nu*L;A0=nu*(4*L+m+15)
    n0=4*a*(k*s*q)*(w['selection__tau_gap']-k)
    n1=8*w['selection__ga']*a*a*c
    nk=-w['selection__h']*a;nl=2*nk
    n3=w['selection__i']**2*c**6;d3=6*Q+14
    degree=9*A0+8*Q+44
    degrees={'first_unit':A0+Q+5,'selection__R15':2*A0+Q+7,
             'selection__P17':d3,'index_unit':A0+3,'linear_unit':A0+3}
    tops={'first_unit':n0,'selection__R15':n1,'selection__P17':n3,'index_unit':nk,'linear_unit':nl}
    top=1
    for value in tops.values():top*=value
    strong_degree=2*A0+6;strong_top=-a*a*w['selection__f']**2
    assert degree==sum(degrees.values())+2*strong_degree
    return degree,top*strong_top**2,dict(unit_degrees=degrees,unit_tops=tops,
        unit_degree=sum(degrees.values()),unit_top=top,strong_degree=strong_degree,
        strong_top=strong_top,former_SOS_degree=2*sum(degrees.values()))


def source_checks():
    rng=random.Random(2804298);records=[];cases=0;example=None
    for codes in ((),((1,2),(3,4)),((1,2,3,4,5,6,7,8,1,2),)):
      for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet)
            prior,prior_out=parent.polynomial_source(old)
            assert len(source)==len(prior)-3
            omit=packet['removed_X_bound_comparison']
            for case in range(32):
                z={name:rng.randrange(1,6) if case<24 else rng.randrange(-3,4)
                   for name in packet['parameters']+packet['auxiliaries']}
                env=execute(source,z);lifted=lift(z,env);before=execute(prior,lifted)
                rr=residuals(old,before);assert rr[omit]==0
                target=[r for i,r in enumerate(rr) if i!=omit]
                delta=before['selection__ic22']-before['selection__R16']
                other=before['first_unit']*before['selection__R15']*before['index_unit']*before['linear_unit']
                target[packet['unit_comparison_index']]+=other*delta*before['selection__aux_square_gap']
                assert residuals(packet,env)==target
                ui=packet['unit_comparison_index'];expected=(target[ui]+1)*(1+sum(r*r for i,r in enumerate(target) if i!=ui))-1
                assert env[out]==expected
                changed={'selection__L17','selection__P17','unit_pair','four_units','five_units','six_units'}
                assert all(env[name]==before[name] for name,_,_,_ in packet['source']
                           if name in before and name not in changed)
                if case<24:
                    assert min(lifted.values())>0
                    assert env['selection__wn2']-env['selection__bs_packed']==lifted['selection__bound_beta']>0
                    assert env['packed_top_sum']>0 and env['selection__q']>=16
                cases+=1
            names=packet['parameters']+packet['auxiliaries'];weights={n:1+i%3 for i,n in enumerate(names)}
            weights['selection__tau_gap']=1
            degree,top,parts=degree_top(packet,weights)
            t=sp.Symbol('t');vals={n:sp.Poly(weights[n]*t+i+1,t) for i,n in enumerate(names)}
            # The literal four product gates are audited numerically above.
            # For degree, multiply their nonzero factor leading terms exactly
            # instead of expanding a large redundant unit polynomial.
            product_rows={
                'unit_pair':('unit_pair','*','selection__R15','selection__P17'),
                'four_units':('four_units','*','unit_pair','first_unit'),
                'five_units':('five_units','*','four_units','index_unit'),
                'six_units':('six_units','*','five_units','linear_unit')}
            rows={row[0]:row for row in packet['source']}
            assert all(rows[name]==row for name,row in product_rows.items())
            assert not any(a in product_rows or b in product_rows
                           for name,_,a,b in packet['source'] if name not in product_rows)
            env=execute([row for row in packet['source'] if row[0] not in product_rows],vals)
            for name,d in parts['unit_degrees'].items():
                assert (env[name].degree(),env[name].LC())==(d,parts['unit_tops'][name]),name
            def val(v):return env[v] if isinstance(v,str) else v
            ui=packet['unit_comparison_index'];di=packet['strong_comparison_index']
            rs={i:sp.Poly(val(a)-val(b),t) for i,(a,b) in enumerate(packet['comparisons']) if i!=ui}
            delta=rs[di]
            unit_degree=sum(env[name].degree() for name in parts['unit_degrees'])
            unit_top=sp.prod(env[name].LC() for name in parts['unit_degrees'])
            assert (unit_degree,unit_top)==(parts['unit_degree'],parts['unit_top'])
            assert (delta.degree(),delta.LC())==(parts['strong_degree'],parts['strong_top'])
            assert all(r.is_zero or r.degree()<=3 for i,r in rs.items() if i!=di)
            assert degree==unit_degree+2*delta.degree() and top==unit_top*delta.LC()**2
            # Exact leading-factor multiplication certifies final degree without
            # expanding the much larger final product polynomial.
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            old_counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in prior)
            assert counts=={'M':old_counts['M']-1,'A':old_counts['A']-2}
            m,h,p=packet['m'],packet['h'],packet['projection_additions'];f=packet['flow']['operations']
            C=3*m+3*h+p+185+f-3*min(h,3)-reuse
            assert packet['operations']==C-1 and packet['equations']==9-comp
            assert packet['positive_witnesses']==m+27-comp and len(source)==C+25-3*comp
            encoded=abs(top).to_bytes((abs(top).bit_length()+7)//8,'big')
            records.append(dict(m=m,controller_mask=reuse,compute_length=comp,auxiliary_coefficient="T_squared",
                certificate_operations=packet['operations'],equations=packet['equations'],positive_witnesses=packet['positive_witnesses'],
                polynomial_operations=len(source),polynomial_M=counts['M'],polynomial_A=counts['A'],exact_degree=degree,
                former_SOS_degree=parts['former_SOS_degree'],weighted_leading_coefficient_sign=1 if top>0 else -1,
                weighted_leading_coefficient_sha256=hashlib.sha256(encoded).hexdigest()))
            if m==16 and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (len(source),degree,packet['positive_witnesses'])==(280,4298,42)
    return dict(records=records,source_example=example,full_signed_lift_and_residual_identities=cases,
                positive_unconditional_graph_extensions=3*cases//4,signed_assignments=cases//4,
                exact_unit_and_outer_degree_audits=len(records))


def inverse_size_checks():
    cases=0
    for t in range(4,13):
        q=1<<t
        for r in (q**3+q*q+q+1,q**4-1,2*q**3+1):
            assert q<r and 2*r+1-t>2*r-t
            # 2^r>=r+1 follows by induction; this finite inequality checks
            # the remaining exponent comparison without materializing X.
            assert t<r and 2*r+1-t>=r+1
            cases+=1
    aliases=0
    for q in range(2,41):
      for S in range(1,41):
       for w in (1,2,17):
        r=(q-1)*S;X=q*(w+S)
        assert X-r==q*w+S>0 and X//q-S==w
        aliases+=1
    return dict(canonical_inverse_size_cases=cases,exact_positive_shift_identities=aliases,
                scope='Supplements the parametric bound2^(2r+1)>r² and canonical q|X theorem; no full Pell tuple is materialized.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_SHIFTED_X_QUOTIENT',source=source_checks(),inverse=inverse_size_checks(),
                scope='Complete positive witness bijection after shifting the quotient by the paid S with r=(q-1)S. q|X retained; the restored T-squared coefficient agrees with the parent on the retained strong equation.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

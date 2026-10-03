"""Complete native index units and conditional coupled-linear restoration.

The index-only rewrite preserves all positive zeros. Coupling preserves
outer coordinates by a conditional F0/r/beta normalization, not a tuple
bijection. Hosts retain a complete positive padded AND embedding.
"""
import argparse
from collections import Counter
import json
from math import prod
from pathlib import Path
import random

import native_binary_norm_units as parent

scale=parent.scale
execute=parent.execute
polynomial_source=parent.polynomial_source
degree_bound=parent.degree_bound
ledger=parent.ledger


def _guard(old):
    assert old.get('native_norm_units') and not old.get('native_index_unit')
    p=old['core_prefix'];n=lambda x:p+x
    ordinary=old['normalized_parent'] if old['normalized_strong'] else old
    ref=parent.rewrite(ordinary['unit_parent'],normalized=old['normalized_strong'])
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    canonical={n:(op,a,b) for n,op,a,b in ref['source'] if n.startswith(p)}
    assert all(rows.get(n)==row for n,row in canonical.items())
    assert old['unit_factors']==ref['unit_factors'] and old['unit_register']==ref['unit_register']
    core_pairs=[pair for pair in ref['comparisons'] if any(isinstance(v,str) and v.startswith(p) for v in pair)]
    assert all(old['comparisons'].count(pair)==1 for pair in core_pairs)
    assert old['comparisons'][-1]==(old['unit_register'],1)
    assert rows[n('q')][0:2]==('*',16)
    assert all(n(k) in old['auxiliaries'] for k in ('F0','F1','F2','bound_beta'))
    assert set(old['computed_fields']) in (set(parent.fields.VARIANTS['four']),set(parent.fields.VARIANTS['six']))
    return p,rows,set(canonical),set(core_pairs)


def index_rewrite(old):
    p,rows,canonical,core_pairs=_guard(old);n=lambda x:p+x
    alias=lambda k:old['computed_substitutions'].get(n(k),n(k))
    r,k=alias('r'),alias('k')
    pair=(k,n('R11'))
    assert rows[n('R11')]==('+',n('r1'),n('hpm1'))
    assert rows[n('r1')]==('+',r,1)
    assert pair in old['comparisons']
    assert not any(n('R11') in (a,b) for _,_,a,b in old['source'])
    assert [v for v in old['comparisons'] if n('R11') in v]==[pair]
    exports=parent.register_leaves(old.get('interfaces',{}))|parent.register_leaves(old.get('public_registers',{}))
    assert n('R11') not in exports
    factor,unit=n('index_unit'),n('index_all_units')
    assert factor not in rows and unit not in rows
    source=[(v,'-',k,n('hpm1')) if v==n('R11') else row for row in old['source'] for v in [row[0]]]
    source += [(factor,'-',n('R11'),r),(unit,'*',old['unit_register'],factor)]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    result=scale.metadata(dict(old,source=source,
        comparisons=[q for q in old['comparisons'][:-1] if q!=pair]+[(unit,1)],
        unit_register=unit,unit_factors=old['unit_factors']+[factor],
        native_index_unit=True,native_coupled_linear=False,index_parent=old,
        index_removed_comparison=pair,index_r_register=r,index_k_register=k,
        canonical_native_registers=sorted(canonical),canonical_native_comparisons=sorted(core_pairs,key=repr)))
    assert result['operations']==old['operations']+2 and result['equations']==old['equations']-1
    assert result['multiplications']==old['multiplications']+1
    return result


def couple(old):
    assert old.get('native_index_unit') and not old.get('native_coupled_linear')
    p=old['core_prefix'];n=lambda x:p+x
    rows={v:(op,a,b) for v,op,a,b in old['source']}
    consumers=lambda v:{name for name,_,a,b in old['source'] if v in (a,b)}
    r=old['index_r_register'];pair=(n('H17'),n('aux_u_rhs'))
    deleted={n('r1'),n('tr1'),n('H17')}
    expected={n('r1'):('+',r,1),n('tr1'):('+',n('r1'),r),
        n('H17'):('-',n('jc'),n('tr1')),n('H2'):('*',n('H17'),n('H17'))}
    assert all(rows[v]==row for v,row in expected.items())
    assert {v:consumers(v) for v in deleted}=={n('r1'):{n('tr1')},n('tr1'):{n('H17')},n('H17'):{n('H2')}}
    assert [q for q in old['comparisons'] if deleted&set(q)]==[pair]
    assert consumers(n('F0'))=={n('shared_sum02'),n('bs_packed')}
    assert consumers(n('bound_beta'))=={n('bs_X_bound')}
    assert rows[n('bs_X_bound')]==('+',r,n('bound_beta'))
    # Private coordinate changes cannot alter an outer source or export.
    changing={n('F0'),n('bound_beta')}
    if r==n('r'):changing.add(r)
    deps={v:{v} for v in old['parameters']+old['auxiliaries']}
    dep=lambda v:deps[v] if isinstance(v,str) else set()
    core=set(old['canonical_native_registers'])|{n('index_unit'),n('index_all_units')}
    for v,_,a,b in old['source']:
        deps[v]=dep(a)|dep(b)
        if v not in core:assert not deps[v]&changing
    assert all(not dep(n(v))&changing for v in ('q','padded_A','padded_B','F3'))
    exports=parent.register_leaves(old.get('interfaces',{}))|parent.register_leaves(old.get('public_registers',{}))
    assert not deleted&exports
    assert all(not dep(v)&changing for v in exports)
    original=set(old['canonical_native_comparisons'])
    for q in old['comparisons'][:-1]:
        if q not in original:assert not (dep(q[0])|dep(q[1]))&changing
    factor,unit=n('linear_unit'),n('coupled_all_units')
    newnames=(n('coupled_twice_K'),n('coupled_difference'),factor,unit)
    assert not set(newnames)&rows.keys()
    source=[(v,'*',n('aux_u_rhs'),n('aux_u_rhs')) if v==n('H2') else row
        for row in old['source'] for v in [row[0]] if v not in deleted]
    source += [(n('coupled_twice_K'),'+',n('R11'),n('R11')),
        (n('coupled_difference'),'-',n('aux_u_rhs'),n('jc')),
        (factor,'+',n('coupled_difference'),n('coupled_twice_K')),
        (unit,'*',old['unit_register'],factor)]
    source=scale.sort_source(source,old['parameters']+old['auxiliaries'])
    scale.checked_source(source,old['parameters'],old['auxiliaries'])
    result=scale.metadata(dict(old,source=source,
        comparisons=[q for q in old['comparisons'][:-1] if q!=pair]+[(unit,1)],
        unit_register=unit,unit_factors=old['unit_factors']+[factor],native_coupled_linear=True,
        coupled_parent=old,coupled_removed_comparison=pair,coupled_deleted_registers=sorted(deleted),
        private_restoration_coordinates=sorted(changing)))
    assert result['operations']==old['operations']+1 and result['equations']==old['equations']-1
    assert result['multiplications']==old['multiplications']+1
    assert result['additions_subtractions']==old['additions_subtractions']
    return result


def rewrite(old,*,coupled=True):
    result=index_rewrite(old)
    return couple(result) if coupled else result


def build(context='and',*,scaled=True,computed='six',normalized=True,coupled=True):
    if context in ('and','motion','toggle'):
        old=parent.build(context,scaled=scaled,computed=computed,normalized=normalized)
    else:
        assert context in ('program','actions') and scaled and computed=='six' and normalized
        import wang_b_packed_program as program
        old=program.build(literal_input=True)
        if context=='actions':
            import wang_b_computed_actions as actions
            old=actions.rewrite(old)
    return rewrite(old,coupled=coupled)


def restore_to_index(packet,values,epsilon):
    """Valid positive restoration at coupled zeros; not an off-zero bijection."""
    assert packet['native_coupled_linear'] and epsilon in (-1,1)
    p=packet['core_prefix'];delta=1-epsilon;result=dict(values)
    result[p+'F0']-=delta;result[p+'bound_beta']+=delta
    if packet['index_r_register']==p+'r':result[p+'r']-=delta
    return result


def closure(packet,sos=False):
    source,out=polynomial_source(packet,sum_of_squares=sos)
    rows={n:(a,b) for n,_,a,b in source};seen=set()
    def visit(v):
        if not isinstance(v,str) or v not in rows or v in seen:return
        seen.add(v)
        for x in rows[v]:visit(x)
    visit(out)
    assert len(rows)==len(source) and seen==set(rows)


def audit(packet,cases=24,seed=731904):
    rng=random.Random(seed);old=packet['coupled_parent'] if packet['native_coupled_linear'] else packet['index_parent']
    source,out=polynomial_source(packet);ss,so=polynomial_source(packet,sum_of_squares=True)
    p=packet['core_prefix'];at=lambda e,v:e[v] if isinstance(v,str) else v
    removed=packet['coupled_removed_comparison'] if packet['native_coupled_linear'] else packet['index_removed_comparison']
    for case in range(cases):
        positive=case<cases//2
        z={n:rng.randrange(1,6) if positive else rng.randrange(-4,5) for n in packet['parameters']+packet['auxiliaries']}
        before=execute(old['source'],z);env=execute(source,z)
        factors={n:before[n] for n in old['unit_factors']}
        if packet['native_coupled_linear']:
            U,V=before[p+'H17'],before[p+'aux_u_rhs']
            factors[p+'P17']+=before[p+'R16']*(V*V-U*U)
            factors[p+'linear_unit']=2*before[p+'index_unit']-1-(U-V)
        else:
            a,b=removed;factors[p+'index_unit']=at(before,a)-at(before,b)+1
        assert all(env[n]==factors[n] for n in packet['unit_factors'])
        rr=[at(before,a)-at(before,b) for a,b in old['comparisons'][:-1] if (a,b)!=removed]
        assert rr==[at(env,a)-at(env,b) for a,b in packet['comparisons'][:-1]]
        W=prod(factors.values());R=sum(v*v for v in rr)
        assert env[out]==W*(1+R)-1
        assert execute(ss,z)[so]==(W-1)**2+R
        if positive:
            assert env[p+'q']>=16 and env[p+'F3']>0
    closure(packet);closure(packet,True)
    return dict(assignments=cases,signed=cases//2,complete_finalizer_identities=2*cases)


def pell(A,n):
    x,y=1,0
    for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
    return x,y


def sign_checks():
    rng=random.Random(72830);bounds=ratios=0
    for q in range(16,97):
      for checksum in (-1,1):
       for trial in range(4):
        total=q-checksum;cuts=sorted(rng.sample(range(1,total),3));F=[cuts[0],cuts[1]-cuts[0],cuts[2]-cuts[1],total-cuts[2]]
        r=sum(f*q**j for j,f in enumerate(F));X=r+1;Y=q;E=X*Y
        assert q**3+q*q+q+1<=r<q**4 and r>=4369
        assert E>2*r+3 and Y*(r-1)>2*(2*r+3)
        for eps in (-1,1):
         for lam in (-1,1):assert 0<2*(r+eps)-lam<E
        bounds+=1
    for X in range(2,10):
     for Y in range(2,10):
      for n in range(1,7):
       A=Y*(X+1)+2;P=2*X*Y*Y+1;Q=2*A*A-1;k=pell(P,n)[1]
       assert P>A and Q>P and 2*A>Y+1
       assert pell(A,2*n)[1]==2*A*pell(Q,n)[1]>k*(Y+1)
       ratios+=1
    for eps in (-1,1):assert (2-eps)%16==(1 if eps==1 else 3)
    return dict(weak_checksum_bounds=bounds,exact_pell_duplications=ratios,
                scope='Finite arithmetic supplements; no full Pell zero is materialized.')


def restoration_checks():
    total=negative=0
    for scaled in (False,True):
     for computed in ('four','six'):
      for normalized in (False,True):
       packet=build(scaled=scaled,computed=computed,normalized=normalized)
       old=packet['coupled_parent'];source,out=polynomial_source(packet);ps,po=polynomial_source(old)
       p='';rreg=packet['index_r_register']
       for eps in (-1,1):
        for trial in range(8):
         z={n:2 for n in packet['parameters']+packet['auxiliaries']}
         z.update(P=8,Hhat=1,Mhat=1,Zhat=1,F1=4,F2=2,F0=128-eps-14,f=1)
         env=execute(packet['source'],z);r=env['bs_packed']
         if computed=='four':z['r']=r
         if not scaled:
          z['w']=r//128+1;z['bound_beta']=z['w']*128-r
         env=execute(packet['source'],z)
         z['zeta']=r+env['hpm1']+eps-z['eta']
         env=execute(packet['source'],z)
         if computed=='four':z['c']=env['R10a']
         env=execute(packet['source'],z)
         z['o']=(z['j']+1)*env['R10a']-2*env['R11']+1
         if trial>=4:z['i']=-z['i']
         env=execute(source,z)
         assert (env['bs_q'],env['index_unit'],env['linear_unit'])==(eps,eps,1)
         restored=restore_to_index(packet,z,eps);before=execute(ps,restored)
         at=lambda e,v:e[v] if isinstance(v,str) else v
         pair=packet['coupled_removed_comparison']
         assert at(before,pair[0])==at(before,pair[1])
         rr=[at(before,a)-at(before,b) for a,b in old['comparisons'] if (a,b)!=pair]
         assert rr==[at(env,a)-at(env,b) for a,b in packet['comparisons']]
         assert before[po]==env[out]
         if trial<4:assert min(restored.values())>0
         total+=1;negative+=eps==-1
    return dict(conditional_restorations=total,negative_index_cases=negative,
                scope='Exact conditional whole-output identities with Qc=Nk=epsilon and Nl=1; norm zeros are not claimed.')


def verify():
    records=[]
    for context in ('and','motion','toggle'):
     for scaled in (False,True):
      for computed in ('four','six'):
       for normalized in (False,True):
        for coupled in (False,True):
         packet=build(context,scaled=scaled,computed=computed,normalized=normalized,coupled=coupled)
         record=dict(context=context,scaled=scaled,computed=computed,normalized=normalized,coupled=coupled,
             ledger=ledger(packet),audit=audit(packet,seed=731904+len(records)))
         records.append(record)
    for context in ('program','actions'):
     for coupled in (False,True):
      packet=build(context,coupled=coupled)
      records.append(dict(context=context,coupled=coupled,ledger=ledger(packet),audit=audit(packet,seed=731904+len(records))))
    standalone=build();src,out=polynomial_source(standalone)
    assert len(src)==80 and standalone['equations']==3 and standalone['witnesses']==15
    # New nested private exports are rejected even if the core rows are unchanged.
    invalid=dict(parent.build(),interfaces={'nested':{'ports':['F0']}})
    try:rewrite(invalid)
    except AssertionError:pass
    else:raise AssertionError('private changing coordinate was exported')
    return dict(status='PASS_NATIVE_BINARY_INDEX_COUPLED_UNITS',ledgers=records,
        assignments=sum(r['audit']['assignments'] for r in records),
        signed=sum(r['audit']['signed'] for r in records),
        complete_finalizer_identities=sum(r['audit']['complete_finalizer_identities'] for r in records),
        signs=sign_checks(),conditional_restoration=restoration_checks(),
        standalone=dict(source=src,output=out,parameters=standalone['parameters'],auxiliaries=standalone['auxiliaries'],ledger=ledger(standalone)),
        scope='Index-only same positive zeros; coupling preserves outer coordinates by conditional native normalization. No universal operation bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['standalone']['ledger'])

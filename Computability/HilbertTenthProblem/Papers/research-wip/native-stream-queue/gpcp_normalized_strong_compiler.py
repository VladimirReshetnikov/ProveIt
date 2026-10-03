"""Normalize all three strong witnesses of a regrouped complete compiler.

The history checksum remains a separate equation.  Only accepted outer
projections agree: the converse reconstructs fifteen canonical auxiliaries.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import gpcp_sparse_tm_compiler as parent
import gpcp_ordered_sparse_tm as ordered
import gpcp_complete_fixed_program_units as complete
import pcp_normalized_strong_history_units as single

execute=parent.execute
scalar=parent.scalar
PREFIXES=('geo__','and__','hist__and__')


def rewrite(old):
    assert old.get('unit_product',True) and old.get('regroup') is True
    assert tuple(old['native_prefixes'])==PREFIXES and len(old['unit_factors'])==10
    checksum=('hist__and__bs_q',1)
    assert checksum in old['comparisons'][:-1]
    assert 'hist__and__bs_q' not in old['unit_factors']
    assert old['unit_factors'].count('and__bs_q')==1
    rebuilt={p+n for p in PREFIXES for n in ('f','i','j','o','y_aux')}
    deps={n:{n} for n in old['parameters']+old['auxiliaries']}
    dep=lambda v:deps[v] if isinstance(v,str) else set()
    for name,_,a,b in old['source']:deps[name]=dep(a)|dep(b)
    for p in PREFIXES:
        for field in ('f','i','j','o','y_aux'):
            assert all(name.startswith(p) for name,_,a,b in old['source'] if p+field in (a,b))
    exceptions={(p+'ic22',p+'R16') for p in PREFIXES}|{(p+'H17',p+'aux_u_rhs') for p in PREFIXES}
    for a,b in old['comparisons'][:-1]:
        if (a,b) not in exceptions:assert not (dep(a)|dep(b))&rebuilt
    for factor in old['unit_factors']:
        if factor not in {p+'P17' for p in PREFIXES}:assert not dep(factor)&rebuilt
    p=old;N=old['history_packet']['scale_exponent']
    for prefix in PREFIXES:
        p=single.rewrite(dict(p,core_prefix=prefix,scale_exponent=N))
    assert checksum in p['comparisons'][:-1]
    assert 'hist__and__bs_q' not in p['unit_factors']
    assert len(p['source'])==old['operations']+6
    assert p['multiplications']==old['multiplications']+6
    assert p['additions_subtractions']==old['additions_subtractions']
    assert p['equations']==old['equations']-3 and p['auxiliaries']==old['auxiliaries']
    strong=[prefix+'f_square_minus_one' for prefix in PREFIXES]
    p.update(parent_packet=old,normalized_strong_factors=strong,
        removed_strong_comparisons=[(prefix+'ic22',prefix+'R16') for prefix in PREFIXES],
        all_norm_factors=old['all_norm_factors']+strong,normalized_three_core=True)
    for key in ('exact_degree','alternative_SOS_degree','normalized_strong_factor','removed_strong_comparison'):
        p.pop(key,None)
    return p


def build_for_tm(*args,**options):return rewrite(parent.build_for_tm(*args,**options))
def odd_machine(**options):return rewrite(parent.odd_machine(**options))
def build_universal(**options):return rewrite(parent.build_universal(**options))
def build_ordered_universal(**options):return rewrite(ordered.build(**options))
def polynomial_source(packet):return complete.polynomial_source(packet)


def lift(packet,values):
    env=execute(packet['source'],values)
    return dict(values,**{p+'i':env[p+'A']*values[p+'i'] for p in PREFIXES})


def audit_identity(packet,values):
    old=packet['parent_packet'];env=execute(packet['source'],values)
    before=execute(old['source'],lift(packet,values));factors={}
    for p in PREFIXES:
        N=env[p+'f_square_minus_one'];Delta=env[p+'A']
        r=before[p+'ic22']-before[p+'R16']
        assert r==Delta*(1-N)
        assert env[p+'P17']==before[p+'P17']+r*env[p+'aux_square_gap']
        factors[p+'P17']=before[p+'P17']+r*env[p+'aux_square_gap']
        factors[p+'f_square_minus_one']=N
    for name in old['unit_factors']:
        if name not in factors:
            assert env[name]==before[name];factors[name]=before[name]
    removed=set(packet['removed_strong_comparisons'])
    others=[scalar(a,before)-scalar(b,before) for a,b in old['comparisons'][:-1] if (a,b) not in removed]
    assert others==[scalar(a,env)-scalar(b,env) for a,b in packet['comparisons'][:-1]]
    assert env['hist__and__bs_q']==before['hist__and__bs_q']
    product=1
    for name in packet['unit_factors']:product*=factors[name]
    assert env[packet['unit_register']]==product
    source,out=polynomial_source(packet)
    assert execute(source,values)[out]==product*(1+sum(v*v for v in others))-1


def degree_audit(packet):
    """Literal homogeneous propagation plus the fully checked main-norm identity."""
    variables=packet['parameters']+packet['auxiliaries']
    degree={n:1 for n in variables};top={n:1+j%3 for j,n in enumerate(variables)}
    for p in PREFIXES:top[p+'tau_gap']=1;top[p+'eta']=top[p+'zeta']=1
    d=lambda v:degree[v] if isinstance(v,str) else 0
    c=lambda v:top[v] if isinstance(v,str) else v
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    overrides={p+'R15':p for p in PREFIXES}
    for name,op,a,b in packet['source']:
        da,db=d(a),d(b)
        if op=='*':degree[name],top[name]=da+db,c(a)*c(b)
        else:
            degree[name]=max(da,db)
            ca=c(a) if da==degree[name] else 0;cb=c(b) if db==degree[name] else 0
            top[name]=ca+cb if op=='+' else ca-cb
        if name in overrides:
            p=overrides[name];X=p+'wn2';ac=p+'cam2';G=p+'gam';aa=p+'R12';cc=p+'R10a'
            expected={p+'R15':('-',p+'L15',p+'Ac2'),p+'R14':('+',p+'D1',G),
                p+'D1':('+',X,ac),ac:('*',cc,aa),G:('*',p+'ga',p+'a4m5'),
                p+'a4m5':('+',p+'a4',3),p+'a4':('*',4,aa),
                p+'A':('+',p+'a_square',p+'a4m5'),p+'a_square':('*',aa,aa),
                p+'c2':('*',cc,cc),p+'Ac2':('*',p+'A',p+'c2'),
                p+'L15':('*',p+'R14',p+'R14')}
            assert all(rows[n]==row for n,row in expected.items())
            high=d(ac)+d(G)
            assert high>max(2*d(X),d(X)+d(ac),d(X)+d(G),2*d(G),d(p+'a4m5')+2*d(cc))
            degree[name],top[name]=high,2*c(ac)*c(G)
    e=d('geo__wn2')-1;v=d('and__q');dd=d('hist__and__q')
    N=packet['history_packet']['scale_exponent'];nu=dd//N
    assert dd==N*nu and e in (1,2) and v==(packet['width']+1)*e+1
    expected={}
    for p,z,aux_degree in [('geo__',e,14*e+24),('and__',v,18*v+20),
                           ('hist__and__',dd,20*dd-6*nu+20)]:
        expected.update({p+'R15':5*z+7,p+'P17':aux_degree,p+'first_unit':3*z+5,
                         p+'f_square_minus_one':8*z+14})
        a,cc,U,i=c(p+'R12'),c(p+'R10a'),c(p+'H17'),c(p+'i')
        assert c(p+'R15')==8*c(p+'ga')*a*a*cc
        assert c(p+'P17')==a**4*i*i*cc**4*U*U
        assert c(p+'f_square_minus_one')==-a*a*i*i*cc**4
    expected['and__bs_q']=v
    assert {n:d(n) for n in packet['unit_factors']}==expected
    residuals=[]
    for a,b in packet['comparisons'][:-1]:
        deg=max(d(a),d(b));coef=(c(a) if d(a)==deg else 0)-(c(b) if d(b)==deg else 0)
        residuals.append((a,b,deg,coef))
    maximum=max(z[2] for z in residuals)
    assert maximum==max(3*v+1,4*dd-3*nu+1)
    outer=sum(z[3]**2 for z in residuals if z[2]==maximum)
    expected_outer=6*sum(c(p+'bs_packed')**2 for p in ('and__','hist__and__') if d(p+'bs_packed')==maximum)
    assert outer==expected_outer and outer>0
    unit=packet['unit_register'];product_degree=30*e+35*v+36*dd-6*nu+142
    assert d(unit)==product_degree
    coefficient=c(unit)*outer;assert coefficient
    blob=abs(coefficient).to_bytes((abs(coefficient).bit_length()+7)//8,'big')
    return dict(exact_degree=product_degree+2*maximum,input_degree=e,recoder_width=packet['width'],
        recoder_AND_scale_degree=v,history_length_degree=nu,history_scale_exponent=N,
        history_scale_degree=dd,unit_degree=product_degree,maximum_outer_degree=maximum,
        factor_degrees={n:d(n) for n in packet['unit_factors']},
        maximum_outer_residuals=[[a,b,deg] for a,b,deg,_ in residuals if deg==maximum],
        leading_sign=1 if coefficient>0 else -1,leading_bits=abs(coefficient).bit_length(),
        leading_sha256=hashlib.sha256(blob).hexdigest(),all_main_norm_prerequisites_checked=True,
        all_new_strong_and_auxiliary_leading_forms_checked=True)


def ledger(packet):
    source,_=polynomial_source(packet);counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    old=packet['parent_packet'];oldsource,_=polynomial_source(old)
    assert len(source)==len(oldsource)-3
    assert counts==dict(M=old['multiplications']+old['equations']+3,
                       A=old['additions_subtractions']+2*old['equations']-7)
    return dict(certificate=dict(operations=packet['operations'],multiplications=packet['multiplications'],
        additions_subtractions=packet['additions_subtractions']),equations=packet['equations'],
        witnesses=packet['witnesses'],polynomial=dict(operations=len(source),multiplications=counts['M'],
        additions_subtractions=counts['A']),degree=degree_audit(packet))


def polynomial_degree_check(packet):
    """Independent actual polynomial evaluation on small composed sources."""
    import sympy as sp
    z=sp.Symbol('z');names=packet['parameters']+packet['auxiliaries']
    weights={name:1+j%3 for j,name in enumerate(names)}
    for p in PREFIXES:weights[p+'tau_gap']=1;weights[p+'eta']=weights[p+'zeta']=1
    values={name:sp.Poly(weights[name]*z+j+1,z) for j,name in enumerate(names)}
    products={name for name,_,_,_ in packet['source']
              if name.startswith('complete_unit_product') or name.endswith('normalized_all_units')}
    source=[row for row in packet['source'] if row[0] not in products]
    env=execute(source,values);expected=degree_audit(packet)
    factors=[sp.Poly(env[n],z) for n in packet['unit_factors']]
    assert {n:f.degree() for n,f in zip(packet['unit_factors'],factors)}==expected['factor_degrees']
    outer=[sp.Poly(scalar(a,env)-scalar(b,env),z) for a,b in packet['comparisons'][:-1]]
    maximum=max(v.degree() for v in outer)
    assert maximum==expected['maximum_outer_degree']
    coefficient=sum(v.LC()**2 for v in outer if v.degree()==maximum)
    for f in factors:coefficient*=f.LC()
    coefficient=int(coefficient);blob=abs(coefficient).to_bytes((abs(coefficient).bit_length()+7)//8,'big')
    assert hashlib.sha256(blob).hexdigest()==expected['leading_sha256']
    return dict(exact_degree=sum(f.degree() for f in factors)+2*maximum,
                leading_sha256=expected['leading_sha256'],all_factors_and_outer_residuals_evaluated=True)


def verify():
    rng=random.Random(807205092);records=[];identities=signed=0
    for inline in (False,True):
      for code in (None,8,'parameter'):
       for choice in ('per_tile','slope_classes'):
        p=odd_machine(inline_initial=inline,program_code=code,history_choice=choice)
        records.append(dict(kind='ordinary_odd',inline_initial=inline,program_code=code,
                            history_choice=choice,**ledger(p)))
        for case in range(16):
            values={n:rng.randrange(1,5) if case<8 else rng.randrange(-3,4)
                    for n in p['parameters']+p['auxiliaries']}
            audit_identity(p,values);identities+=1;signed+=case>=8
    # An explicit width-dominant example makes the recoder's outer square
    # dominate a supplied short history instead of assuming history dominance.
    tiles=(((0,),(1,)),)
    for code in (None,8,'parameter'):
        old=complete.build(tiles,100,(2,3),(4,5),(5,2,6,4),inline_initial=False,
                           layout='contiguous',program_code=code)
        p=rewrite(old);records.append(dict(kind='width100_singleton',program_code=code,**ledger(p)))
        for case in range(8):
            values={n:rng.randrange(-2,4) for n in p['parameters']+p['auxiliaries']}
            audit_identity(p,values);identities+=1;signed+=1
    universal=[];example=None
    for inline in (False,True):
      for variant in ('sparse_tuned','balanced'):
        p=build_universal(inline_initial=inline,variant=variant)
        rec=ledger(p);universal.append(dict(inline_initial=inline,code_variant=variant,**rec))
        for case in range(16):
            values={n:rng.randrange(1,4) if case<8 else rng.randrange(-2,3)
                    for n in p['parameters']+p['auxiliaries']}
            audit_identity(p,values);identities+=1;signed+=case>=8
        if inline and variant=='sparse_tuned':
            assert rec['polynomial']==dict(operations=807,multiplications=352,additions_subtractions=455)
            assert rec['certificate']['operations']==736 and rec['equations']==24 and rec['witnesses']==125
            assert rec['degree']['exact_degree']==205092
            source,out=polynomial_source(p)
            example=dict(ledger=rec,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
                source=p['source'],comparisons=p['comparisons'],polynomial_finalizer=source[p['operations']:],
                output=out,retained_history_checksum=['hist__and__bs_q',1])
    ordered_records=[]
    for inline in (False,True):
        p=build_ordered_universal(inline_initial=inline);rec=ledger(p)
        ordered_records.append(dict(inline_initial=inline,**rec))
        assert rec['polynomial']['operations']==(805 if inline else 808)
        assert rec['degree']['exact_degree']==(205092 if inline else 8532)
        if inline:
            assert rec['polynomial']==dict(operations=805,multiplications=352,additions_subtractions=453)
        for case in range(16):
            values={n:rng.randrange(1,4) if case<8 else rng.randrange(-2,3)
                    for n in p['parameters']+p['auxiliaries']}
            audit_identity(p,values);identities+=1;signed+=case>=8
    rejected=[]
    for kwargs in (dict(unit_product=False),dict(regroup=False)):
        try:rewrite(parent.odd_machine(**kwargs))
        except AssertionError:rejected.append(kwargs)
    assert len(rejected)==2
    # Simultaneous canonical choices for three independent native parameters;
    # no full packed-history Pell zero is claimed by these finite cases.
    triples=[]
    for shift in range(3):
        triples.append([single.canonical.canonical(A,3) for A in range(2+shift,5+shift)])
    exact=[]
    for code in (None,'parameter'):
        old=complete.build(tiles,4,(2,3),(4,5),(5,2,6,4),inline_initial=False,
                           layout='contiguous',program_code=code)
        exact.append(polynomial_degree_check(rewrite(old)))
    return dict(status='PASS_GPCP_NORMALIZED_STRONG_COMPILER',variant_ledgers=records,
        universal_ledgers=universal,ordered_universal_ledgers=ordered_records,
        example=example,complete_correction_output_identities=identities,
        signed_assignments=signed,canonical_three_core_fixtures=triples,
        actual_weighted_affine_polynomial_audits=exact,
        rejected_ineligible_parents=rejected,full_packed_Pell_zeros_materialized=False,
        scope='Same positive outer projection of the eligible safely regrouped complete parent; '
              'history checksum retained separately; fifteen canonical auxiliaries may be rebuilt. '
              'Sparse explicit universal807, ordered universal805, and generic compiler variants; no all-tuples bijection.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])

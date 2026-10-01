"""UNRESOLVED 86-operation candidate: omit the strengthened Z slack.

Exact signed parent substitution and positive forward inclusion are proved.
The reverse positive projection is proved only on alpha>Z.  The supplied
outer family obstructs the old positivity bootstrap, not universality.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import sympy as sp

import complete75_normalized_strong87 as parent

RETAINED=parent.RETAINED
FACTOR_NAMES=parent.FACTOR_NAMES
eliminated=parent.eliminated


def sources():
    original,old,pairs,_=parent.sources()
    nodes={name:(op,a,b) for name,op,a,b in old}
    consumers={name for name,op,a,b in old if 'q_minus_FZ' in (a,b)}
    assert consumers=={'C_after_alpha','gap'}
    assert nodes.pop('q_minus_FZ')==('-','q_minus_F','Z')
    assert nodes['C_after_alpha']==('-','q_minus_FZ','alpha')
    assert nodes['gap_product']==('*','repunit','q_minus_F')
    assert nodes['gap']==('+','gap_product','q_minus_FZ')
    nodes['C_after_alpha']=('-','q_minus_F','alpha')
    nodes['gap_product']=('*','q','q_minus_F')
    nodes['gap']=('-','gap_product','Z')
    source=[(name,*nodes[name]) for name,_,_,_ in old if name in nodes]
    return original,source,pairs,source+[('polynomial','-','eight_units',1)]


def verify_source():
    _,source,pairs,polynomial=sources();_,old,oldpairs,oldpoly=parent.sources()
    before={n:(op,a,b) for n,op,a,b in old};after={n:(op,a,b) for n,op,a,b in source}
    assert before.keys()-after.keys()=={'q_minus_FZ'} and not after.keys()-before.keys()
    assert {n for n in after if before[n]!=after[n]}=={'C_after_alpha','gap_product','gap'}
    known=set(RETAINED+eliminated.baseline.prior.CONSTANTS+['x','Bm1','Kconstant','twice_cell_bits'])
    for n,op,a,b in polynomial:
        assert n not in known and all(isinstance(v,int) or v in known for v in (a,b))
        known.add(n)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in polynomial)
    assert counts=={'M':48,'A':38} and pairs==oldpairs==[('eight_units',1)]
    rng=random.Random(86203);signed=restricted=nonpositive_restoration=forward=0
    for case in range(512):
        v={n:rng.randrange(1,10) if case<384 else rng.randrange(-9,10) for n in RETAINED+['x']}
        if case<192:v['alpha']+=v['Z']
        B=rng.choice((16,32,64,256));d=B.bit_length()-1
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        new=eliminated.run(polynomial,eliminated.fixed_inputs({**v,**fixed}))
        restored={**v,'alpha':v['alpha']-v['Z']}
        oldenv=eliminated.run(oldpoly,eliminated.fixed_inputs({**restored,**fixed}))
        assert all(new[n]==oldenv[n] for n in FACTOR_NAMES+('polynomial','r_lhs','marked_rhs','W','gap'))
        assert new['gap']==new['q']*(new['q']-v['F'])-v['Z']
        signed+=case>=384
        restricted+=case<384 and restored['alpha']>0
        nonpositive_restoration+=case<384 and restored['alpha']<=0
        if case<384:
            old_original=eliminated.run(oldpoly,eliminated.fixed_inputs({**v,**fixed}))
            lifted={**v,'alpha':v['alpha']+v['Z']}
            assert min(lifted[n] for n in RETAINED+['x'])>0
            liftedenv=eliminated.run(polynomial,eliminated.fixed_inputs({**lifted,**fixed}))
            assert old_original['polynomial']==liftedenv['polynomial'];forward+=1
    assert restricted and nonpositive_restoration
    return dict(certificate=dict(operations=85,multiplications=48,additions_subtractions=37,equations=1,witnesses=19),
        polynomial=dict(operations=86,multiplications=48,additions_subtractions=38,degree=203,witnesses=19),
        status='UNRESOLVED_CANDIDATE_NOT_A_UNIVERSAL_BOUND',
        removed_register='q_minus_FZ',changed_registers=['C_after_alpha','gap_product','gap'],
        unchanged_literal_gates=82,retained_positive_witnesses=RETAINED,
        comparisons=pairs,polynomial_schedule=polynomial,
        exact_complete_signed_substitution_cases=512,signed_cases=signed,
        positive_forward_inclusion_cases=forward,positive_inverse_domain_cases=restricted,
        nonpositive_old_alpha_cases=nonpositive_restoration,
        parent_substitution='alpha_old=alpha_candidate-Z',
        positive_forward_map='alpha_candidate=alpha_old+Z',
        proved_inverse_domain='alpha_candidate>Z')


def verify_degree():
    z=sp.Symbol('z');polynomial=sources()[3];records=[]
    for B,d,shift in ((16,4,0),(64,6,1),(256,8,2)):
        scales={n:1+(j+shift)%4 for j,n in enumerate(RETAINED+['x'])}
        scales.update(tau_gap=5,eta=1,zeta=2,Jrep=2,x=1)
        values={n:sp.Poly(scales[n]*z+j+1,z) for j,n in enumerate(RETAINED+['x'])}
        fixed=dict(B=B,DC=3,DR=5,MC=B-2,MF=4,cell_bits=d,inner_bits=3)
        env=eliminated.run(polynomial,eliminated.fixed_inputs({**values,**fixed}))
        factors=[sp.Poly(env[n],z) for n in FACTOR_NAMES]
        assert tuple(p.degree() for p in factors)==parent.FACTOR_DEGREES
        Q=(B-1)*scales['Jrep'];k=scales['eta']+scales['zeta']
        C=Q-scales['F']-scales['alpha']-2*d*scales['x']
        top=(32*Q**135*scales['h']**2*(scales['rho']+scales['sigma'])*scales['delta']**2
             *scales['i']**4*k**12*scales['w']**17*scales['s']**28*C*(2*scales['tau_gap']-k))
        result=sp.Poly(env['polynomial'],z)
        assert top and result.degree()==203 and result.LC()==top
        records.append(dict(B=B,cell_bits=d,degree=203,leading_coefficient=str(top)))
    return dict(exact_degree=203,fixtures=records,
        highest_form='parent87 highest form after alpha_old=alpha_candidate-Z',
        C_top='(B-1)*Jrep-F-alpha-2*cell_bits*x')


def verify_outer_obstruction():
    polynomial=sources()[3];records=[]
    for j in range(64):
        v={n:1 for n in RETAINED+['x']}
        v.update(Jrep=1,F=1,alpha=3,Z=265+4*j,w=11,zplus=12038)
        fixed=dict(B=16,DC=3,DR=5,MC=10,MF=12,cell_bits=4,inner_bits=3)
        # These are the original masks; fixed_inputs pays the source's
        # historical MF_source=MF+B-1 convention, without changing a gate.
        assert fixed['MC']%4==2 and fixed['MF']%8==4
        assert fixed['MC'].bit_count()+fixed['MF'].bit_count()==fixed['cell_bits']
        env=eliminated.run(polynomial,eliminated.fixed_inputs({**v,**fixed}))
        assert min(v.values())>0
        assert env['q']==16 and env['marked_rhs']==4 and env['wn2']==45056
        assert env['mask']==442 and env['gap']==-25-4*j
        assert env['r_lhs']==-5933-1020*j and env['r_lhs']%4==3
        assert env['norm_transport']==1 and v['alpha']-v['Z']<0
        assert env['polynomial']!=0
        records.append(dict(Z=v['Z'],C=env['marked_rhs'],X=env['wn2'],R=env['r_lhs'],
                            old_alpha=v['alpha']-v['Z'],transport_unit=1,
                            complete_polynomial_zero=False))
    return dict(fixed=dict(B=16,J=1,x=1,F=1,alpha=3,w=11,zplus=12038,
                          DC=3,DR=5,MC=10,MF=12,cell_bits=4,inner_bits=3),
        family='Z=265+4j, j>=0; R=-5933-1020j',cases=records,
        scope='Only the positive outer transport/width bootstrap is refuted. The other native units are not asserted; none of these fixtures is a full candidate zero. Scalar mask congruences/population hold, without claiming DC/DR are an instantiated universal program.')


def verify():
    return dict(status='PASS_SCOPED_WEAKENED_BOUND86_CANDIDATE_AUDIT',
        source=verify_source(),degree=verify_degree(),outer_obstruction=verify_outer_obstruction(),
        conclusion='Universal completeness is inherited from87. Positive soundness for alpha<=Z remains open; no below87 universal bound or lower bound is proved.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(result['status']);print(result['source']['polynomial']);print(result['conclusion'])

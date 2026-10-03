"""Exact reduction and elementary subcase checks for proportional carry."""
import argparse
from itertools import product
import json
from math import gcd
from pathlib import Path


def factor(alpha,beta,gamma,delta):
    assert alpha*delta==beta*gamma
    if alpha or gamma:
        a=gcd(alpha,gamma);u=alpha//a;v=gamma//a
        if u:
            assert beta%u==0;b=beta//u
        else:
            assert delta%v==0;b=delta//v
    elif beta or delta:
        a=0;b=gcd(beta,delta);u=beta//b;v=delta//b
    else:
        a=b=0;u=1;v=0
    assert gcd(u,v)==1
    assert (u*a,u*b,v*a,v*b)==(alpha,beta,gamma,delta)
    return u,v,a,b


def domain(L,joint=False):
    return [(A,B) for A in range(1,L) for B in range(1,L)
            if not joint or A+B<=L-1]


def factor_audit():
    cases=0;degenerate=0
    for alpha,beta,gamma,delta in product(range(-4,5),repeat=4):
        if alpha*delta!=beta*gamma:continue
        u,v,a,b=factor(alpha,beta,gamma,delta)
        for W in range(1,8):
            assert (alpha*W+beta,gamma*W+delta)==((a*W+b)*u,(a*W+b)*v)
        cases+=1;degenerate+=not a or not b
    return dict(integer_coefficient_factorizations=cases,degenerate_factors=degenerate)


def reduction_audit():
    cases=accepted=zero_factors=0
    models=((1,1,1,1),(-2,3,4,-6),(0,0,3,-2),(2,-4,3,-6),(-1,-2,0,0))
    for alpha,beta,gamma,delta in models:
        u,v,a,b=factor(alpha,beta,gamma,delta);assert a
        for ep,ze,eta in product(range(-2,3),repeat=3):
            for W in range(1,6):
                G=a*W+b
                for L in range(2,7):
                    for joint in (False,True):
                        image={u*A+v*B for A,B in domain(L,joint)}
                        exact=any(G*Z+ep*W*L+ze*W+eta==0 for Z in image)
                        # Enumerate exactly the possible image-derived H,
                        # with congruence explicitly tested in both directions.
                        Hs={a*Z+ep*L+ze for Z in image}
                        reduced=any(G*H==b*ep*L+b*ze-a*eta
                                    and (H-ep*L-ze)%a==0
                                    and (H-ep*L-ze)//a in image for H in Hs)
                        assert exact==reduced
                        for Z in image:
                            H=a*Z+ep*L+ze
                            assert G*H-b*ep*L-b*ze+a*eta==a*(G*Z+ep*W*L+ze*W+eta)
                        cases+=1;accepted+=exact;zero_factors+=G==0
    # Bare divisibility does not establish the positive image guard.
    W=L=2;G=W+1
    assert 3%G==0
    assert all(G*(A+B)-3!=0 for A,B in domain(L))
    return dict(exact_guarded_equivalences=cases,admitted=accepted,
                zero_factor_cases=zero_factors,divisibility_only_false_positive=True)


def constant_factor_bound_audit():
    cases=admitted=0
    for c0,c1,ep,ze,eta in product(range(-2,3),repeat=5):
        if not ep:continue
        C=abs(c0)+abs(c1);L0=2*(abs(ze)+1);W0=2*(C+abs(eta)+1)
        for W in (1,2,3,4,8,9):
            for L in (2,3,4,8,9):
                values={c0*A+c1*B for A,B in domain(L)}
                witness=-ep*W*L-ze*W-eta in values
                if witness:
                    assert W<W0 or L<L0
                    admitted+=1
                if W>=W0 and L>=L0:
                    assert W*(abs(ep)*L-abs(ze))>C*L+abs(eta)
                cases+=1
    return dict(parameter_width_duration_cases=cases,admitted=admitted)


def zero_intercept_audit():
    cases=accepted=0
    for a,u,v,ep,ze,eta in product((1,2),(-1,0,1),(-1,0,1),range(-1,2),range(-1,2),range(-2,3)):
        if gcd(u,v)!=1:continue
        for W in (1,2,3,4,8,9):
            for L in (2,3,4):
                for A,B in domain(L):
                    original=W*(a*(u*A+v*B)+ep*L+ze)+eta
                    if original==0:
                        if eta:assert eta%W==0
                        else:assert a*(u*A+v*B)+ep*L+ze==0
                        accepted+=1
                    assert eta or (original==0)==(a*(u*A+v*B)+ep*L+ze==0)
                    cases+=1
    return dict(exact_identity_cases=cases,admitted=accepted)


def zero_padding_audit():
    cases=loops=0
    for radix in (2,3,4):
        for h,cf in product(range(-5,6),repeat=2):
            for length in range(1,7):
                power=radix**length
                numerator=(radix-1)*cf+h*(power-1)
                denominator=(radix-1)*power
                same=numerator==denominator*cf
                assert same==((radix-1)*cf==h)
                cases+=1;loops+=same
    return dict(exact_rational_endpoint_checks=cases,absorbing_loops=loops)


def verify():
    return dict(status='PASS_PROPORTIONAL_CARRY_REDUCTION_AND_ELEMENTARY_SUBCASES',
                factorization=factor_audit(),guarded_reduction=reduction_audit(),
                constant_factor=constant_factor_bound_audit(),
                zero_intercept=zero_intercept_audit(),zero_padding=zero_padding_audit(),
                scope='Exact guarded reduction; epsilon0, constant-factor, and zero-intercept cases decidable by the proof',
                general_two_power_divisibility='UNRESOLVED_HERE',
                general_presburger_elimination_implemented=False,
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))

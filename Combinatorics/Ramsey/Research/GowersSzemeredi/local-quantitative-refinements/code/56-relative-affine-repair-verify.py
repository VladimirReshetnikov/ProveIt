#!/usr/bin/env python3
"""Finite exact-arithmetic diagnostics for relative affine repair.

These checks are not a substitute for the universal proofs in article.tex.
Run: python3 code/verify.py --output data/verification.json
Uses only the Python standard library. No floating-point inequalities are used.
"""
from __future__ import annotations
import argparse
import json
import random
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from repair import AbelianGroup, decode, json_ready

COUNTS: dict[str,int] = {}
def check(name: str, condition: bool) -> None:
    if not condition:
        raise AssertionError(name)
    COUNTS[name] = COUNTS.get(name,0)+1

def radical_bound(lhs: F, base: F, radicand: F) -> bool:
    """Exact decision for lhs <= base + sqrt(radicand)."""
    return radicand >= 0 and (lhs <= base or (lhs-base)**2 <= radicand)


def audit_case(moduli: tuple[int,...], target_modulus: int,
               W: list[int], denominator: int, labels: list[int],
               run_decoder: bool = True) -> None:
    G = AbelianGroup(moduli)
    xs = G.elements
    n = len(xs)
    idx = {x:i for i,x in enumerate(xs)}
    add = [[idx[G.add(x,y)] for y in xs] for x in xs]
    sub = [[idx[G.sub(x,y)] for y in xs] for x in xs]
    R=[]; q=[]; mode_mass=[]; good_numerator=0
    for h in range(n):
        hist={}
        for x in range(n):
            y=add[x][h]
            v=(labels[y]-labels[x]) % target_modulus
            hist[v]=hist.get(v,0)+W[x]*W[y]
        r=sum(hist.values()); R.append(r)
        chosen=min(hist,key=lambda v:(-hist[v],v)) if r else 0
        q.append(chosen); mode_mass.append(hist.get(chosen,0))
        good_numerator += sum(m*m for m in hist.values())
    d=denominator
    a=F(sum(W),n*d)
    mu=F(sum(w*w for w in W), n*d*d)
    r=[F(x,n*d*d) for x in R]
    Q=F(sum(x*x for x in R), n**3*d**4)
    K=Q-a**4
    defect=Q-F(good_numerator,n**3*d**4)
    B=F(sum(x-y for x,y in zip(R,mode_mass)),n*n*d*d)
    check('autocorrelation_mean',sum(r,F(0))/n == a*a)
    check('autocorrelation_variance',sum(((x-a*a)**2 for x in r),F(0))/n == K)
    check('uniformity_nonnegative', K>=0)
    check('weighted_interpolation',radical_bound(a*a*B,defect,K*defect))
    triangles=[]; bad_triangle_mass=F(0); rho=F(0)
    for h in range(n):
        for k in range(n):
            T=F(sum(W[x]*W[add[x][h]]*W[add[add[x][h]][k]] for x in range(n)),n*d**3)
            triangles.append(T)
            if q[add[h][k]] != (q[h]+q[k]) % target_modulus:
                bad_triangle_mass += T/(n*n)
                rho += F(1,n*n)
    V=sum(((x-a**3)**2 for x in triangles),F(0))/(n*n)
    check('triangle_mean',sum(triangles,F(0))/(n*n) == a**3)
    check('triangle_second_moment',sum((x*x for x in triangles),F(0))/(n*n) == sum((x**3 for x in r),F(0))/n)
    check('triangle_variance_cap',V <= a*(1+2*a)*K)
    check('weighted_triangle_union',bad_triangle_mass <= 3*a*B)
    check('triangle_transfer',radical_bound(a**3*rho,3*a*B,V*rho))
    # Mark errors relative to the zero affine map; this tests the profile for
    # arbitrary error patterns, not just the repaired candidate.
    errors=[int(l % target_modulus != 0) for l in labels]
    v=[w*e for w,e in zip(W,errors)]
    b=F(sum(v),n*d)
    singles=[0]*4; pairs=[0]*6; bad_count=0; energy_count=0; exactly_one=0
    pair_indices=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    for x in range(n):
        for y in range(n):
            for z in range(n):
                t=sub[add[x][y]][z]
                ids=(x,y,z,t)
                mass=W[x]*W[y]*W[z]*W[t]
                energy_count+=mass
                err=[errors[i] for i in ids]
                if (labels[x]+labels[y]-labels[z]-labels[t]) % target_modulus:
                    bad_count+=mass
                if sum(err)==1: exactly_one+=mass
                for i in range(4): singles[i]+=mass*err[i]
                for j,(s,t0) in enumerate(pair_indices): pairs[j]+=mass*err[s]*err[t0]
    norm=n**3*d**4
    check('quadruple_energy_identity',F(energy_count,norm)==Q)
    check('quadruple_defect_identity',F(bad_count,norm)==defect)
    check('one_error_is_violation',bad_count>=exactly_one)
    check('one_error_inclusion_exclusion',exactly_one >= sum(singles)-2*sum(pairs))
    check('violation_union_upper',bad_count<=sum(singles))
    for x in range(n):
        link=F(sum(W[y]*W[z]*W[sub[add[y][z]][x]] for y in range(n) for z in range(n)),n*n*d**3)
        check('pointwise_link_fourier_bound',(link-a**3)**2 <= K*(mu-a*a))
    for count in pairs:
        check('mixed_two_error_bound',radical_bound(F(count,norm),b*b*a*a,K*b**3))
    if run_decoder:
        out=decode(G,AbelianGroup((target_modulus,)),[F(w,d) for w in W],[(l%target_modulus,) for l in labels])
        check('decoder_defect_consistency',out['epsilon']==defect/Q)
        check('decoder_pair_error_consistency',out['pair_error']==B)
        if out['rho']<F(1,6):
            check('blr_additivity',out['additive'])
            check('blr_distance',out['tau']<=out['rho']/(1-2*out['rho']))
        if out['hypotheses_hold']:
            check('main_theorem_output',out['additive'] and out['distance']<=F(13,50)*out['epsilon'])


def constants() -> dict:
    beta=F(2081,1048576)
    check('constant_beta',beta<F(1,480))
    rho=6*F(1,480)+F(3,1024)
    check('constant_rho',rho==F(79,5120) and rho<F(1,64))
    check('constant_tau',F(1,62)<F(1,60))
    coarse=F(1,480)+F(1,60)+F(1,224)
    check('constant_coarse',coarse==F(13,560) and coarse<F(1,32))
    coefficient=4*(1-F(1,32))-12*F(1,32)-12*F(1,32)*F(1,4)
    check('constant_linear',coefficient==F(109,32) and coefficient>3*(1+F(1,1024)))
    # sqrt(3) <= 7/4 provides a rational lower bound on the final denominator.
    denom=4*(1-F(1,32))-F(4,1024)-4*F(7,4)*F(1,32)*F(1,32)
    check('constant_refined',F(1025,1024)/denom<F(13,50))
    return dict(beta_upper=beta,rho_upper=rho,coarse_distance=coarse,
                profile_coefficient=coefficient,refined_rational_coefficient=F(1025,1024)/denom)


def punctured_example(N: int) -> dict:
    if N<5 or N%2!=1: raise ValueError('N must be odd and >=5')
    a=F(N-1,N)
    Q=F((N-1)**2+(N-1)*(N-2)**2,N**3)
    K=Q-a**4
    D=F(4*(N-3)+4*(N-3)*(N-4),N**3)
    eps=D/Q; t=F(1,N-1)
    check('punctured_uniformity_formula',K==F(N-1,N**4))
    if N>=8193:
        check('punctured_hypotheses',K<=a**5/1024 and eps<=F(1,1024))
        check('punctured_conclusion',t<=F(13,50)*eps)
    return dict(N=N,alpha=a,uniformity_fourth=K,epsilon=eps,distance=t,ratio=t/eps)


def main() -> None:
    ap=argparse.ArgumentParser(); ap.add_argument('--output',default='data/verification.json')
    args=ap.parse_args()
    const=constants()
    exhaustive=0
    for n in range(1,7):
        for state in product(range(3),repeat=n):
            if not any(state): continue
            # 0 = absent; 1 = present with label 0; 2 = present with label 1.
            audit_case((n,),2,[int(s>0) for s in state],1,[int(s==2) for s in state])
            exhaustive+=1
    rng=random.Random(20261006)
    weighted=0
    for moduli in [(7,),(8,),(2,3),(2,2,2),(3,3),(11,)]:
        n=len(AbelianGroup(moduli).elements)
        for _ in range(15):
            W=[rng.randrange(5) for _ in range(n)]
            if not any(W): W[0]=1
            labels=[rng.randrange(3) for _ in range(n)]
            audit_case(moduli,3,W,4,labels)
            weighted+=1
    examples=[]
    for n in [31,37,41]:
        W=[1]+[10000]*(n-1); labels=[1]+[0]*(n-1)
        audit_case((n,),3,W,10000,labels)
        out=decode(AbelianGroup((n,)),AbelianGroup((3,)),[F(x,10000) for x in W],[(x,) for x in labels])
        examples.append({k:out[k] for k in ['alpha','uniformity_fourth','epsilon','distance','hypotheses_hold','additive']})
    for n in [5,7,9,11]:
        W=[0]+[1]*(n-1); labels=[0,1]+[0]*(n-2)
        audit_case((n,),2,W,1,labels)
        out=decode(AbelianGroup((n,)),AbelianGroup((2,)),W,[(x,) for x in labels])
        ex=punctured_example(n)
        check('punctured_formula_crosscheck',out['epsilon']==ex['epsilon'])
    # Rank implication is checked algebraically at the exact endpoint.
    check('rank_constant',16*F(1,2**14)==F(1,1024))
    result=dict(status='PASS',method='exact rational and integer arithmetic; finite diagnostics, not a formal proof',
                seed=20261006,exhaustive_unweighted_cases=exhaustive,random_weighted_cases=weighted,
                weighted_small_error_cases=examples,punctured_subset_example=punctured_example(8193),
                constants=const,checks_by_name=COUNTS,total_assertions=sum(COUNTS.values()))
    path=Path(args.output); path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(json_ready(result),indent=2)+'\n')
    print(json.dumps(json_ready(result),indent=2))

if __name__=='__main__': main()

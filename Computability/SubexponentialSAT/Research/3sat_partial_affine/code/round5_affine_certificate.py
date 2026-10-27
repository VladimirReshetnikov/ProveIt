"""Revised certificate against ProveIt round 5, commit 324f3d9b009a.

Uses the newly prior rectangular backend and coupled-pair theorem on the
new doubled-affine 18-group construction. Standard library only.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import json
from certificate_helpers import (affine_plans, operation_supports, dot,
    require, sqrt_bounds, coefficient_bounds, decimal_enclosure)

DENOMINATOR=1400000
TRIPLES=sorted(set(permutations((1400007,1400007,0))) |
               set(permutations((1400000,1175014,750000))))

def rectangular_supports(plan):
    old=operation_supports(plan)
    answer=[]
    for offset in range(0,len(old),3):
        operation=[row[0] for row in old[offset:offset+3]]
        categories=[None if operation[0][e]==0 else
                    next(c for c in range(3) if operation[c][e]==3)
                    for e in range(len(operation[0]))]
        for triple in TRIPLES:
            answer.append(tuple(0 if c is None else triple[c] for c in categories))
    require(len(answer)==9*(sum(map(len,plan))-2),"Rectangular support count")
    return answer

def coupled_certificate(plans):
    arrays=[rectangular_supports(plan) for plan in plans]
    q=len(arrays);r=sum(map(len,plans[0]))
    norms=[[dot(v,v) for v in arr] for arr in arrays]
    pair_maxima=[];witnesses=[]
    for i,j in combinations(range(q),2):
        best=-1;arg=None
        for iv,v in enumerate(arrays[i]):
            for iw,w in enumerate(arrays[j]):
                candidate=norms[i][iv]+norms[j][iw]+2*(q-1)*dot(v,w)
                if candidate>best:
                    best=candidate;arg=[iv,iw]
        pair_maxima.append(best);witnesses.append(arg)
    beta_squared=F(2*sum(pair_maxima),
                    (q-1)*q*q*DENOMINATOR*DENOMINATOR*r*r)
    # A matching witness establishes sharpness for this fixed portfolio and
    # Euclidean relaxation; no claim of realizability by a SAT input.
    k=len(arrays[0])-9+TRIPLES.index((1400000,1175014,750000))
    g=tuple(sum(arr[k][e] for arr in arrays) for e in range(r*(r-1)//2))
    norm_g=dot(g,g)
    maxima=[max(dot(v,g) for v in arr) for arr in arrays]
    relaxed_squared=F(2*maxima[0]**2,DENOMINATOR**2*r*r*norm_g)
    require(maxima==[maxima[0]]*q,"Uniform extremizing witness")
    require(relaxed_squared==beta_squared,"Exact local minimax value")
    return dict(r=r,plans=plans,supports_per_plan=len(arrays[0]),
        pair_checks=sum(len(arrays[i])*len(arrays[j]) for i,j in combinations(range(q),2)),
        pair_maxima=pair_maxima,maximizing_indices=witnesses,
        beta_squared=str(beta_squared),
        sharpness=dict(witness_support_index=k,norm_squared=norm_g,
                       maximum_dot_per_plan=maxima))

def main():
    root=coupled_certificate(affine_plans(18))
    tail=coupled_certificate(affine_plans(9))
    B=F(563681831683,1764000000000)
    require(root['pair_maxima']==[811701837623520]*6,"Doubled-affine pair maxima")
    require(tail['pair_maxima']==[202925459405880]*6,"Affine tail pair maxima")
    require(F(root['beta_squared'])==B==F(tail['beta_squared']),"Common exact beta")
    # All comparisons below are exact rational/integer comparisons.
    require(648**107<2**1000,"Root packing margin")
    require(162**17<2**125,"Tail packing margin")
    require(F(1,12)<F(107,1000)<F(17,125),"Degree/cap order")
    require(F(3,8)>F(1,4),"Uniform taper positivity at depth log_4(lambda)")
    eta0=F(107,1000);eta1=F(29,1600);q=F(3,8)
    require(eta0+eta1/(1-q)==F(17,125),"Total capacity")
    # Bound the paid tail branch relative to the root K coefficient.
    # alpha18 < .324, gamma9 < .363, K1/K0 < .270,
    # alpha9/(1-gamma9) < .698, hence tail <= .51246 < beta.
    require(F(34,18**2)<F(324,1000)**2,"alpha18 bound")
    require(F(4,81)/q<F(363,1000)**2,"gamma9 bound")
    require(F(1,81)*eta0/eta1<F(270,1000)**2,"K1/K0 bound")
    require(F(4,9)/(1-F(363,1000))<F(698,1000),"Tail infinite-path coefficient")
    require(B<F(698,1000)**2,"Tail local work below same coefficient")
    require((F(324,1000)+F(270,1000)*F(698,1000))**2<B,
            "All recursively paid tail branches below root")
    factor=2*B/eta0
    require(factor==F(563681831683,94374000000),"Time coefficient identity")
    bound=coefficient_bounds([factor])
    require(bound[1]<F(11077,1000),"Safe eventual time coefficient")
    # Joint-selector space certificate is independently checked in
    # check_rectangular_joint.py. This file checks only its coefficient.
    space_factor=2*F(7,27)/eta0
    require(space_factor==F(14000,2889),"Joint space coefficient identity")
    space_bound=coefficient_bounds([space_factor])
    require(space_bound[1]<F(9978,1000),"Safe eventual space coefficient")
    result=dict(
        reviewed_commit='324f3d9b009ab0323f33be65cd6577867c9c4338',
        prior_ingredients=['sat_pairwise_certificates rectangular backend',
                           'sat_pairwise_certificates coupled-pair inequality',
                           'round-5 affine-nine menus'],
        new_ingredient='Doubled affine18 root, certified complete supports, and strict18-to9 low-degree schedule',
        denominator=DENOMINATOR,triples=TRIPLES,root=root,tail=tail,
        schedule=dict(root_groups=18,tail_groups=9,root_eta=str(eta0),
            tail_eta1=str(eta1),tail_ratio=str(q),total_cap='17/125',
            leaf_threshold='ceil(s/ceil(log2(s)))'),
        coefficients=dict(time_squared_factor=str(factor),
            time=decimal_enclosure(bound),
            joint_space_squared_factor=str(space_factor),
            joint_space=decimal_enclosure(space_bound)),
        scope='Exact finite certificates and schedule arithmetic; imported contraction/reduction identities; no logarithmic-order improvement claimed.')
    (Path(__file__).resolve().parents[1] / "results" / 'round5_affine_certificate_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()

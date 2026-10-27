#!/usr/bin/env python3
"""Independent exact joint certificate for the round-5 rectangular backend.

Uses only the Python standard library and the affine geometry reconstruction
in this directory's independent check_doubled_affine.py. It imports no search
or source-packet implementation. All checks remain active under python -O.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from pathlib import Path
import json

from geometry18_independent import (VERTICES, EDGES, NORMALS, affine_plan,
                                 operations, require)


L = 1400000
TRIPLES = tuple(sorted(set(permutations((1400007,1400007,0))))) + tuple(
    sorted(set(permutations((1400000,1175014,750000)))))
PAIRS = ((0,1),(0,2),(1,2))
A_EXPECTED = 811701837623520


def time_menu(plan):
    out=[]
    for kind,parts in operations(plan):
        labels={v:i for i,part in enumerate(parts) for v in part}
        for triple in TRIPLES:
            values=[]
            for x,y in EDGES:
                pair=tuple(sorted((labels[x],labels[y])))
                values.append(0 if pair[0]==pair[1] else triple[PAIRS.index(pair)])
            out.append((kind,triple,tuple(values)))
    return tuple(out)


def boundary_menu(plan):
    subsets=[]
    def visit(block):
        subsets.append(tuple(block))
        if len(block)>1:
            middle=len(block)//2
            visit(block[:middle])
            visit(block[middle:])
    for block in plan:
        visit(block)
    require(len(subsets)==33 and len(set(subsets))==33,"Wrong boundary family")
    return tuple((S,tuple(int((x in S)!=(y in S)) for x,y in EDGES)) for S in subsets)


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def select_joint(cardinality_products):
    """Executable integer selector; its exponents are rounded UP per edge.

    Input D_e is the positive integer |I_gh|*|I_hg| in EDGES order. There
    are no floating logarithms and no comparisons involving an irrational.
    Returning a minimum of these integer scores minimizes the rounded joint
    proxy. Rounding adds a uniformly bounded constant to its exponent.
    """
    require(len(cardinality_products)==len(EDGES),"Wrong cardinality vector length")
    require(all(isinstance(d,int) and d>=1 for d in cardinality_products),
            "Every exact mode-list product must be a positive integer")
    ghat=tuple((d-1).bit_length() for d in cardinality_products)
    records=[]
    for normal in NORMALS:
        plan=affine_plan(normal)
        time_hat=max(dot(t[2],ghat) for t in time_menu(plan))
        boundary_hat=max(dot(b[1],ghat) for b in boundary_menu(plan))
        score=max(336*time_hat*time_hat,A_EXPECTED*boundary_hat*boundary_hat)
        records.append({"time_numerator_upper":time_hat,
                        "boundary_exponent_upper":boundary_hat,"score":score})
    chosen=min(range(4),key=lambda j:records[j]["score"])
    return {"selected_plan":chosen,"normal":NORMALS[chosen],
            "upper_entropies":ghat,"plans":records}


def audit():
    plans=tuple(affine_plan(n) for n in NORMALS)
    times=tuple(time_menu(p) for p in plans)
    bounds=tuple(boundary_menu(p) for p in plans)
    require(len(TRIPLES)==9 and all(len(m)==144 for m in times),"Wrong time supports")
    norm_t=tuple(tuple(dot(v[2],v[2]) for v in m) for m in times)
    norm_b=tuple(tuple(dot(v[1],v[1]) for v in m) for m in bounds)
    require(max(map(max,norm_b))==72,"Wrong boundary self maximum")
    pair_maxima=[]
    tt_count=bb_count=tb_count=0
    bb_max=0
    mixed_dot_max=0
    min_mixed_D=None
    min_mixed_square_gap=None
    for i,j in combinations(range(4),2):
        pair_best=0
        for a,t in enumerate(times[i]):
            for b,u in enumerate(times[j]):
                candidate=norm_t[i][a]+norm_t[j][b]+6*dot(t[2],u[2])
                pair_best=max(pair_best,candidate)
                tt_count+=1
        require(pair_best==A_EXPECTED,"Time coupled-pair maximum changed")
        pair_maxima.append(pair_best)
        for a,b in product(bounds[i],bounds[j]):
            bb_max=max(bb_max,dot(a[1],b[1]))
            bb_count+=1
        for ti,bi in ((i,j),(j,i)):
            for k,t in enumerate(times[ti]):
                for m,b in enumerate(bounds[bi]):
                    overlap=dot(t[2],b[1])
                    mixed_dot_max=max(mixed_dot_max,overlap)
                    # rho^2=A_EXPECTED/(336 L^2). Squaring is safe only after
                    # checking D>=0. These are integer inequalities throughout.
                    D=A_EXPECTED*(336-norm_b[bi][m])-336*norm_t[ti][k]
                    gap=D*D-36*336*A_EXPECTED*overlap*overlap
                    require(D>=0 and gap>=0,"Mixed time-boundary pair exceeds A")
                    min_mixed_D=D if min_mixed_D is None else min(min_mixed_D,D)
                    min_mixed_square_gap=gap if min_mixed_square_gap is None else min(min_mixed_square_gap,gap)
                    tb_count+=1
    require(bb_max==32,"Wrong boundary cross maximum")
    require(2*72+6*bb_max==336,"Scaled boundary coupled bound changed")
    require(mixed_dot_max==53200224,"Wrong mixed time-boundary maximum")

    # The maximum TT pair is attained by two final operations carrying the
    # second support triple. Affine transversality gives a direct formula.
    Y=(1400000,1175014,750000)
    self_final=36*sum(x*x for x in Y)
    cross_final=8*sum(Y)**2
    require(2*self_final+6*cross_final==A_EXPECTED,"Closed-form pair certificate fails")
    final=tuple(next(t[2] for t in menu if t[0]=="F" and t[1]==Y) for menu in times)
    g=tuple(sum(xs) for xs in zip(*final))
    require(dot(g,g)==2*A_EXPECTED,"Four-mask attainment fails")
    maxdots=tuple(max(dot(t[2],g) for t in menu) for menu in times)
    require(maxdots==(A_EXPECTED//2,)*4,"Time relaxation tightness fails")

    beta2=Fraction(A_EXPECTED,4*L**2*18**2)
    rho2=Fraction(A_EXPECTED,336*L**2)
    storage2=beta2/rho2
    require(beta2==Fraction(563681831683,1764000000000),"Wrong time coefficient")
    require(storage2==Fraction(7,27),"Wrong joint storage coefficient")

    selector_examples=[]
    for Ds in ([1]*len(EDGES),
               [2**(i%5) for i in range(len(EDGES))],
               [2**(i%5)+1 for i in range(len(EDGES))]):
        selected=select_joint(Ds)
        require(selected["plans"][selected["selected_plan"]]["score"]
                ==min(rec["score"] for rec in selected["plans"]),
                "Integer joint selector failed")
        for d,h in zip(Ds,selected["upper_entropies"]):
            require(d<=2**h and (h==0 or 2**(h-1)<d),"Entropy ceiling failed")
        selector_examples.append({"selected_plan":selected["selected_plan"],
                                  "score":selected["plans"][selected["selected_plan"]]["score"]})

    return {
        "status":"PASS",
        "time_masks_per_plan":144,"boundary_masks_per_plan":33,
        "integer_denominator":L,"time_triples":TRIPLES,
        "time_pair_maxima":pair_maxima,
        "time_pairs_checked":tt_count,"boundary_pairs_checked":bb_count,
        "mixed_pairs_checked":tb_count,
        "boundary_self_max":72,"boundary_cross_max":bb_max,
        "mixed_dot_integer_max":mixed_dot_max,
        "minimum_nonnegative_mixed_D":min_mixed_D,
        "minimum_nonnegative_squared_mixed_gap":min_mixed_square_gap,
        "time_beta_squared":str(beta2),"joint_rho_squared":str(rho2),
        "storage_beta_squared":str(storage2),
        "exact_integer_selector_score":"max(336*T_hat_j^2, 811701837623520*B_hat_j^2)",
        "selector_upper_entropies":"g_hat_e=(D_e-1).bit_length(), D_e=|I_gh|*|I_hg|",
        "selector_examples":selector_examples,
        "root_eta":"107/1000",
        "root_time_radicand_after_pi_over_ln2":str(2*beta2/Fraction(107,1000)),
        "root_space_radicand_after_pi_over_ln2":str(2*storage2/Fraction(107,1000)),
        "scope":"Local joint support certificate and root coefficients; tail schedule separately audited.",
    }


if __name__=="__main__":
    result=audit()
    text=json.dumps(result,indent=2,sort_keys=True)+"\n"
    (Path(__file__).resolve().parents[1] / "results" / "rectangular_joint_result.json").write_text(text)
    print(text,end="")

#!/usr/bin/env python3
"""Exact checks in Z[omega], omega^2+omega+1=0; no third-party packages."""
from itertools import product, permutations
from fractions import Fraction
import json
from pathlib import Path
from math import gcd

Z=(0,0)
O=(1,0)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def sub(x,y): return add(x,neg(y))
def mul(x,y):
    a,b=x; c,d=y
    return (a*c-b*d,a*d+b*c-b*d)
def conj(x): return (x[0]-x[1],-x[1])
def norm(x):
    ans=mul(x,conj(x)); assert ans[1]==0
    return ans[0]
def wp(n): return (O,(0,1),(-1,-1))[n%3]
def matmul(a,b):
    return tuple(tuple(sum_ring(mul(a[i][k],b[k][j]) for k in range(3)) for j in range(3)) for i in range(3))
def matscale(a,c): return tuple(tuple(mul(c,x) for x in row) for row in a)
def sum_ring(xs):
    ans=Z
    for x in xs: ans=add(ans,x)
    return ans
def trace(a): return sum_ring(a[i][i] for i in range(3))
def det(a):
    ans=Z
    for p in permutations(range(3)):
        inv=sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        term=O
        for i in range(3): term=mul(term,a[i][p[i]])
        ans=add(ans,neg(term) if inv%2 else term)
    return ans
def charpoly(a):
    # Coefficients from T^0 through T^3, using the principal 2x2 minors.
    c2=Z
    for i in range(3):
        for j in range(i+1,3):
            c2=add(c2,sub(mul(a[i][i],a[j][j]),mul(a[i][j],a[j][i])))
    return (neg(det(a)),c2,neg(trace(a)),O)
def groupmul(g,h):
    a,b,c=g; x,y,z=h
    return ((a+x)%3,(b+y)%3,(c+z+a*y)%3)
def rep(t,g):
    a,b,c=g
    return tuple(tuple(wp(t*(c+a*j)) if i==(j+b)%3 else Z for j in range(3)) for i in range(3))

def main():
    group=list(product(range(3),repeat=3))
    matrices={t:{g:rep(t,g) for g in group} for t in (1,2)}
    checks=0
    for t in (1,2):
        for g in group:
            assert det(matrices[t][g])==O
            for h in group:
                assert matmul(matrices[t][g],matrices[t][h])==matrices[t][groupmul(g,h)]
                checks+=1
    chars={t:{g:trace(matrices[t][g]) for g in group} for t in (1,2)}
    assert all(sum(norm(chars[t][g]) for g in group)==27 for t in (1,2))
    assert sum_ring(mul(chars[1][g],conj(chars[2][g])) for g in group)==Z
    discrepancy=[g for g in group if charpoly(matrices[1][g])!=charpoly(matrices[2][g])]
    assert discrepancy==[(0,0,1),(0,0,2)]
    assert all(norm(sub(chars[1][g],chars[2][g]))==27 for g in discrepancy)
    assert sum(norm(sub(chars[1][g],chars[2][g])) for g in group)==54
    for g in group:
        if g[:2]!=(0,0):
            assert all(charpoly(matrices[t][g])==((-1,0),Z,Z,O) for t in (1,2))
    witness={"status":"PASS","arithmetic":"exact Z[omega]","group_order":27,
        "representation_law_pairs_checked":checks,"determinants":"both identically 1",
        "character_norms":[1,1],"character_inner_product":0,
        "full_factor_disagreement_count":len(discrepancy),"full_factor_disagreement_density":str(Fraction(len(discrepancy),27)),
        "full_factor_agreement_density":str(Fraction(27-len(discrepancy),27)),
        "disagreeing_elements":discrepancy,"character_distance_squared_average":2,
        "noncentral_polynomial":"T^3-1","extremal_trace_difference_squared":27}

    # The odd-dimensional Serre trace example has a different full-factor distance.
    serre_group=[(g,e) for g in group for e in (1,-1)]
    serre_trace_bad=[]
    serre_factor_bad=[]
    for g,e in serre_group:
        a=matrices[1][g]
        b=matscale(a,(e,0))
        if trace(a)!=trace(b): serre_trace_bad.append((g,e))
        if charpoly(a)!=charpoly(b): serre_factor_bad.append((g,e))
    assert len(serre_trace_bad)==3
    assert len(serre_factor_bad)==27
    serre={"group":"H27 x C2","group_order":54,
        "pair":"tau tensor 1, tau tensor sgn",
        "trace_disagreement_count":len(serre_trace_bad),
        "trace_disagreement_density":str(Fraction(len(serre_trace_bad),54)),
        "full_factor_disagreement_count":len(serre_factor_bad),
        "full_factor_disagreement_density":str(Fraction(len(serre_factor_bad),54)),
        "explanation":"At every element with sign -1 the determinants differ; traces differ only above the three central H27 elements."}

    # Half-distance decoding is exactly sharp, including deterministic finite weights.
    p1={g:charpoly(matrices[1][g]) for g in group}
    p2={g:charpoly(matrices[2][g]) for g in group}
    received=dict(p1)
    received[(0,0,2)]=p2[(0,0,2)]
    errors1=sum(received[g]!=p1[g] for g in group)
    errors2=sum(received[g]!=p2[g] for g in group)
    assert errors1==errors2==1
    unerased=[g for g in group if g not in discrepancy]
    assert all(p1[g]==p2[g] for g in unerased)
    decoding={"hybrid_error_density_from_first":str(Fraction(errors1,27)),
        "hybrid_error_density_from_second":str(Fraction(errors2,27)),
        "hybrid_description":"Use rho_1 at central c=1 and rho_2 at central c=2; elsewhere the outputs coincide.",
        "erasure_density_for_complete_ambiguity":str(Fraction(len(discrepancy),27)),
        "strict_uniqueness_threshold":"2e+s < 2/27",
        "error_only_boundary":"e=1/27 is ambiguous",
        "erasure_only_boundary":"s=2/27 is ambiguous"}

    # The sharp reducible cubic floor is 1/8, realized over the rational integers.
    rid=((O,Z,Z),(Z,O,Z),(Z,Z,O))
    rmat=((Z,(-1,0),Z),(O,Z,Z),(Z,Z,O))
    smat=((O,Z,Z),(Z,(-1,0),Z),(Z,Z,O))
    rpow=[rid]
    for _ in range(3): rpow.append(matmul(rpow[-1],rmat))
    reducible_group=list(product(range(4),range(2),(1,-1)))
    reducible_bad=[]
    reducible_norms=[0,0]
    reducible_inner=Z
    for a,b,e in reducible_group:
        m=matmul(rpow[a],smat) if b else rpow[a]
        twist=((e,0),Z,Z),(Z,(e,0),Z),(Z,Z,O)
        n=matmul(m,twist)
        assert det(m)==det(n)
        if charpoly(m)!=charpoly(n): reducible_bad.append((a,b,e))
        reducible_norms[0]+=norm(trace(m))
        reducible_norms[1]+=norm(trace(n))
        reducible_inner=add(reducible_inner,mul(trace(m),conj(trace(n))))
    assert reducible_bad==[(0,0,-1),(2,0,-1)]
    assert reducible_norms==[32,32]
    assert reducible_inner==(16,0)
    reducible={"group":"D8 x C2","group_order":16,
        "pair":"(tau tensor 1) plus 1, (tau tensor sgn) plus 1",
        "character_norms":[2,2],"character_inner_product":1,
        "full_factor_disagreement_count":len(reducible_bad),
        "full_factor_disagreement_density":str(Fraction(len(reducible_bad),16)),
        "disagreeing_elements":reducible_bad,"determinants":"identical"}
    # Three abelian Euler factors: a counterexample to the printed Rajan
    # Conjecture 3, whose size-three claimed disagreement floor is 1/4.
    logs7={pow(3,j,7):j%3 for j in range(6)}
    logs13={pow(2,j,13):j%3 for j in range(12)}
    abelian_bad=[]
    fibres={f"{a},{b}":0 for a in range(3) for b in range(3)}
    for u in range(91):
        if gcd(u,91)!=1: continue
        a,b=logs7[u%7],logs13[u%13]
        fibres[f"{a},{b}"]+=1
        first=((O,Z,Z),(Z,wp(a),Z),(Z,Z,wp(2*a)))
        second=matscale(first,wp(b))
        mismatch=charpoly(first)!=charpoly(second)
        assert mismatch==(a==0 and b!=0)
        if mismatch: abelian_bad.append(u)
    assert set(fibres.values())=={8}
    assert len(abelian_bad)==16
    abelian={"modulus":91,"primitive_generators":{"7":3,"13":2},
        "character_packets":[["1","chi","chi^2"],["psi","psi chi","psi chi^2"]],
        "total_reduced_classes":72,"joint_character_fibre_sizes":fibres,
        "full_factor_disagreement_count":16,
        "full_factor_disagreement_density":"2/9","full_factor_agreement_density":"7/9",
        "disagreeing_reduced_classes":abelian_bad,
        "comparison_to_printed_conjecture_at_n3":"7/9 > 3/4 (difference 1/36)",
        "source_scope":"The accompanying manuscript separately verifies the printed conjecture; this program verifies the finite mathematics only."}
    report={"status":"PASS","heisenberg_witness":witness,"serre_trace_comparison":serre,"decoding_boundary":decoding,"reducible_sharpness":reducible,"abelian_cubic_packet":abelian}
    output=json.dumps(report,indent=2)
    out = Path(__file__).resolve().parents[1] / "results" / "exact_checks.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(output+"\n")
    print(output)

if __name__=="__main__": main()

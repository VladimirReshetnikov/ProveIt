#!/usr/bin/env python3
"""Deterministic exact checks; not a substitute for the article's proofs."""
from __future__ import annotations
import copy
import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path
from rotations import *


def reduced_words(rank: int, max_length: int):
    yield ()
    layer = [()]
    alphabet = tuple(range(1, rank+1)) + tuple(range(-1, -rank-1, -1))
    for _ in range(max_length):
        layer = [w+(x,) for w in layer for x in alphabet if not w or w[-1] != -x]
        yield from layer


def mod5_matrix(v):
    a,b,c,d = (int(x) % 5 for x in v)
    return (( (a+2*b)%5, (c+2*d)%5), ((4*c+2*d)%5, (a+3*b)%5))


def mm5(X,Y):
    return tuple(tuple(sum(X[i][k]*Y[k][j] for k in range(2))%5 for j in range(2)) for i in range(2))


def det4(M):
    out = F(0)
    for p in itertools.permutations(range(4)):
        inversions = sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        a=F((-1)**inversions)
        for i,j in enumerate(p): a*=M[i][j]
        out+=a
    return out


def main():
    rng = random.Random(20260930)
    counts = {}
    # Mod-5 algebra homomorphism on basis products and adjacent-letter criterion.
    for p in BASIS:
        for q in BASIS:
            assert mod5_matrix(multiply(p,q)) == mm5(mod5_matrix(p),mod5_matrix(q))
    counts['mod5_basis_products'] = 16
    numerators = {x: quat(*(5*a for a in q)) for x,q in BINARY.items()}
    for x,p in numerators.items():
        for y,q in numerators.items():
            zero = mm5(mod5_matrix(p),mod5_matrix(q)) == ((0,0),(0,0))
            assert zero == (x == -y)
    counts['mod5_adjacent_pairs'] = 16
    seen = set()
    for w in reduced_words(2,7):
        q=evaluate_binary(w)
        assert norm_squared(q)==1 and denominator(q)==5**len(w)
        assert decode_binary(q)==w
        assert q not in seen
        seen.add(q)
    counts['exhaustive_binary_words_max_length_7'] = len(seen)
    for rank in (1,2,3,5):
        for _ in range(50):
            w=reduce_word(rng.choice((-1,1))*rng.randint(1,rank) for _ in range(12))
            assert decode_rank(evaluate_rank(w,rank),rank)==w
    counts['rank_decoder_roundtrips'] = 200
    rejects=(quat(-1,0,0,0),quat(0,1,0,0),quat(F(4,5),F(3,5),0,0),quat(F(5,13),F(12,13),0,0),quat(2,0,0,0))
    assert all(decode_binary(q) is None for q in rejects)
    assert decode_rank(A,3) is None
    assert decode_rank(evaluate_binary((1,1,1,2,-1,-1,-1)),3) is None
    counts['quaternion_rejection_cases'] = len(rejects)+2
    assert all(frobenius(TENSOR_BASIS[i][j],TENSOR_BASIS[k][l]) == 4*int(i==k and j==l)
               for i in range(4) for j in range(4) for k in range(4) for l in range(4))
    counts['tensor_gram_entries'] = 256
    P=Presentation(2,((1,),(2,2)))  # <z,x | z, x^2> = C2
    wp=lambda w: sum((1 if x>0 else -1) for x in w if abs(x)==2)%2==0
    for _ in range(100):
        s=reduce_word(rng.choice((1,-1,2,-2)) for _ in range(6))
        t=reduce_word(rng.choice((1,-1,2,-2)) for _ in range(6))
        p,q=evaluate_rank(s,2),evaluate_rank(t,2)
        M=spin(p,q)
        assert matmul(transpose(M),M)==IDENTITY and det4(M)==1
        assert (p,q) in rational_spin_lifts(M)
        assert P.matrix_membership(M,wp)==wp(s+inverse_word(t))
    counts['rational_spin_and_membership_roundtrips'] = 100
    no_rational_lift=((F(0),F(-1),F(0),F(0)),(F(1),F(0),F(0),F(0)),
                      (F(0),F(0),F(1),F(0)),(F(0),F(0),F(0),F(1)))
    assert matmul(transpose(no_rational_lift),no_rational_lift)==IDENTITY
    assert det4(no_rational_lift)==1 and rational_spin_lifts(no_rational_lift)==()
    assert not P.matrix_membership(no_rational_lift,wp)
    minusI=tuple(tuple(-a for a in row) for row in IDENTITY)
    assert not P.matrix_membership(minusI,wp)
    zeroM=tuple(tuple(F(0) for _ in range(4)) for _ in range(4))
    assert not P.matrix_membership(zeroM,wp)
    counts['matrix_rejection_cases'] = 3
    for Q0 in (Presentation(1,((1,1),)),Presentation(2,((1,2,-1,-2),))):
        MM=MillerMachine(Q0)
        PG=MM.presentation()
        assert all(MM.word_problem(r) for r in PG.relators)
        assert not MM.word_problem((2,))
        for _ in range(30):
            w=tuple(rng.choice((-1,1))*rng.randint(1,MM.rank) for _ in range(10))
            assert MM.word_problem(w+inverse_word(w))
    counts['miller_relators_checked'] = sum(len(MillerMachine(Q0).presentation().relators)
                              for Q0 in (Presentation(1,((1,1),)),Presentation(2,((1,2,-1,-2),))))
    counts['miller_inverse_word_tests'] = 60
    gates=P.gates()
    c=evaluate_rank((2,),2)
    assert c==quat(F(3,5),0,F(-28,125),F(96,125))
    bprime=multiply(multiply(c,B),conjugate(c))
    assert bprime[1] != 0  # its axis is not the j-axis
    assert matmul(matmul(spin(c,c),spin(B,ONE)),transpose(spin(c,c)))==spin(bprime,ONE)
    counts['density_subsystem_identities'] = 3
    certificates=0
    mutations=0
    for T in range(9):
        labels=tuple(rng.randrange(len(gates)) for _ in range(T))
        wit=certificate_witness(gates,c,labels)
        target=wit['target']
        assert certificate_value(gates,c,target,wit)==0
        state=c
        for j in labels: state=quat(*matvec(gates[j],state))
        assert state==target
        for t in range(T+1):
            assert sum(x*x for x in wit['z'][t])==wit['h'][t]**2
        certificates+=1
        bad=copy.deepcopy(wit); bad['z'][T]=tuple(x+int(i==0) for i,x in enumerate(bad['z'][T]))
        assert certificate_value(gates,c,target,bad)>0
        mutations+=1
        if T:
            bad=copy.deepcopy(wit); row=list(bad['selectors'][0]); row[0]+=2;bad['selectors'][0]=tuple(row)
            assert certificate_value(gates,c,target,bad)>0
            mutations+=1
    counts['exact_trace_certificates'] = certificates
    counts['corrupted_trace_rejections'] = mutations
    # Explicit two-gate transfer in the Miller machine for Q=<x|x^2>.
    MM=MillerMachine(Presentation(1,((1,1),)))
    PG=MM.presentation(); MG=PG.gates()
    # Forward list: C_1,...,C_rank,L_r1,... ; inverse half mirrors it.
    t_r=5
    forward_count=PG.rank+len(PG.relators)
    last_relator=len(PG.relators)-1
    labels=(t_r-1,forward_count+PG.rank+last_relator)
    wit=certificate_witness(MG,evaluate_rank((2,),PG.rank),labels)
    expected=evaluate_rank((2,3,3),PG.rank)
    assert wit['target']==expected and certificate_value(MG,c,expected,wit)==0
    assert all(PG.matrix_membership(g,MM.word_problem) for g in MG)
    counts['miller_compiled_gates_membership'] = len(MG)
    counts['miller_two_gate_marker_transfer'] = 1
    recurrence_checks=0
    for r,s in ((A,B),(evaluate_binary((1,2)),B),
                (evaluate_binary((1,2,-1,2)),evaluate_binary((2,1)))):
        seq=commutator_target_sequence(c,r,s,25)
        coefs=order_five_recurrence(r)
        for n in range(20):
            for coordinate in range(4):
                assert sum(coefs[j]*seq[n+j][coordinate] for j in range(6))==0
                recurrence_checks+=1
    counts['order_five_coordinate_recurrence_checks']=recurrence_checks
    result={"status":"PASS","seed":20260930,"arithmetic":"exact integers and fractions.Fraction",
            "tests":counts,"scope":"Finite algebraic tests; not a proof of the infinite or undecidability theorems.",
            "miller_example":{"base_presentation":"<x | x^2>","group_rank":PG.rank,
                "group_relators":[list(r) for r in PG.relators],"gate_count":len(MG),
                "source":[str(x) for x in c],"target":[str(x) for x in expected],
                "chronological_zero_based_labels":list(labels),"common_denominator":str(wit['D']),
                "quartic_variables":len(MG)*2+5*3,
                "quartic_residual_count":len(certificate_residuals(MG,c,expected,wit))}}
    out=Path(__file__).resolve().parents[1]/'verification_results.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()

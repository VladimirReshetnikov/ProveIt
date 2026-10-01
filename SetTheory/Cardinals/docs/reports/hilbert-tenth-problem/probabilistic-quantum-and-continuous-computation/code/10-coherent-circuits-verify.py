#!/usr/bin/env python3
"""Reproducible exact checks. Run from any directory; writes data/verification.json."""
from __future__ import annotations
from itertools import product
from pathlib import Path
from fractions import Fraction
from math import isqrt
import json
import random
import time
from coherent import (Certificate, Gate, ONE, ZERO, Poly, branch_sum, branch_dense,
                      cadd, cmul, cconj, contract, dense_state, probability_network,
                      probability_numerator, real_coeff, sign_sqrt2, graph_branch_network)

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/"data"
DATA.mkdir(exist_ok=True)
counts={"circuit_states":0,"network_equalities":0,"normalizations":0,
        "branch_amplitudes":0,"branch_distribution_normalizations":0,
        "quadratic_certificates":0,"mutations_rejected":0,
        "sqrt2_sign_certificates":0,"nonnegative_gadget_cases":0,
        "cyclotomic_norm_identities":0,"height_bounds":0,
        "graph_network_equalities":0,"ternary_copy_stress_cases":0}
examples=[]
started=time.time()


def check_circuit(n,gates,initial,observations):
    state,h=dense_state(n,gates,initial)
    counts["circuit_states"]+=1
    assert probability_numerator(state,{})==(1 << h,0,0,0)
    counts["normalizations"]+=1
    for observed in observations:
        network,hh=probability_network(n,gates,initial,observed)
        assert hh==h
        actual,stats=contract(network)
        expected=probability_numerator(state,observed)
        assert actual==expected,(n,gates,initial,observed,actual,expected)
        counts["network_equalities"]+=1


def all_words(alphabet,depth):
    for k in range(depth+1):
        yield from product(alphabet,repeat=k)


# Exhaustive one-qubit H,T,X words of length at most four.
alphabet=[Gate("H",(0,)),Gate("T",(0,)),Gate("X",(0,))]
for word in all_words(alphabet,4):
    for initial in range(2):
        check_circuit(1,list(word),initial,[{}, {0:0},{0:1}])
print("one-qubit exhaustive checks complete",flush=True)

# Exhaustive two-qubit words up to length three, all basis inputs.
alphabet=[Gate("H",(0,)),Gate("H",(1,)),Gate("T",(0,)),
          Gate("CX",(0,1)),Gate("CX",(1,0))]
for word in all_words(alphabet,3):
    for initial in range(4):
        check_circuit(2,list(word),initial,[{}, {0:0},{0:1}, {0:0,1:0},{0:1,1:1}])
print("two-qubit exhaustive checks complete",flush=True)

rng=random.Random(20260930)
alphabet=[Gate("H",(q,)) for q in range(3)]+[Gate("T",(q,)) for q in range(3)]
alphabet += [Gate("CCX",(0,1,2)),Gate("CX",(2,0)),Gate("CZ",(0,2))]
for _ in range(60):
    gates=[rng.choice(alphabet) for _ in range(rng.randrange(1,9))]
    check_circuit(3,gates,rng.randrange(8),[{0:rng.randrange(2)},{0:0,1:1,2:0}])

# All graphs on <=3 vertices, all outcome strings and four angle patterns.
for n in range(1,4):
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    for mask in range(1 << len(pairs)):
        edges=[p for k,p in enumerate(pairs) if mask >> k & 1]
        for angle_case in range(4):
            norm=ZERO
            for outcome in product((0,1),repeat=n):
                # Adaptive but causal: angle at q depends only on outcome[:q].
                angles=tuple((angle_case*q+sum(outcome[:q]))%8 for q in range(n))
                a=branch_sum(n,edges,outcome,angles)
                b=branch_dense(n,edges,outcome,angles)
                assert a==b
                graph_network=graph_branch_network(n,edges,outcome,angles)
                contracted,_=contract(graph_network)
                assert contracted==a
                doubled=graph_branch_network(n,edges,outcome,angles,probability=True)
                contracted_norm,_=contract(doubled)
                assert contracted_norm==cmul(a,cconj(a))
                assert len(doubled)<=4*n+6*len(edges)
                assert sum(len(t.edges) for t in doubled)//2<=2*n+8*len(edges)
                assert max(len(t.edges) for t in doubled)<=3
                counts["graph_network_equalities"]+=2
                norm=cadd(norm,cmul(a,cconj(a)))
                counts["branch_amplitudes"]+=1
            assert norm==(1 << (2*n),0,0,0),(n,edges,angle_case,norm)
            counts["branch_distribution_normalizations"]+=1
print("measurement-based checks complete",flush=True)

# High-degree vertices exercise the ternary equality-tree decomposition.
for n,edges in [(6,[(0,j) for j in range(1,6)]),
                (5,[(i,j) for i in range(5) for j in range(i+1,5)])]:
    outcome=tuple(i%2 for i in range(n));angles=tuple((3*i+1)%8 for i in range(n))
    network=graph_branch_network(n,edges,outcome,angles)
    value,stats=contract(network)
    assert value==branch_sum(n,edges,outcome,angles)
    assert max(len(t.edges) for t in network)<=3
    assert len(network)<=2*n+3*len(edges)
    assert sum(len(t.edges) for t in network)//2<=n+4*len(edges)
    counts["ternary_copy_stress_cases"]+=1

# Compare the ring multiplication implementation with an independent norm formula.
for c in product(range(-2,3), repeat=4):
    a0,a1,a2,a3=c
    norm_a=sum(x*x for x in c)
    norm_b=a0*a1-a0*a3+a1*a2+a2*a3
    assert cmul(c,cconj(c))==(norm_a,norm_b,0,-norm_b)
    assert cconj(cconj(c))==c
    counts["cyclotomic_norm_identities"]+=1

# Independently certified rational enclosure of sqrt(2), not floating point.
D=10**30
L=isqrt(2*D*D)
lo,hi=Fraction(L,D),Fraction(L+1,D)
assert lo*lo<2<hi*hi
for p in range(-24,25):
    for q in range(-24,25):
        lower=p+q*(lo if q>=0 else hi)
        upper=p+q*(hi if q>=0 else lo)
        reference=0 if p==q==0 else (1 if lower>0 else -1 if upper<0 else None)
        assert reference is not None
        assert sign_sqrt2(p,q)==reference
        cert=Certificate()
        bit=cert.sqrt2_nonnegative(cert.const(p),cert.const(q))
        assert cert.valid()
        assert cert.witness[bit]==int(reference>=0)
        counts["sqrt2_sign_certificates"]+=1

# Exhaustively verify the two-auxiliary nonnegative gadget in a covering box.
for value in range(-6,7):
    minus=max(-value,0)
    solutions=[]
    for b in range(3):
        for s in range(10):
            if b*(b-1)==0 and b*minus==0 and minus==(1-b)*(s+1) and b*s==0:
                solutions.append((b,s))
    assert solutions==[(int(value>=0),max(-value-1,0))]
    counts["nonnegative_gadget_cases"]+=1

# Canonical certificates, including true and false strict comparisons.
samples=[("HH_zero",1,[Gate("H",(0,)),Gate("H",(0,))],{0:1}),
         ("HTH_zero",1,[Gate("H",(0,)),Gate("T",(0,)),Gate("H",(0,))],{0:0}),
         ("HTH_one",1,[Gate("H",(0,)),Gate("T",(0,)),Gate("H",(0,))],{0:1}),
         ("Bell",2,[Gate("H",(0,)),Gate("CX",(0,1))],{0:0}),
         ("Toffoli",3,[Gate("H",(0,)),Gate("H",(1,)),Gate("CCX",(0,1,2))],{2:1})]
for name,n,gates,obs in samples:
    for order in ("greedy","queue"):
        cert=Certificate(); network,h=probability_network(n,gates,0,obs)
        result,stats=contract(network,cert,order=order)
        coeff=tuple(w.value for w in result)
        state,hh=dense_state(n,gates)
        assert coeff==probability_numerator(state,obs) and h==hh
        assert cert.valid()
        edge_count=sum(len(t.edges) for t in network)//2
        H=1 << edge_count
        assert max(cert.witness)<=H
        counts["height_bounds"]+=1
        a,b=real_coeff(coeff)
        assert cert.arithmetic_gates==32*stats["term_products"]-4*stats["output_entries"]
        assert len(cert.witness)<=8*stats["leaf_entries"]+64*stats["term_products"]
        # Every assignment differs at exactly one selected coordinate.
        selected=rng.sample(range(len(cert.witness)),min(24,len(cert.witness)))
        for i in selected:
            mutation=list(cert.witness); mutation[i]+=1
            assert not cert.valid(mutation)
            counts["mutations_rejected"]+=1
        counts["quadratic_certificates"]+=1
        examples.append({"name":name,"order":order,"probability_a":a,"probability_b":b,
                         "denominator":1 << h,"variables":len(cert.witness),
                         "equations":len(cert.constraints),
                         "max_witness_bits":max(x.bit_length() for x in cert.witness),**stats})
        if order=="greedy" and name in {"HH_zero","HTH_zero"}:
            exported=Certificate()
            exported.names=list(cert.names);exported.witness=list(cert.witness)
            exported.constraints=list(cert.constraints)
            for wire,value in zip(result,coeff): exported.equation(wire.expr-value)
            assert exported.valid()
            exported.export(str(DATA/(name+"_certificate.json")),metadata={
                "query":"exact output coefficients", "qubits":n,"initial":0,
                "gates":[{"name":g.name,"qubits":list(g.qubits)} for g in gates],
                "measured":obs,"hadamards":h,"physical_denominator":1 << h,
                "output_coordinates":[{"positive":w.pos,"negative":w.neg} for w in result],
                "expected_numerator_coefficients":list(coeff),
                "contraction_order":order,"profile":stats,
                "note":"Four linear output equations are additional to the reported base counts."})
        for u,v in [(0,1),(1,2),(1,1)]:
            queried=Certificate(); res,_=contract(network,queried,order=order)
            queried.require_probability_gt(res,h,u,v)
            assert queried.valid()==(sign_sqrt2(v*a-u*(1 << h),v*b)>0)
            bound=v*H+u*(1 << h)
            assert max(queried.witness)<=2*bound*bound
            assert len(queried.witness)-len(cert.witness)<=39
            assert len(queried.constraints)-len(cert.constraints)<=50
            counts["height_bounds"]+=1
            counts["quadratic_certificates"]+=1
print("canonical certificate checks complete",flush=True)

# Graph-native quadratic certificates for amplitude and doubled probability.
for is_probability in (False,True):
    network=graph_branch_network(3,[(0,1),(1,2)],(1,0,1),(0,1,2),
                                 probability=is_probability)
    cert=Certificate(); result,stats=contract(network,cert)
    expected=branch_sum(3,[(0,1),(1,2)],(1,0,1),(0,1,2))
    if is_probability: expected=cmul(expected,cconj(expected))
    assert tuple(w.value for w in result)==expected and cert.valid()
    edge_count=sum(len(t.edges) for t in network)//2
    assert max(cert.witness)<=1 << edge_count
    counts["quadratic_certificates"]+=1
    counts["height_bounds"]+=1

# A complete small expanded quartic, showing cancellation arithmetically.
# H H |0>: unnormalized amplitudes 1+1=2 and 1-1=0.
small=Certificate()
one=small.const(1)
x=small.add(one,one)
y=small.sub(one,one)
z=small.mul(y,y)
small.equation(z.expr)
quartic=small.sum_of_squares()
assert quartic.degree==4 and quartic.evaluate(small.witness)==0
small.export(str(DATA/"HH_expanded_quartic.json"),expanded=True)
counts["quadratic_certificates"]+=1

# Demonstrate why the canonical-pair equations are essential.
p=Poly.var(0)-Poly.var(1)-2
assert all(p.evaluate([2+k,k])==0 for k in range(20))
assert sum((2+k)*k==0 for k in range(20))==1

report={"status":"PASS","seed":20260930,"arithmetic":"exact integer and rational",
        "counts":counts,"examples":examples,
        "small_quartic":{"variables":len(small.witness),"equations":len(small.constraints),
                         "monomials":len(quartic.terms),"degree":quartic.degree},
        "elapsed_seconds":round(time.time()-started,3),
        "scope":"Finite tests support implementation correctness; the article supplies general proofs. No Lean build was performed."}
(DATA/"verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
print(json.dumps(report,indent=2))

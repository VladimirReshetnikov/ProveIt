#!/usr/bin/env python3
"""Reproduce the exact finite checks reported in the article.

No numerical tolerance, external package, or external network access is used.
These tests complement the proofs; they are not a substitute for them.
"""
from __future__ import annotations
from itertools import combinations, product
from pathlib import Path
from collections import Counter
import argparse
import json
import time
from trace_polytope import (Net, compile_certificate, forbidden_history,
                            graph_realization, circuit_net, enabled_runs,
                            interval_independence, guarded_run)


def test_demands():
    comparisons = 0
    commuting = 0
    # All scalar transitions with pre/post weights 0..3. A two-step demand
    # is <= 6, so these 8 initial values include every threshold boundary.
    transitions = list(product(range(4), repeat=2))
    for c,v in transitions:
        for d,w in transitions:
            net = Net(((c,),(d,)),((v,),(w,)))
            match = net.demand(0,1) == net.demand(1,0)
            empirical = True
            for x in range(8):
                ab = net.run((x,), (0,1))
                ba = net.run((x,), (1,0))
                assert (ab is not None) == (x >= net.demand(0,1)[0])
                assert (ba is not None) == (x >= net.demand(1,0)[0])
                if (ab is None) != (ba is None): empirical = False
                if ab is not None and ba is not None: assert ab[-1] == ba[-1]
                comparisons += 1
            assert match == empirical
            commuting += match
    return {'transition_pairs':256, 'marking_comparisons':comparisons,
            'commuting_pairs_including_equal_transitions':commuting}


def test_normal_forms(max_m=4, max_length=6):
    """Compare with connected components of the adjacent-swap graph.

The oracle does not use the forbidden-set recurrence: a disjoint-set union
computes whole equivalence classes from the defining local swaps.
"""
    graphs, words_tested, classes_tested = 0, 0, 0
    for m in range(1,max_m+1):
        edges = list(combinations(range(m),2))
        for mask in range(1<<len(edges)):
            I = frozenset(pair for j,(a,b) in enumerate(edges) if mask>>j&1
                          for pair in ((a,b),(b,a)))
            net = graph_realization(m,I)
            assert net.independence() == I
            graphs += 1
            for n in range(max_length+1):
                words = list(product(range(m), repeat=n))
                parents = list(range(len(words)))
                def root(i):
                    while parents[i] != i:
                        parents[i] = parents[parents[i]]
                        i = parents[i]
                    return i
                def union(i,j):
                    x,y=root(i),root(j)
                    if x != y:
                        # The representative is the least lexicographic index.
                        if x > y: x,y=y,x
                        parents[y]=x
                powers=[m**k for k in range(n)]
                for code,word in enumerate(words):
                    for k in range(n-1):
                        a,b=word[k:k+2]
                        if a>b and (a,b) in I:
                            neighbor=code+(b-a)*powers[n-k-1]+(a-b)*powers[n-k-2]
                            union(code,neighbor)
                normal_count=0
                for code,word in enumerate(words):
                    accepted,_=forbidden_history(word,m,I)
                    assert accepted == (code==root(code)), (m,mask,word)
                    normal_count += accepted
                classes_tested += normal_count
                words_tested += len(words)
    return {'alphabets_up_to':max_m, 'lengths_up_to':max_length,
            'independence_graphs':graphs, 'words':words_tested, 'classes':classes_tested}


def test_memory_bound():
    subsets=0
    for k in range(1,8):
        m=2*k
        # a_i=2*i, b_i=2*i+1, I(a_i,b_j) iff j<=i.
        I=frozenset(pair for i in range(k) for j in range(i+1)
                    for pair in ((2*i,2*j+1),(2*j+1,2*i)))
        for mask in range(1<<k):
            word=tuple(2*i+1 for i in range(k-1,-1,-1) if mask>>i&1)
            ok,flags=forbidden_history(word,m,I)
            assert ok
            assert tuple(flags[-1][2*i] for i in range(k)) == tuple(mask>>i&1 for i in range(k))
            for i in range(k):
                accepted,_=forbidden_history(word+(2*i,),m,I)
                assert accepted == (not (mask>>i&1))
            subsets+=1
    return {'k_up_to':7,'distinguishable_prefix_subsets_checked':subsets}


def test_certificates(out):
    # a produces, b is a no-op, c consumes: I={(a,b),(b,c)}.
    net=Net(((0,),(0,),(1,)),((1,),(0,),(0,)),('a','b','c'))
    cases=[]; mutations=0; witnesses=0
    for initial,final,T in [((0,),(0,),0),((0,),(0,),4),((2,),(2,),6),((1,),(2,),5)]:
        raw=[word for word,mark in enabled_runs(net,initial,T) if mark==final]
        canon=[w for w in raw if forbidden_history(w,net.m,net.independence())[0]]
        # Check each raw word's whole swap orbit retains executability/endpoints.
        I=net.independence()
        for word in raw:
            for j in range(T-1):
                if (word[j],word[j+1]) in I:
                    switched=word[:j]+(word[j+1],word[j])+word[j+2:]
                    tr=net.run(initial,switched)
                    assert tr is not None and tr[-1]==final
        record={'initial':initial,'final':final,'horizon':T,'raw_runs':len(raw),'classes':len(canon)}
        for form in ('raw','quartic','quadratic'):
            cert=compile_certificate(net,initial,final,T,form)
            words=raw if form=='raw' else canon
            if form=='quartic':
                assert len(cert.variables)==(2*T+1)*(net.d+net.m)
                assert len(cert.residuals)==2*(T+1)*net.d+(T+1)*net.m+2*T
            if form=='quadratic':
                assert len(cert.variables)==(2*T+1)*net.d+(7*T+1)*net.m
                assert len(cert.residuals)==2*(T+1)*net.d+(5*T+1)*net.m+T
                assert all(r.degree<=1 for r in cert.residuals)
            record[form]={'variables':len(cert.variables),'residuals':len(cert.residuals),
                          'degree_bound':cert.degree_bound}
            for word in words:
                env=cert.witness(word)
                assert cert.decode(env)==word and cert.energy(env)==0
                witnesses+=1
            # Exhaustively mutate one selected witness in each coordinate.
            if words:
                env=cert.witness(words[0])
                for name in cert.variables:
                    env[name]+=1
                    assert not cert.zero(env), (form,name)
                    env[name]-=1
                    mutations+=1
            if T==6:
                cert.export(str(out/f'example_{form}.json'))
                if words:
                    (out/f'witness_{form}.json').write_text(json.dumps(cert.witness(words[0]),indent=2)+'\n')
        cases.append(record)
    # A full, forced-height box search: d=0, m=2, T=1.
    tiny=Net(((),()),((),()))
    cert=compile_certificate(tiny,(),(),1,'quadratic')
    zeros=[]
    for values in product((0,1),repeat=len(cert.variables)):
        env=dict(zip(cert.variables,values))
        if cert.zero(env): zeros.append(cert.decode(env))
    assert sorted(zeros)==[(0,),(1,)]
    # Fully expand one small example and check its actual polynomial degree.
    expanded=cert.expanded_polynomial()
    assert expanded.degree==2
    (out/'tiny_expanded_polynomial.txt').write_text(expanded.text()+'\n')
    # Real feasibility without integer feasibility, verified exactly by doubling
    # an assignment and using Fraction arithmetic rather than the integer API.
    from fractions import Fraction
    gapnet=Net(((2,0),(0,2)),((0,0),(0,0)))
    gap=compile_certificate(gapnet,(1,1),(0,0),1,'quadratic')
    env={name:Fraction(0) for name in gap.variables}
    for p in range(2): env[f'x_0_{p}']=Fraction(1)
    env['e_0_0']=env['e_0_1']=Fraction(1,2)
    I=gap.independence
    for a in range(2):
        c=sum(env[f'e_0_{b}'] for b in range(2) if (a,b) in I)
        h=sum(env[f'e_0_{b}'] for b in range(a+1,2) if (a,b) in I)
        env[f'f_1_{a}']=h
        env[f's2_0_{a}']=c-h
        env[f's3_0_{a}']=1-(c-h)
        env[f's4_0_{a}']=1-env[f'e_0_{a}']
    assert all(r.evaluate(env)==0 for r in gap.residuals)
    assert list(enabled_runs(gapnet,(1,1),1))==[]
    return {'examples':cases,'constructed_witnesses':witnesses,
            'single_coordinate_mutations_rejected':mutations,
            'full_binary_box_assignments':2**len(cert.variables), 'full_box_zeros':len(zeros),
            'tiny_expanded_monomials':len(expanded.terms), 'integrality_gap_verified':True}


def test_circuits():
    cases=[(2,[('AND',(0,1))],2,1),
           (2,[('OR',(0,1))],2,3),
           (2,[('OR',(0,1)),('AND',(0,1)),('NOT',(3,)),('AND',(2,4))],5,2),
           (1,[('AND',(0,0)),('NOT',(1,))],2,1)]
    results=[]
    for n,gates,output,expected in cases:
        net,initial,final,T=circuit_net(n,gates,output)
        runs=[w for w,f in enabled_runs(net,initial,T) if f==final]
        assert len(runs)==expected
        vectors=set()
        for word in runs:
            trace=net.run(initial,word)
            assert max((x for row in trace for x in row),default=0)<=1
            parikh=tuple(Counter(word)[a] for a in range(net.m))
            vectors.add(parikh)
            assert forbidden_history(word,net.m,net.independence())[0]
        assert len(vectors)==expected
        cert=compile_certificate(net,initial,final,T,'quadratic')
        for word in runs: assert cert.zero(cert.witness(word))
        results.append({'inputs':n,'gates':len(gates),'horizon':T,'labels':net.m,
                        'places':net.d,'accepting_runs':len(runs),'safe':True})
    return results


def test_ballot_formula():
    from math import comb
    def choose(n,k): return comb(n,k) if 0 <= k <= n else 0
    net=Net(((0,),(0,),(1,)),((1,),(0,),(0,)))
    I=net.independence(); comparisons=0
    for M in range(4):
        for T in range(8):
            raw=Counter(); classes=Counter()
            for word,mark in enabled_runs(net,(M,),T):
                raw[mark[0]]+=1
                if forbidden_history(word,net.m,I)[0]: classes[mark[0]]+=1
            for N in range(5):
                total_raw=total_classes=0
                for ell in range(T+1):
                    twice_r=ell+N-M
                    if twice_r%2 or not 0 <= twice_r//2 <= ell: continue
                    r=twice_r//2
                    count=choose(ell,r)-choose(ell,r+M+1)
                    total_classes+=count
                    total_raw+=choose(T,ell)*count
                assert (raw[N],classes[N])==(total_raw,total_classes)
                comparisons+=1
    return {'endpoint_horizon_instances':comparisons,'max_horizon':7}


def test_guarded_translations():
    # Scalar lower guards 0,1,2; post values 0,1,2; upper guards
    # lower, lower+1, and infinity. Domains are always nonempty.
    rules=[(lo,post,hi) for lo in range(3) for post in range(3)
           for hi in (lo,lo+1,None)]
    pairs=comparisons=0
    for lo,post,hi in rules:
        for lo2,post2,hi2 in rules:
            net=Net(((lo,),(lo2,)),((post,),(post2,)))
            upper=((hi,),(hi2,))
            exact=(0,1) in interval_independence(net,upper)
            empirical=True
            for x in range(9):
                ab=guarded_run(net,upper,(x,),(0,1))
                ba=guarded_run(net,upper,(x,),(1,0))
                if (ab is None)!=(ba is None): empirical=False
                if ab is not None and ba is not None: assert ab[-1]==ba[-1]
                comparisons+=1
            assert exact==empirical
            pairs+=1
    # Increment, zero-test/no-op, decrement. A zero guard must prevent
    # the unguarded no-op from being mistaken for an independent action.
    net=Net(((0,),(0,),(1,)),((1,),(0,),(0,)))
    upper=((None,),(0,),(None,))
    witnesses=0; instances=0
    for T in range(5):
        for M in range(3):
            for N in range(3):
                raw=[word for word in product(range(net.m),repeat=T)
                     if (tr:=guarded_run(net,upper,(M,),word)) is not None and tr[-1]==(N,)]
                I=interval_independence(net,upper)
                for word in raw:
                    for j in range(T-1):
                        if (word[j],word[j+1]) in I:
                            swapped=word[:j]+(word[j+1],word[j])+word[j+2:]
                            assert guarded_run(net,upper,(M,),swapped)[-1]==(N,)
                for form in ('raw','quartic','quadratic'):
                    cert=compile_certificate(net,(M,),(N,),T,form,upper=upper)
                    words=raw if form=='raw' else [w for w in raw if forbidden_history(w,net.m,I)[0]]
                    for word in words:
                        env=cert.witness(word)
                        assert cert.decode(env)==word
                        witnesses+=1
                    if form=='quadratic':
                        assert len(cert.variables)==(2*T+1)*net.d+(7*T+1)*net.m+T
                        assert len(cert.residuals)==2*(T+1)*net.d+(5*T+1)*net.m+T+T
                        assert cert.degree_bound<=2
                instances+=1
    return {'transition_pairs':pairs,'marking_comparisons':comparisons,
            'bounded_instances':instances,'constructed_witnesses':witnesses}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    parser.add_argument('--quick',action='store_true',help='Shorten only the exhaustive normal-form check.')
    args=parser.parse_args(); args.output.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    results={
        'status':'PASS',
        'arithmetic':'exact integers (one explicitly marked exact rational relaxation example)',
        'demand_criterion':test_demands(),
        'normal_forms':test_normal_forms(max_length=4 if args.quick else 6),
        'memory_lower_bound':test_memory_bound(),
        'certificates':test_certificates(args.output),
        'circuit_reduction':test_circuits(),
        'ballot_formula':test_ballot_formula(),
        'guarded_translations':test_guarded_translations(),
    }
    results['elapsed_seconds']=round(time.perf_counter()-start,3)
    (args.output/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__': main()

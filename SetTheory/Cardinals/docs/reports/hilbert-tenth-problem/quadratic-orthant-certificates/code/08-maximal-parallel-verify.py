#!/usr/bin/env python3
"""Deterministic exact checks. Tests support, but do not replace, article proofs."""
from __future__ import annotations
from itertools import product, combinations
from math import comb
from pathlib import Path
from time import perf_counter
import json
import platform

from parallel_certificates import (Network, Atom, RoundCertificate, HistoryCertificate, resource_cover_rank,
                                   trace_count)

stats: dict[str, int] = {}


def comparator_test() -> None:
    checks = 0
    for a in range(1, 8):
        for r in range(13):
            zeros = []
            for b, c, v, w in product(range(3), range(3), range(14), range(14)):
                value = (b+c-1)**2 + (r+v-(a-1)-b-w)**2 + b*v + c*w
                assert value >= 0
                if value == 0:
                    zeros.append((b,c,v,w))
                checks += 1
            expected = (1,0,0,r-a) if r >= a else (0,1,a-1-r,0)
            assert zeros == [expected], (a, r, zeros)
    stats['comparator_assignments'] = checks


def full_root_test() -> None:
    net = Network(((1,),), ((2,),))
    compiler = RoundCertificate(net)
    checks = roots = 0
    for x in range(3):
        for y in range(5):
            actual = []
            for vals in product(range(3), repeat=len(compiler.auxiliary_names)):
                assignment = {'x0':x, 'y0':y, **dict(zip(compiler.auxiliary_names, vals))}
                p = compiler.polynomial.evaluate(assignment)
                assert p >= 0
                if p == 0:
                    actual.append(assignment)
                    roots += 1
                checks += 1
            expected = compiler.canonical_assignment((x,), (x,), (y,))
            assert actual == ([] if expected is None else [expected])
    stats['full_polynomial_assignments'] = checks
    stats['full_polynomial_roots'] = roots


def many_networks_test() -> None:
    cols = [c for c in product(range(3), repeat=2) if any(c)]
    candidate_count = legal_count = mutations = 0
    for col1, col2 in product(cols, repeat=2):
        net = Network((col1, col2), ((1,0), (0,2)))
        compiler = RoundCertificate(net)
        assert len(compiler.auxiliary_names) == net.d + 2*net.m + 4*len(net.thresholds)
        assert len(compiler.polynomial.squares) == 2*net.d + 2*len(net.thresholds) + net.m
        assert len(compiler.polynomial.products) == 2*len(net.thresholds)
        for x in product(range(5), repeat=2):
            bounds = [min(x[i]//a for i,a in enumerate(col) if a) for col in net.consume]
            for f in product(*(range(b+1) for b in bounds)):
                candidate_count += 1
                r = tuple(x[i] - sum(net.consume[j][i]*f[j] for j in range(net.m))
                          for i in range(net.d))
                feasible = min(r) >= 0
                maximal = feasible and all(any(a > r[i] for i,a in enumerate(col))
                                            for col in net.consume)
                witness = compiler.canonical_assignment(x,f)
                assert (witness is not None) == maximal
                if witness is not None:
                    legal_count += 1
                    assert compiler.polynomial.evaluate(witness) == 0
                    expanded_value = sum(c * prod(witness[k] for k in monomial)
                                         for monomial,c in compiler.polynomial.expanded().items())
                    assert expanded_value == 0
                    # Every auxiliary is forced when the extent and endpoints are fixed;
                    # changing any one coordinate must destroy the zero.
                    for name in compiler.auxiliary_names:
                        changed = dict(witness)
                        changed[name] += 1
                        assert compiler.polynomial.evaluate(changed) > 0
                        mutations += 1
                    wrong_y = list(witness[k] for k in compiler.output_names)
                    wrong_y[0] += 1
                    assert compiler.canonical_assignment(x,f,wrong_y) is None
    stats['networks_exhausted'] = len(cols)**2
    stats['round_candidates'] = candidate_count
    stats['round_roots_constructed'] = legal_count
    stats['single_coordinate_mutations_rejected'] = mutations


def prod(values):
    p = 1
    for v in values:
        p *= v
    return p


def variants_test() -> None:
    # A two-branch zero/decrement instruction, both branches with genuine guards.
    net = Network(((1,1,0), (1,0,0)), ((0,0,1), (0,0,1)),
                  ((Atom(0,1), Atom(1,1)), (Atom(0,1), Atom(1,1,False))))
    rounds = 0
    for flat in (False, True):
        for keep in ((1,1,1), (0,0,0), (1,0,1)):
            compiler = RoundCertificate(net, flat=flat, retention=keep)
            for n in range(12):
                x = (1,n,0)
                choices = list(net.outcomes(x,flat,keep))
                assert len(choices) == 1
                f,y = choices[0]
                assert f == ((1,0) if n else (0,1))
                assert compiler.canonical_assignment(x,f,y) is not None
                rounds += 1
    # Same-round product reuse is illegal: A->B, B->C from one A.
    chain = Network(((1,0,0),(0,1,0)), ((0,1,0),(0,0,1)))
    assert not chain.legal((1,0,0),(1,1))
    assert list(chain.outcomes((1,0,0))) == [((1,0),(0,1,0))]
    # Maximal need not mean maximum cardinality: A->0 and 2A->0.
    competing = Network(((1,),(2,)), ((0,),(0,)))
    assert set(f for f,_ in competing.outcomes((2,))) == {(2,0),(0,1)}
    # Products alone do not decide terminality within this round: A->A.
    recycle = Network(((1,),), ((1,),))
    assert recycle.legal((3,),(3,))
    assert not recycle.legal((3,),(2,))
    # Ordinary and flat semantics are observably different.
    flat = RoundCertificate(recycle,flat=True)
    assert flat.canonical_assignment((3,),(1,),(3,)) is not None
    assert not recycle.legal((3,),(1,),False)
    stats['guarded_flat_retention_rounds'] = rounds
    stats['semantic_regressions'] = 7


def growth_test() -> None:
    tests = 0
    for m in range(1,4):
        consume = tuple((1,)+(0,)*m for _ in range(m))
        produce = tuple((1,)+tuple(int(i==j) for i in range(m)) for j in range(m))
        net = Network(consume,produce)
        assert resource_cover_rank(net)[0] == 1
        for n in range(6):
            for t in range(4):
                assert trace_count(net,(n,)+(0,)*m,t) == comb(n+m-1,m-1)**t
                tests += 1
    # Three independent pools with 2,1,3 competitors: rho=3, m-rho=3.
    sizes = (2,1,3)
    cols = tuple(tuple(int(i==g) for i in range(3)) for g,s in enumerate(sizes) for _ in range(s))
    net = Network(cols,cols)
    assert resource_cover_rank(net)[0] == 3
    for n in range(7):
        expected = prod(comb(n+s-1,s-1) for s in sizes)
        assert sum(1 for _ in net.outcomes((n,n,n))) == expected
        tests += 1
    # A genuinely periodic one-step counting sequence: f1+f2=floor(n/2).
    doubled = Network(((2,), (2,)), ((0,), (0,)))
    for n in range(25):
        assert sum(1 for _ in doubled.outcomes((n,))) == n//2+1
        tests += 1
    # Flat shared-pool counts stabilize once n>=m.
    for m in range(1,5):
        net = Network(tuple((1,) for _ in range(m)), tuple((1,) for _ in range(m)))
        for n in range(m,m+5):
            assert trace_count(net,(n,),3,flat=True) == 1
            tests += 1
    stats['exact_count_identities'] = tests



def history_test() -> None:
    cases = 0
    net = Network(((1,0,0),(1,0,0)), ((1,1,0),(1,0,1)))
    for n in range(5):
        for t in range(4):
            compiler = HistoryCertificate(net,t)
            choices = [(k,n-k) for k in range(n+1)]
            for history in product(choices, repeat=t):
                witness = compiler.canonical_assignment((n,0,0),history)
                assert witness is not None
                assert len(compiler.witness_names) == t*(2*net.d+2*net.m+4*len(net.thresholds))
                cases += 1
    consume = Network(((1,),), ((0,),))
    for n in range(6):
        for t in range(4):
            compiler = HistoryCertificate(consume,t,first_halt=True)
            history = (() if t==0 else ((n,),)+((0,),)*(t-1))
            witness = compiler.canonical_assignment((n,),history)
            assert (witness is not None) == ((n==0 and t==0) or (n>0 and t==1))
            cases += 1
    recycle = Network(((1,),), ((1,),))
    for t in range(4):
        assert HistoryCertificate(recycle,t,first_halt=True).canonical_assignment(
            (1,),((1,),)*t) is None
        cases += 1
    stats['history_and_first_halt_cases'] = cases

def graph_test() -> None:
    graphs = network_roots = 0
    for n in range(1,5):
        possible = list(combinations(range(n),2))
        for mask in range(1<<len(possible)):
            edges = [e for i,e in enumerate(possible) if mask>>i&1]
            independent = [s for s in range(1<<n)
                           if all(not (s>>u&1 and s>>v&1) for u,v in edges)]
            hedges = edges + [(u,n+u) for u in range(n)]
            cols = tuple(tuple(int(u in edge) for edge in hedges) for u in range(2*n))
            net = Network(cols,tuple((0,)*len(hedges) for _ in range(2*n)))
            outcomes = list(net.outcomes((1,)*len(hedges)))
            assert len(outcomes) == len(independent)
            expected = {tuple((s>>u)&1 for u in range(n)) +
                        tuple(1-((s>>u)&1) for u in range(n)) for s in independent}
            assert {f for f,_ in outcomes} == expected
            compiler = RoundCertificate(net)
            for f,y in outcomes:
                assert compiler.canonical_assignment((1,)*len(hedges),f,y) is not None
                network_roots += 1
            graphs += 1
    stats['graph_reductions_exhausted'] = graphs
    stats['graph_roots_constructed'] = network_roots


def main() -> None:
    started = perf_counter()
    for test in (comparator_test, full_root_test, many_networks_test,
                 variants_test, growth_test, history_test, graph_test):
        test()
        print(f'PASS {test.__name__}',flush=True)
    print(f'Python {platform.python_version()}')
    for key,value in stats.items():
        print(f'{key}: {value}')
    print(f'Elapsed seconds: {perf_counter()-started:.3f}')
    print('All checks are exact integer arithmetic; finite tests are not general proofs.')
    folder = Path(__file__).resolve().parent.parent / 'data'
    (folder/'verification_counts.json').write_text(json.dumps(stats,indent=2)+'\n')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Independent truth and insertion audit for the native two-marker compiler."""
from itertools import product
from pathlib import Path
import hashlib
import json
import sys

import explore_fixed_raw_universal_84 as candidate

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).with_suffix('.json')


def independent_compile(k, allowed):
    A = 1 << max(2*k,4).bit_length()
    clauses = []
    for site in range(3):
        clauses.append((tuple(int(i//k == site) for i in range(3*k)), A-2))
    for other in (1,2):
        clauses.append((tuple(int(i//k in (0,other)) for i in range(3*k)),1))
    for triple in product(range(k), repeat=3):
        if allowed is not None and triple not in allowed:
            weights = [0]*(3*k)
            for site,symbol in enumerate(triple):
                weights[site*k+symbol] = 2 if site == 2 else 1
            clauses.append((tuple(weights),4))
    mu = sum(mask*A**j for j,(_,mask) in enumerate(clauses))
    while mu.bit_count() < k:
        mu += A**len(clauses)
        clauses.append(((0,)*(3*k),1))
    c = tuple(sum(weights[i]*A**j for j,(weights,_) in enumerate(clauses)) for i in range(3*k))
    m = mu.bit_count()
    target = max((m+2)*sum(c),mu)+2
    R = 1 << (target-1).bit_length()
    B = R**(k+m+1)
    Ds = tuple(sum(c[site*k+i]*R**(k-1-i) for i in range(k)) for site in range(3))
    MC = B-1-sum(R**i for i in range(2,m+2))
    MF = mu*R**(k-1)
    return dict(k=k,A=A,c=c,mu=mu,m=m,R=R,B=B,Ds=Ds,MC=MC,MF=MF,d=B.bit_length()-1)


def check_compile(k, allowed):
    ref = independent_compile(k,allowed)
    actual = candidate.compile_rule(k,allowed)
    for name,value in ref.items():
        assert getattr(actual,name) == value, name
    assert ref['MC'].bit_count()+ref['MF'].bit_count() == ref['d']
    assert ref['MC']%2 == 1 and ref['MF']%2 == 0
    return ref


def scalar_audit():
    cases = accepted = compilations = 0
    def check_relation(k, allowed, fills):
        nonlocal cases,accepted,compilations
        cc = check_compile(k,allowed)
        compilations += 1
        R,B,Ds,m = (cc[key] for key in ('R','B','Ds','m'))
        for flat in product((0,1),repeat=3*k):
            rows = [flat[site*k:(site+1)*k] for site in range(3)]
            occupancy = tuple(sum(row) for row in rows)
            truth = occupancy[0] <= 1 and len(set(occupancy)) == 1
            if truth and occupancy[0]:
                triple = tuple(row.index(1) for row in rows)
                truth = allowed is None or triple in allowed
            for fill in fills:
                full = [row+tuple((fill >> site)&1 for _ in range(m+2-k)) for site,row in enumerate(rows)]
                cells = [sum(bit*R**i for i,bit in enumerate(row)) for row in full]
                field = sum(coef*cell for coef,cell in zip(Ds,cells))
                assert 0 <= field <= B-2
                assert (field & cc['MF'] == 0) == truth
                for bits,cell in zip(full,cells):
                    assert (cell & cc['MC'] == 0) == (not bits[0] and not bits[1])
                cases += 1
                accepted += truth
    triples = tuple(product(range(2),repeat=3))
    for selection in range(256):
        allowed = {triple for i,triple in enumerate(triples) if selection >> i & 1}
        check_relation(2,allowed,(0,7))
    ternary = tuple(product(range(3),repeat=3))
    for allowed in (None,set(),{v for v in ternary if v[0] == v[1]},
                    {v for v in ternary if (v[0]+v[1])%3 == v[2]}):
        check_relation(3,allowed,(0,2,5,7))
    check_compile(32,None)
    return dict(compilations=compilations+1,scalar_and_dummy_cases=cases,accepted_cases=accepted,
                every_binary_ternary_relation=True,mixed_site_dummy_fillings=True,
                expected_truth_independent_of_candidate_helpers=True)


def insertion_audit():
    cc = check_compile(3,None)
    R,B,m = (cc[key] for key in ('R','B','m'))
    DC,DR,DY = cc['Ds']
    cases = nonzero_unit_tails = 0
    for x,h,extra,fill in product(range(1,6),(1,2,3),(1,2),(0,1)):
        t = x+2
        N = h*t+extra
        endpoint = h*t
        states = [1]+[2]*(N-1)
        states[endpoint] = 0
        cells = [R**state+fill*sum(R**i for i in range(3,m+2)) for state in states]
        C = sum(cell*B**i for i,cell in enumerate(cells))
        q,P,W = B**N,B**h,B**endpoint
        Z = C-R-W
        D,J = q-1,(q-1)//(B-1)
        assert 0 < Z < C < q and C+x+2 < q and 0<W<C
        assert Z & (cc['MC']*J) == 0 and Z%2 == 0
        nonzero_unit_tails += bool(Z%B)
        # Each insertion has disjoint binary support; no between-cell carry.
        assert Z & R == 0 and Z & W == 0 and R & W == 0
        assert Z|R|W == Z+R+W == C
        assert sum(cell//R%R == 1 for cell in cells) == 1
        assert sum(cell%R == 1 for cell in cells) == 1
        pack = lambda digits: sum(digit*B**i for i,digit in enumerate(digits))
        RR = pack([cells[(i-h)%N] for i in range(N)])
        YY = pack([cells[(i-h-1)%N] for i in range(N)])
        F = DC*C+DR*RR+DY*YY
        assert 0 < F < D and F & (cc['MF']*J) == 0
        kR,kY = (P*C-RR)//D,(B*P*C-YY)//D
        zquot = DR*kR+DY*kY
        assert C >= J and kR >= 0 and kY >= P and zquot >= DY*P > 0
        assert (DC+(DR+B*DY)*P)*C == F+zquot*D
        S,M = Z+q*F,(cc['MC']+q*cc['MF'])*J
        r = (q*q-S)*(q*q-1)+M
        assert q*q <= r < q**4 and r%2 == 1 and r.bit_count() == 3*cc['d']*N
        cases += 1
    assert nonzero_unit_tails > 0
    return dict(cases=cases,nonzero_unit_tail_cases=nonzero_unit_tails,
                tail_not_required_to_be_divisible_by_B=True,positive_transport_with_minimum_cell_one=True,
                actual_packed_index_odd=True)


def verify():
    paths = [ROOT/'Papers'/'1980'/'FIXED_RAW_UNIVERSAL_84_PROOF.md',
             ROOT/'Papers'/'verification'/'explore_fixed_raw_universal_84.py',
             ROOT/'Papers'/'verification'/'explore_fixed_raw_universal_84.json']
    hashes = lambda: {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    result = dict(status='PASS_INDEPENDENT_FIXED_RAW84',scalar=scalar_audit(),insertions=insertion_audit(),
                  reviewed_sha256=before,scope='Independent compiler truth, two disjoint marker insertions, positive outer witnesses and odd actual index; full proof reviewed separately')
    assert hashes() == before
    return result


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['scalar']['scalar_and_dummy_cases'],'scalar cases;',
          result['insertions']['cases'],'two-marker insertions')

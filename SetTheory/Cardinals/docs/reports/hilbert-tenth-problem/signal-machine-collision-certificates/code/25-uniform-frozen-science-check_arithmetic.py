#!/usr/bin/env python3
"""Fresh arithmetic checks for PROOF-NOTE.md; not a CA/rule compiler.
This script imports no upstream code and runs no saved schedule.
"""
from fractions import Fraction
from itertools import product
from random import Random
from hashlib import sha256
from pathlib import Path
import json

COUNTS = {}

def ceil_div(a, b):
    assert b > 0
    return -((-a) // b)


def first_contact(A, d, radius):
    """Least k>=0 with -radius <= A+d*k <= radius, or None."""
    if d == 0:
        return 0 if -radius <= A <= radius else None
    if d < 0:
        A, d = -A, -d
    k = max(0, ceil_div(-radius-A, d))
    return k if A+d*k <= radius else None


def test_first_contact():
    n = 0
    for A in range(-100, 101):
        for d in range(-9, 10):
            for radius in range(0, 7):
                found = first_contact(A, d, radius)
                brute = next((k for k in range(220) if -radius <= A+d*k <= radius), None)
                assert found == brute, (A, d, radius, found, brute)
                if d:
                    den = abs(d)
                    rhs = -radius-(A if d > 0 else -A)
                    residue = rhs % den
                    # For fixed residue, this is an affine expression in rhs.
                    affine_ceiling = (rhs-residue)//den+(residue != 0)
                    assert affine_ceiling == ceil_div(rhs, den)
                n += 1
    COUNTS['first_contact_interval_cases'] = n


def offsets(word):
    result = [0]
    for c in word:
        result.append(result[-1]+c)
    return result


def accelerated(d, N, word, shifts, alphas, betas):
    cs = offsets(word)
    es = offsets(shifts)
    delta, E = cs[-1], es[-1]
    assert delta < 0
    a, b = -delta, min(cs)
    K = max(0, ceil_div(d+b-N, a))
    fail = next(s for s in range(1, len(cs)) if d+K*delta+cs[s] <= N)
    assert all(d+K*delta+cs[s] > N for s in range(fail))
    assert d+K*delta > N
    A = sum(alphas)
    B = sum(alphas[i]*cs[i]+betas[i] for i in range(len(word)))
    As = sum(alphas[:fail])
    Bs = sum(alphas[i]*cs[i]+betas[i] for i in range(fail))
    time = K*(A*d+B)+A*delta*Fraction(K*(K-1),2)+As*(d+K*delta)+Bs
    gap = d+K*delta+cs[fail]
    anchor = K*E+es[fail]
    return K, fail, gap, anchor, time


def direct(d, N, word, shifts, alphas, betas):
    gap, anchor, time, edges = d, 0, Fraction(0), 0
    while gap > N:
        i = edges % len(word)
        time += alphas[i]*gap+betas[i]
        anchor += shifts[i]
        gap += word[i]
        edges += 1
        assert edges < 100000
    K, r = divmod(edges, len(word))
    # A failed final edge means that cycle was not wholly live-to-live.
    if r == 0:
        K, r = K-1, len(word)
    return K, r, gap, anchor, time


def test_contracting_cycles():
    n = 0
    rng = Random(20261004)
    words = [w for m in range(1,5) for w in product(range(-3,4), repeat=m) if sum(w)<0]
    words += [tuple(rng.randint(-20,20) for _ in range(rng.randint(2,12))) for _ in range(300)]
    words = [w for w in words if sum(w)<0]
    for wi, word in enumerate(words):
        m = len(word)
        shifts = [((3*i+wi)%11)-5 for i in range(m)]
        alphas = [Fraction((i+wi)%7+1, (i%3)+1) for i in range(m)]
        betas = [Fraction((i*wi)%9+1, (i%3)+1) for i in range(m)]
        N = 40
        for d in range(N+1, N+51):
            got = accelerated(d,N,word,shifts,alphas,betas)
            expect = direct(d,N,word,shifts,alphas,betas)
            assert got == expect, (word,d,got,expect)
            cs = offsets(word)
            K = got[0]
            assert all(d+k*sum(word)+c > N for k in range(K) for c in cs)
            assert not all(d+K*sum(word)+c > N for c in cs)
            # Piecewise-affine substitution K=(d+b-N-r)/a+[r!=0]
            # on the positive branch, with no division by an input variable.
            v, a = d+min(cs)-N, -sum(word)
            if v > 0:
                r = v % a
                assert K == (v-r)//a + (r != 0)
            else:
                assert K == 0
            n += 1
    COUNTS['contracting_cycle_direct_comparisons'] = n
    COUNTS['distinct_contracting_words'] = len(words)


def test_huge_and_noncontracting():
    count = 0
    for word in [(-2,), (5,-8,2,-3), (-7,12,-11), (8,-12,5,-3), (20,-5,-17)]:
        if sum(word)>=0:
            continue
        cs = offsets(word)
        N=40
        for exponent in [12,40,100]:
            for small in range(7):
                d=10**exponent+small
                got=accelerated(d,N,word,[i-2 for i in range(len(word))],
                    [Fraction(i+1) for i in range(len(word))],[Fraction(i+2) for i in range(len(word))])
                K=got[0]
                assert all(d+(K-1)*sum(word)+c>N for c in cs) if K else True
                assert any(d+K*sum(word)+c<=N for c in cs)
                assert d+K*sum(word)>N
                count += 1
    COUNTS['huge_integer_contracting_cases'] = count
    count=0
    for m in range(1,5):
        for word in product(range(-3,4), repeat=m):
            if sum(word)<0:
                continue
            cs=offsets(word)
            N=40
            d=N-min(cs)+1
            for k in range(30):
                assert all(d+k*sum(word)+c>N for c in cs)
            # One smaller initial gap fails an endpoint of the first cycle.
            assert any((d-1)+c<=N for c in cs)
            count+=1
    COUNTS['nonnegative_cycle_guard_cases'] = count


def test_two_input_substitution_degree():
    # Freeze a residue branch where d=6u+2v+101 and a=2,
    # K=(d+b-N)/2 with b=-6, N=41, giving K=3u+v+27.
    # Time uses d*K and K*(K-1), so every third finite difference
    # in arbitrary directions must vanish. All calculations are exact.
    def polynomial(u,v):
        d=6*u+2*v+101
        K=3*u+v+27
        assert K==ceil_div(d-6-41,2)
        return Fraction(7,3)*K*d-Fraction(14,3)*Fraction(K*(K-1),2)+5*K+Fraction(11,2)*d+3
    n=0
    for u in range(5):
        for v in range(5):
            for du,dv in product(range(3),repeat=2):
                values=[polynomial(u+i*du,v+i*dv) for i in range(4)]
                assert values[3]-3*values[2]+3*values[1]-values[0]==0
                n+=1
    COUNTS['quadratic_substitution_directional_checks']=n


def main():
    test_first_contact()
    test_contracting_cycles()
    test_huge_and_noncontracting()
    test_two_input_substitution_degree()
    here=Path(__file__).resolve().parent
    report={'status':'PASS','scope':'Fresh finite arithmetic fixtures only; not an all-rules proof or CA compiler',
            'counts':COUNTS,'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'executed_upstream_code':False,'executed_saved_schedules':False}
    (here/'arithmetic-check-results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()

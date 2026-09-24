#!/usr/bin/env python3
"""Exact-arithmetic regression checks for the corrected Jones--Matijasevic article.

Python 3.9+; standard library only. Run without -O (assertions are the tests).
Finite tests supplement, and do not replace, the proofs in editorial_notes.pdf.
The output CSV is generated from the program, not transcribed from the scan.
Self-contained (reads no article source).
Writes jones1984_example1_trace.csv and jones1984_verification_results.txt.
"""
from __future__ import annotations

import csv
import itertools
import math
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parent

def mask(a: int, b: int) -> bool:
    """Natural-number masking, with out-of-domain arguments treated as false."""
    return a >= 0 and b >= 0 and (a & b) == a

def pack(digits: Sequence[int], q: int) -> int:
    return sum(d * q**t for t, d in enumerate(digits))

def submasks(value: int) -> Iterable[int]:
    result = value
    while True:
        yield result
        if result == 0:
            break
        result = (result - 1) & value

def choose(n: int, k: int) -> int:
    return math.comb(n, k) if k <= n else 0

def example1(x: int, limit: int = 200000) -> Tuple[str, List[Tuple[int, Tuple[int, ...]]]]:
    """Execute all parallel assignments from old register values.

    Return 'halt', 'cycle', or 'limit', and pre-instruction configurations.
    A limit is not a proof of divergence. Repeated full states are.
    """
    if x < 0:
        raise ValueError("Input must be nonnegative")
    regs = [x, 0, 0, 0]
    pc = 0
    trace = []
    seen = set()
    for _ in range(limit):
        state = (pc, tuple(regs))
        if state in seen:
            return "cycle", trace
        seen.add(state)
        trace.append(state)
        old = regs[:]
        nxt = pc + 1
        if pc in (0, 1):
            regs[1] = old[1] + 1
        elif pc == 2:
            nxt = 5 if old[2] == 0 else 3
        elif pc == 3:
            regs[2] = old[2] - 1
        elif pc == 4:
            nxt = 2
        elif pc == 5:
            regs[2], regs[3], regs[1] = old[2]+1, old[3]+1, old[1]-1
        elif pc == 6:
            nxt = 5 if old[1] > 0 else 7
        elif pc == 7:
            regs[1], regs[3] = old[1]+1, old[3]-1
        elif pc == 8:
            nxt = 7 if old[3] > 0 else 9
        elif pc == 9:
            nxt = 5 if old[2] < old[0] else 10
        elif pc == 10:
            nxt = 1 if old[0] < old[2] else 11
        elif pc == 11:
            nxt = 10 if old[1] < old[0] else 12
        elif pc == 12:
            regs[0], regs[1], regs[2] = old[0]-1, old[1]-1, old[2]-1
        elif pc == 13:
            nxt = 12 if old[0] > 0 else 14
        elif pc == 14:
            return "halt", trace
        else:
            raise AssertionError("Invalid program counter")
        assert min(regs) >= 0, (x, state, regs)
        pc = nxt
    return "limit", trace

def check_example_encoding(trace: Sequence[Tuple[int, Tuple[int, ...]]], x: int) -> None:
    s, ell = len(trace)-1, 14
    q = 2**(x+s+ell+2)
    I = sum(q**t for t in range(s+1))
    R = [pack([state[1][j] for state in trace], q) for j in range(4)]
    L = [pack([int(state[0] == i) for state in trace], q) for i in range(15)]
    assert x+s < q//2 and ell+1 < q
    assert 1+(q-1)*I == q**(s+1)
    assert all(mask(v, (q//2-1)*I) for v in R)
    assert all(mask(v, I) for v in L) and sum(L) == I
    assert mask(1, L[0]) and L[14] == q**s
    assert mask(q*L[4], L[2])
    for i in [0, 1, 3, 5, 7, 12]:
        assert mask(q*L[i], L[i+1])
    assert mask(q*L[2], L[5]+L[3])
    assert mask(q*L[2], L[3]+q*I-2*R[2])
    for i,k,a,b in [(6,5,0,R[1]), (8,7,0,R[3]), (9,5,R[2],R[0]),
                       (10,1,R[0],R[2]), (11,10,R[1],R[0]), (13,12,0,R[0])]:
        assert mask(q*L[i], L[k]+L[i+1])
        assert mask(q*L[i], L[k]+q*I+2*a-2*b)
    inc = [[], [0,1,7], [5], [5]]
    dec = [[12], [5,12], [3,12], [7]]
    for j in range(4):
        assert R[j] == q*R[j] + q*sum(L[k] for k in inc[j]) - q*sum(L[k] for k in dec[j]) + (x if j == 0 else 0)

def main() -> None:
    if not __debug__:
        raise RuntimeError("Do not run this verification script with Python -O")
    report: List[str] = []
    def record(message: str) -> None:
        report.append(message)
        print(message)

    count = 0
    for n in range(21):
        u = 2**n + 1
        value = (u+1)**n
        for k in range(n+4):
            w, low = divmod(value, u**(k+1))
            m, v = divmod(low, u**k)
            assert m == choose(n,k) and v < u**k and m < u
            assert value == w*u**(k+1) + m*u**k + v
            count += 1
    record(f"PASS (8): {count} digit-extraction cases, n=0..20, k=0..n+3.")

    for x,y in itertools.product(range(21), range(2,21)):
        modulus = 2**(x*y) - x
        assert modulus > 0 and x**y < modulus
        assert pow(2, x*y*y, modulus) == x**y
    record("PASS (9): 399 cases, x=0..20, y=2..20.")

    for a,b,c in itertools.product(range(64), repeat=3):
        assert ((a & b) == c) == (mask(c,b) and mask(b,a+b-c)), (a,b,c)
    record("PASS (11): all 262144 triples a,b,c=0..63.")
    for a in range(4096):
        power = a > 0 and (a & (a-1)) == 0
        assert power == (a > 0 and mask(a,2*a-1))
    record("PASS (12): a=0..4095, with explicit positivity.")
    count = 0
    for q in [1,2,4,8]:
        for a,b,c,d in itertools.product(range(q),range(q),range(16),range(16)):
            assert (mask(a,b) and mask(c,d)) == mask(a+c*q,b+d*q)
            count += 1
    record(f"PASS (13): {count} concatenation cases.")
    for p in [2,3,5,7]:
        for s,r in itertools.product(range(81), repeat=2):
            a,b,product = s,r,1
            while a or b:
                product = product * choose(a%p,b%p) % p
                a,b = a//p,b//p
            assert choose(s,r)%p == product
            if p == 2:
                assert mask(r,s) == (choose(s,r)%2 == 1)
    record("PASS (14) and masking lemma: 26244 cases, primes 2,3,5,7; r,s=0..80.")

    for x,s,ell in itertools.product(range(21), repeat=3):
        q = 2**(x+s+ell+2)
        assert x+s < q//2 and ell+1 < q
    for x,s,ell in itertools.product(range(101), range(21), range(21)):
        q = 2**(s+x.bit_length()+ell+3)
        assert 2**s*(x+1) < q//2 and ell+1 < q
    record("PASS base choices: 9261 basic and 44541 polynomial-bit-size cases, including zeros.")

    # In these local tests labels are distinct: active=0, target=1, next=2, other=3.
    branch_cases = 0
    for q in [4,8]:
        n = 3
        I = sum(q**t for t in range(n))
        vectors = list(itertools.product(range(q//2), repeat=n))
        for pcs in itertools.product(range(4), repeat=n):
            if pcs[-1] == 0 or 0 not in pcs:
                continue
            if any(pcs[t] == 0 and pcs[t+1] not in (1,2) for t in range(n-1)):
                continue
            A = pack([int(v == 0) for v in pcs],q)
            K = pack([int(v == 1) for v in pcs],q)
            N = pack([int(v == 2) for v in pcs],q)
            assert mask(q*A,K+N)
            for av,bv in itertools.product(vectors, repeat=2):
                a,b = pack(av,q),pack(bv,q)
                expected_lt = all((pcs[t+1] == 1) == (av[t] < bv[t]) for t in range(n-1) if pcs[t] == 0)
                expected_le = all((pcs[t+1] == 1) == (av[t] <= bv[t]) for t in range(n-1) if pcs[t] == 0)
                expected_z = all((pcs[t+1] == 1) == (av[t] == 0) for t in range(n-1) if pcs[t] == 0)
                assert mask(q*A,K+q*I+2*a-2*b) == expected_lt, (q,pcs,av,bv)
                assert mask(q*A,N+q*I+2*b-2*a) == expected_le, (q,pcs,av,bv)
                assert mask(q*A,N+q*I-2*a) == expected_z, (q,pcs,av)
                branch_cases += 1
    record(f"PASS (35)--(37): {branch_cases} three-column cases per formula, distinct branch labels.")

    select_cases,half_cases,original_failures = 0,0,0
    for q in [4,8]:
        n = 3
        I = sum(q**t for t in range(n))
        for rv in itertools.product(range(q//2),repeat=n):
            R = pack(rv,q)
            for lv in itertools.product(range(2),repeat=n):
                L = pack(lv,q)
                expected_M = pack([r*l for r,l in zip(rv,lv)],q)
                # Enumerate exactly the candidates satisfying the first two inequalities.
                for M in submasks(R & ((q-1)*L)):
                    assert mask(M,R) and mask(M,(q-1)*L)
                    assert mask(R,(q-1)*(I-L)+M) == (M == expected_M)
                    select_cases += 1
                expected_J = pack([(r//2)*l for r,l in zip(rv,lv)],q)
                eligible = (R >> 1) & ((q//2-1)*L)
                for J in submasks(eligible):
                    assert mask(2*J,R) and mask(J,(q//2-1)*L)
                    assert mask(R,(q-1)*(I-L)+2*J+L) == (J == expected_J)
                    half_cases += 1
                if not mask(R,(q-1)*(I-L)+2*expected_J+I):
                    original_failures += 1
    record(f"PASS (47): {select_cases} eligible witness cases, Q=4,8 and three columns.")
    record(f"PASS corrected (49): {half_cases} eligible witness cases; unique intended witness.")
    record(f"Printed (49) rejects the intended witness in {original_failures} of the tested R,L cases.")

    # An actual legal ceil-halving/decrement/STOP computation from input 2.
    q,s,x,ell = 32,2,2,2
    I,R,L,J = 1057,34,1,1
    assert I == sum(q**t for t in range(s+1))
    assert 2**s*(x+1) < q//2 and ell+1 < q
    assert mask(2*J,R) and mask(J,(q//2-1)*L)
    original_rhs = (q-1)*(I-L)+2*J+I
    corrected_rhs = (q-1)*(I-L)+2*J+L
    assert original_rhs == 33795 and corrected_rhs == 32739
    assert not mask(R,original_rhs) and mask(R,corrected_rhs)
    assert R == q*R-q*J-q*q+x  # decrement at L1, encoded as Q
    record("CONFIRMED (49) source-error counterexample: Q=32,I=1057,R=34,L=1,J=1.")

    # A spurious accepting computation admitted by the printed self-jump case of (36).
    for q in [8,256]:
        I = 1+q+q*q+q**3
        L0,L1,L2,L3 = 1,q,q*q,q**3
        R1,R2 = 0,q+q*q
        assert sum([L0,L1,L2,L3]) == I
        assert all(mask(v,I) for v in [L0,L1,L2,L3])
        assert mask(R2,(q//2-1)*I)
        assert mask(q*L0,L1) and mask(q*L2,L3)
        assert mask(q*L1,L1+L2)
        assert mask(q*L1,L1+q*I+2*R1-2*R2)
        assert R2 == q*R2+q*L0-q*L2
        assert L3 == q**3 and 3 < q//2 and 4 < q
    record("CONFIRMED (36) self-target counterexample: increment R2; IF R1<R2 GOTO itself; decrement R2; STOP.")
    record("The true run from x=0 repeats the unchanged conditional state forever, yet the printed constraints admit [L0,L1,L2,L3].")

    for value in range(4096):
        current,steps = value,0
        while current > 1:
            current = (current+1)//2
            steps += 1
        if current == 1:
            current -= 1
            steps += 1
        assert current == 0 and steps <= value.bit_length()+1
        assert (value%2 == 0) == (2*((value+1)//2) <= value)
    record("PASS repaired clearing macro and (43): all inputs 0..4095. Ceil-halving alone fixes 1.")
    for a,b in itertools.product(range(101),repeat=2):
        out,j,k = 0,a,b
        while True:
            if k%2:
                out += j
            k //= 2
            j *= 2
            if k == 0:
                break
        assert out == a*b
    record("PASS (45): 10201 input pairs, including zero; source registers are destructive operands.")

    status,trace = example1(2)
    assert status == "halt" and len(trace) == 19 and trace[-1] == (14,(0,0,0,0))
    assert [p for p,_ in trace] == [0,1,2,5,6,5,6,7,8,7,8,9,10,11,12,13,12,13,14]
    check_example_encoding(trace,2)
    with (ROOT/'jones1984_example1_trace.csv').open('w',newline='',encoding='utf-8') as f:
        writer = csv.writer(f,lineterminator='\n')
        writer.writerow(['t','instruction','R1','R2','R3','R4'])
        for t,(pc,regs) in enumerate(trace):
            writer.writerow([t,f'L{pc}',*regs])
    for x in range(2,41):
        status,t = example1(x)
        prime = all(x%d for d in range(2,math.isqrt(x)+1))
        assert (status == 'halt') == prime
        assert status in ('halt','cycle')
        if status == 'halt':
            assert t[-1][1] == (0,0,0,0)
    record("PASS Example 1: all 19 configurations for x=2; 18 transitions; (24)--(39) checked exactly.")
    record("PASS Example 1 on x=2..40: primes halt with zero registers; composites reach a repeated full state.")
    record("No finite bounded run is used to claim nontermination at inputs 0 or 1.")
    record("All regression assertions passed. See editorial notes for proofs and the limits of finite testing.")
    (ROOT/'jones1984_verification_results.txt').write_text('\n'.join(report)+'\n',encoding='utf-8',newline='\n')

if __name__ == '__main__':
    main()

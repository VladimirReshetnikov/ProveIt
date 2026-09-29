#!/usr/bin/env python3
"""A same-cost base-four variant of the 51-operation half-mask module.

This is an exact bounded mask predicate, not a universal certificate.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import sys

import sympy as sp
import explore_one_field_half_mask as binary

HERE = Path(__file__).resolve().parent
PAPERS = HERE.parent.parent
sys.path.insert(0, str(PAPERS / "verification"))
from round37_1980_base_two_pell_regression import pell_power

CORE = [(out, op, 8 if out == "a4" else left,
         15 if out == "a4m5" else right)
        for out, op, left, right in binary.CORE]
SCHEDULE = binary.OUTER + CORE


def sources(z):
    n, F, J = (z[v] for v in ("n", "F", "Jrep"))
    a, c, d, f, h, i, j, k, o, r, s, w, tau, eta, zeta, ga, ya = (
        z[v] for v in binary.CORE_NAMES)
    q, D0 = n**2, n**3
    X, Y = w*D0, s*D0
    delta, H, U = a*a+8*a+15, 8*a+15, j*c-(2*r+1)
    return [
        (z["B"]-1)*J-q+1,
        r-(q-F)*(q-1)-z["m"]*J,
        ((X*Y)**2+X)*(k*Y)**2-tau*(tau+1),
        c-k*Y-eta, k-eta-zeta, k-r-1-h*X*Y,
        a-Y*(X+1), d-X-a*c-ga*H,
        d*d-1-delta*c*c,
        (i*c*c)**2-delta*(f*f-1),
        delta*(f*f-1)*(U*U-ya*ya)-(1-ya*ya),
        U-o*f+c,
    ]


def source_audit():
    z = {v: sp.Symbol(v, positive=True, integer=True)
         for v in binary.NAMES+["B", "m"]}
    env = binary.run(SCHEDULE, dict(z, Bm1=z["B"]-1))
    polynomials = [sp.expand(p) for p in sources(z)]
    U = z["j"]*z["c"]-(2*z["r"]+1)
    correction = polynomials[9]*(U*U-z["y_aux"]**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(binary.EQUALITIES, polynomials)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if ix == 10 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(index=ix, equality=[left, right], sign=sign,
                            source=str(source), correction=str(sp.expand(adjust))))
    counts = Counter(row[1] for row in SCHEDULE)
    assert len(SCHEDULE) == 51 and counts["*"] == 30
    assert counts["+"]+counts["-"] == 21
    assert len(polynomials) == len(binary.EQUALITIES) == 12
    assert len(binary.NAMES) == 20
    assert [(a, b) for a, b in zip(binary.CORE, CORE) if a != b] == [
        (("a4", "*", 4, "a"), ("a4", "*", 8, "a")),
        (("a4m5", "+", "a4", 3), ("a4m5", "+", "a4", 15)),
    ]
    assert sp.expand(env["A"]-((z["a"]+4)**2-1)) == 0
    return dict(operations=51, multiplications=30, additions_subtractions=21,
                positive_parameters=["n", "F"], positive_witness_count=18,
                equations=12, kernel_operations=43,
                schedule=[list(row) for row in SCHEDULE], sources=records,
                recovered_power="X=4^(2r+1)",
                scope="Exact complete half-mask module; no universal compiler")


def pre_power_checks():
    counts = Counter()
    for d in (8, 10):
        B = 1 << d
        for n in range(1, 513):
            q = n*n
            if q < B or (q-1) % (B-1):
                continue
            J = (q-1)//(B-1)
            for m in binary.fixed_masks(d):
                M = m*J
                for F in (1, q//2, q-1, q, q+1):
                    r = (q-F)*(q-1)+M
                    counts["tuples"] += 1
                    if r <= 0:
                        assert F > q
                        continue
                    assert F <= q and 15 <= r < q*q
                    D0 = n**3
                    X = Y = D0
                    a, A, P = Y*(X+1), Y*(X+1)+4, 2*X*Y*Y+1
                    assert D0 >= 4096 and D0*D0 == q**3
                    assert X*Y > r+1 and a > 2*r+1
                    assert P > A and 2*P-1 > 4*A and 16*r < a
                    counts["positive_tuples"] += 1
                    counts["endpoint_tuples"] += F == q
                    counts["nonpower_square_tuples"] += bool(q & (q-1))
    for A in range(2, 100):
        assert (2*A-1)**16 > A*(A*A-1)**2
    for r in range(15, 257):
        assert 4**(3*(2*r+1)) < 4096**(r+1)
        assert 4**(2*r+1) > 64*r
    return dict(counts)


def exact_first_main_examples():
    rows = []
    for r in (3, 7, 15):
        J = 2*r+1
        X = 4**J
        denominator = X**r
        numerator = (X+1)**(2*r)
        Y, remainder = divmod(numerator, denominator)
        a, A = Y*(X+1), Y*(X+1)+4
        Delta, H = A*A-1, 8*a+15
        P = 2*X*Y*Y+1
        d, c = pell_power(A, J)
        chi, k = pell_power(P, r+1)
        tau, tau_rem = divmod(chi-1, 2)
        eta, zeta = c-Y*k, (Y+1)*k-c
        h, hrem = divmod(k-r-1, X*Y)
        ga, garem = divmod(d-X-a*c, H)
        assert tau_rem == hrem == garem == 0
        assert min(tau, eta, zeta, h, ga) > 0
        assert ((X*Y)**2+X)*(k*Y)**2 == tau*(tau+1)
        assert d*d == 1+Delta*c*c and c == Y*k+eta and k == eta+zeta
        assert k == r+1+h*X*Y and d == X+a*c+ga*H
        assert 0 < 4*remainder < denominator
        assert c*denominator > k*numerator
        assert 2*(c*denominator-k*numerator) < k*denominator
        assert Y % (1 << r.bit_count()) == 0
        rows.append(dict(r=r, main_index=J, X_bits=X.bit_length(),
                         Y_bits=Y.bit_length(), c_bits=c.bit_length(),
                         exact_seven_first_main_equations=True,
                         strict_ratio_and_tail=True))
    return dict(examples=rows,
                scope="Small first/main prototypes with base-four constants; not full module witnesses")


def mask_checks():
    counts = Counter()
    for d, N in ((8, 1), (10, 1), (8, 2)):
        B, q = 1 << d, 1 << (d*N)
        J = (q-1)//(B-1)
        masks = binary.fixed_masks(d)
        if N > 1:
            masks = masks[::7]
        for m in masks:
            M, threshold = m*J, 3*d*N//2
            assert M.bit_count() == d*N//2
            assert M.bit_count() < threshold
            counts["endpoint_exclusions"] += 1
            for F in range(1, q):
                r = (q-F)*(q-1)+M
                valid = F & M == 0
                assert r.bit_count() <= threshold
                assert (r.bit_count() == threshold) == valid
                counts["bounded_fields"] += 1
                if valid:
                    assert F % 2 == 0 and r % 2 == 1 and q**3 < r**4
                    counts["valid_fields"] += 1
    return dict(counts)


def arbitrary_mask_parity_checks():
    counts = Counter()
    for d in (8, 10):
        B = q = 1 << d
        for m in range(1, B-1):
            if m.bit_count() != d//2:
                continue
            for F in range(1, q):
                r = (q-F)*(q-1)+m
                mask_ok = F & m == 0
                parity_ok = (F+m) % 2 == 1
                assert r % 2 == (F+m) % 2
                assert (r.bit_count() == 3*d//2 and r % 2 == 1) == (mask_ok and parity_ok)
                if m % 2:
                    assert not mask_ok or parity_ok
                else:
                    assert parity_ok == (F % 2 == 1)
                counts["fields"] += 1
                counts["odd_mask_fields" if m % 2 else "even_mask_fields"] += 1
                if mask_ok and parity_ok:
                    counts["valid_fields"] += 1
    return dict(counts)


def verify():
    dependencies = [HERE / "explore_one_field_half_mask.py",
                    PAPERS / "1980/PELL_INDEX_MULTIPLE_PROOF.md",
                    PAPERS / "1980/EXPLORATION_ODD_INDEX_PELL_SIGNS.md",
                    PAPERS / "1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md"]
    return dict(status="PASS_BASE_FOUR_HALF_MASK_51_MODULE",
                source=source_audit(), pre_power=pre_power_checks(),
                first_main=exact_first_main_examples(), masks=mask_checks(),
                arbitrary_mask_parity=arbitrary_mask_parity_checks(),
                dependencies={str(p.relative_to(PAPERS)):
                    hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest()
                    for p in dependencies},
                established_universal_bound=76,
                scope="Same-cost mask module with an even binary power exponent; compiler remains open")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix(".json")
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    else:
        assert result == json.loads(receipt.read_text(encoding="utf-8"))
    print(result["status"])
    print(result["pre_power"])
    print(result["first_main"])
    print(result["masks"])
    print(result["arbitrary_mask_parity"])

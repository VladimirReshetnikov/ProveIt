#!/usr/bin/env python3
"""Finite regression for the complete narrow binary product packing.

Compiler support is sparse; giant powers are never constructed for it.
Separate bounded integer families test the changed packing and decoding.
The general positive-domain theorem is BINARY_PRODUCT_89_PROOF.md.
"""
from __future__ import annotations

import json
from pathlib import Path

import round37_1980_binary_product_encoding as previous
from round30_1980_linear_radix_encoding import need, sparse_digits

OUT = Path(__file__).with_suffix('.json')


def digit_is_binary(value, B):
    while value:
        value, digit = divmod(value, B)
        if digit > 1:
            return False
    return True


def preliminary_bounds():
    count = overflow = 0
    for B in range(4, 66):
        theta = B-2
        for q in range(8, 97):
            if (q*q-1) % (B-1):
                continue
            la = (q*q-1)//(B-1)
            if la == 0:
                continue
            for C in range(2, 7):
                for ell in sorted({1, q//4, q//2, q-1}):
                    for Omega in (1, 2, 3):
                        sigma, e = Omega*C*C, ell+Omega
                        if not 0 < ell+sigma < q:
                            continue
                        for x in range(1, C):
                            g = C-x
                            for b in sorted({x+1, B-3}):
                                if not x < b < theta:
                                    continue
                                n = q**4
                                S = g+q*sigma+q*q*(ell+e*q)
                                Tp = q*q*theta*la+ell*(theta*q-b)
                                r = S*(n*n-n)+Tp*(n*n-1)
                                need(0 < S < n and 0 < Tp < 2*n,
                                     'pre-exponent word bounds without a power identity')
                                need(n <= r < 3*n**3, 'widened pre-exponent index range')
                                overflow += int(Tp >= n)
                                count += 1
    need(count > 1000, 'nontrivial pre-exponent family')
    return dict(cases=count, Tplus_at_least_n_cases=overflow,
                B_range=[4,65], q_range=[8,96],
                note='Small algebraic bound cases, not fixed-threshold complete witnesses')


def spill_checks():
    count = admissible = spills = 0
    categories = {'0':0, '1':0, 'at_least_2':0}
    for B, L in ((4,2),(4,3),(4,4),(8,2),(8,3),(16,2),(16,3),(32,2)):
        q, theta = B**L, B-2
        la = (q*q-1)//(B-1)
        for b in range(1, theta):
            for ell in range(1, q):
                k, rb = divmod(b*ell, q)
                j, u = divmod(theta*ell-k-1, q)
                Tp = q*q*theta*la+ell*(theta*q-b)
                need(0 < Tp < q**4, 'post-exponent strict mask bound')
                need(0 <= j <= B-3, 'exhausted middle spill range')
                need(Tp-1 == q-1-rb+q*u+q*q*(theta*la+j),
                     'exact normalized mask before canonicality')
                categories['0' if j == 0 else '1' if j == 1 else 'at_least_2'] += 1
                if ell & ((theta*la+j) % q) == 0:
                    need(j == 0, 'any accepted low code rules out a middle spill')
                    need(digit_is_binary(ell, B), 'accepted low code is binary')
                    admissible += 1
                else:
                    spills += int(j != 0)
                count += 1
    need(all(categories.values()), 'both nonzero spill forms were tested')
    return dict(cases=count, accepted_low_codes=admissible,
                rejected_nonzero_spills=spills, spill_categories=categories,
                family='All positive ell<q and 1<=b<B-2 in the eight listed (B,L) pairs',
                radix_exponent_pairs=[[4,2],[4,3],[4,4],[8,2],[8,3],[16,2],[16,3],[32,2]])


def packed_binary_checks():
    count = accepted = 0
    for logn in range(1, 9):
        n = 1 << logn
        for S in range(1, n):
            for Tp in range(1, n):
                r = S*(n*n-n)+Tp*(n*n-1)
                criterion = r.bit_count() >= 2*logn
                no_intersection = S & (Tp-1) == 0
                need(criterion == no_intersection, 'ordinary packed binary iff including top carries')
                expected = 2*logn-S.bit_count()-(Tp-1).bit_count()+(S+Tp-1).bit_count()
                need(r.bit_count() == expected, 'exact three-block popcount formula')
                count += 1
                accepted += criterion
    return dict(cases=count, accepted=accepted, n_powers_of_two_exponents=[1,8],
                valuation='v2 central binomial = popcount(r), so no binomial materialization is needed')


def full_normalization_checks():
    count = mask_pass = 0
    for B, L in ((4,2),(4,3),(8,2),(16,2)):
        q, theta = B**L, B-2
        la = (q*q-1)//(B-1)
        for ell in range(1, q):
            for b in sorted({1, B-3}):
                for e in sorted({1, q//2, q-1}):
                    for sigma in sorted({1, q//3, q//2, q-1}):
                        for g in sorted({1, q//2, q-1}):
                            S2 = ell+e*q
                            S = g+q*sigma+q*q*S2
                            Tp = q*q*theta*la+ell*(theta*q-b)
                            k, rb = divmod(b*ell, q)
                            j, u = divmod(theta*ell-k-1, q)
                            fields = ((g & (q-1-rb)) == 0 and (sigma & u) == 0
                                      and (S2 & (theta*la+j)) == 0)
                            combined = (S & (Tp-1)) == 0
                            need(fields == combined, 'all three normalized field tests exactly match')
                            if combined:
                                need(j == 0 and digit_is_binary(S2, B),
                                     'full packed test forces binary S2 before fixed code recovery')
                                mask_pass += 1
                            count += 1
    need(mask_pass > 0, 'full-field family includes accepted and rejected words')
    return dict(cases=count, accepted=mask_pass,
                scope='Finite arbitrary positive word fields; no compiler congruence is assumed')


def borrowed_mask_checks(layout):
    v0, M = min(layout['indicator']), layout['M']
    need(v0 == 8 and min(layout['D']) > M >= v0,
         'changed mask only touches product digits forced zero by divisibility')
    # sparse_digits handles huge exponent gaps without constructing giant powers.
    checks = 0
    for B in (64,128,256,512):
        positions = set(layout['indicator']) | set(range(v0))
        old_raw = {p:B-2 for p in layout['indicator']}
        new_raw = dict(old_raw)
        new_raw[0] = -1
        old_digits, _, _ = sparse_digits(old_raw, positions, B)
        new_digits, _, _ = sparse_digits(new_raw, positions, B)
        for p in positions:
            expected = B-1 if p < v0 else B-3 if p == v0 else old_digits[p]['digit']
            need(new_digits[p]['digit'] == expected, 'sparse borrow reaches exactly the first indicator')
            if p > v0:
                need(new_digits[p]['digit'] == old_digits[p]['digit'], 'all tested row masks unchanged')
            checks += 1
    numerical = 0
    for B in (4,8,16):
        # Toy indicator with the same positive least-degree shape; exhaustive
        # product words divisible by B^(v0+1), plus a bounded arbitrary high word.
        ell = B**2+B**4+B**5
        for high in range(4096):
            sigma = high*B**3
            need((sigma & ((B-2)*ell-1)) == (sigma & ((B-2)*ell)),
                 'borrowed and unborrowed masks have equal intersections on all allowed low-zero words')
            numerical += 1
    return dict(sparse_digit_comparisons=checks, numerical_intersection_comparisons=numerical,
                least_indicator=v0, minimum_D_exponent=str(min(layout['D'])),
                maximum_true_weight=str(M),
                exact_divisibility_reason='min support D > M >= v0, so B^(v0+1) divides D(B)*C^2 for every integer C')


def canonical_toy_packing():
    records = []
    for B in (16,32,64):
        H0 = B//2
        b, theta = B-H0-1, B-2
        L = 16
        q, n = B**L, B**(4*L)
        # A short compiler-shaped binary code with an isolated negative start,
        # a compensating reset, and product support above the first indicator.
        ell = B**2+B**8+B**9+B**10
        D = B**7-B**8+B**11
        e = ell+D
        need(digit_is_binary(ell,B) and digit_is_binary(e,B), 'toy fixed codes binary')
        # These are arithmetic mask words, not canonical represented solutions.
        # Use a divisible product word separately to test exact parity/packing;
        # the full compiler's canonical assignments are checked sparsely below.
        g, sigma = B**2, B**11
        S2 = ell+e*q
        S = g+q*sigma+q*q*S2
        la = (q*q-1)//(B-1)
        Tp = q*q*theta*la+ell*(theta*q-b)
        r = S*(n*n-n)+Tp*(n*n-1)
        need(0 < S < n and 0 < Tp < n and n <= r < 2*n**3,
             'narrow canonical-shaped packing and exact bounds')
        need(S % 2 == Tp % 2 == r % 2 == 0, 'even index required by fixed-plus half-parameter converse')
        need((S & (Tp-1)) == 0, 'all toy packed masks pass')
        need(r.bit_count() == 2*(n.bit_length()-1), 'central-binomial threshold attained exactly')
        records.append(dict(B=B, L=L, n_log2=n.bit_length()-1,
                            valuation=r.bit_count(), r_even=True))
    return records


def verify():
    layout = previous.make_layout()
    return dict(status='PASS',
        scope='Finite symbolic/sparse compiler and bounded packing regression; no exhaustive universality claim or giant full Pell tuple',
        unchanged_compiler=dict(symbolic=previous.symbolic_checks(layout), finite=previous.finite_checks(layout)),
        preliminary_bounds=preliminary_bounds(),
        spill_exclusion=spill_checks(),
        packed_binary=packed_binary_checks(),
        full_normalization=full_normalization_checks(),
        borrowed_mask=borrowed_mask_checks(layout),
        canonical_shaped_packing=canonical_toy_packing())


if __name__ == '__main__':
    receipt = verify()
    OUT.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(receipt['status'], 'spill cases', receipt['spill_exclusion']['cases'],
          'packed cases', receipt['packed_binary']['cases'])

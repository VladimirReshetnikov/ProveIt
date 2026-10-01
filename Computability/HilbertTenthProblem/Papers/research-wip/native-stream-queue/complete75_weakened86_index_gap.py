"""Necessary index-gap restrictions for the unresolved86 candidate.

No gate or witness of that candidate changes.  The new conclusions concern
R<0 with a positive computed input root; no universal86 bound is claimed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import complete75_weakened86_positive_index as parent

candidate = parent.candidate
pell = parent.pell


def source_contract():
    source = candidate.sources()[3]
    nodes = {name: (op, a, b) for name, op, a, b in source}
    critical = dict(c2=('*', 'R10a', 'R10a'), ic2=('*', 'i', 'c2'),
                    ic22=('*', 'ic2', 'ic2'), L16=('*', 'f', 'f'),
                    strong_difference=('*', 'A', 'ic22'),
                    norm_strong=('-', 'L16', 'strong_difference'),
                    R16=('*', 'A', 'strong_difference'))
    assert all(nodes[name] == row for name, row in critical.items())
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert counts == {'M': 48, 'A': 38}
    assert len(candidate.RETAINED) == 19
    return dict(polynomial_operations=len(source), operation_split=dict(counts),
                positive_witnesses=19, unchanged_exact_degree=203,
                source_sha256=hashlib.sha256(json.dumps(source, sort_keys=True).encode()).hexdigest(),
                normalized_strong_rows_checked=len(critical),
                source_changed=False)


def congruence_audit():
    rng = random.Random(861320)
    cases = negative_targets = zero_wraps = 0
    for case in range(512):
        B = rng.choice((16, 32, 64))
        J = rng.choice((1, 2, 7))
        q = (B-1)*J+1
        X, Y = rng.randrange(1, 5)*q**3, rng.randrange(1, 5)*q**3
        E, A, P = X*Y, Y*(X+1)+2, 2*X*Y*Y+1
        M = q*q-1
        p = rng.randrange(13, 50, 2)
        n = rng.randrange((p+1)//2, p)
        c, k = pell(A, p)[1], 2*pell(P, n)[1]
        small_pell = pell(2, p)[1]
        assert (k-2*n) % E == 0
        assert (c-small_pell) % Y == 0
        j = rng.choice((0, 1, 2*M-1, rng.randrange(2*M)))
        sign, epsilon, lam = (rng.choice((-1, 1)) for _ in range(3))
        R = sign*p-j*c-epsilon+lam
        difference = 2*n-sign*p-lam
        numerator = j*small_pell+difference
        # A candidate zero makes first_residual a multiple of E.
        # The following identity checks the resulting reduction modulo Y
        # without asserting that first_residual actually vanishes.
        first_residual = k-R-epsilon
        assert first_residual % Y == numerator % Y
        assert 0 <= difference < 3*p
        assert (difference == 0) == (sign == lam == 1 and p == 2*n-1)
        if R < 0:
            assert numerator > 0
            assert numerator <= (2*M-1)*small_pell+3*p-1
            if j == 0:
                assert sign == -1 and 0 < difference < 3*p
                assert first_residual % E == difference % E
                zero_wraps += 1
            negative_targets += 1
        cases += 1
    assert negative_targets and zero_wraps
    return dict(exact_modular_identity_cases=cases,
                negative_target_cases=negative_targets,
                zero_wrap_negative_target_cases=zero_wraps,
                scope='Exact Pell-recurrence and residue identities with a formal wrapped target; '
                      'the first-index residual, ratios and full candidate are not asserted zero.')


def growth_audit():
    parameter_cases = general_growth = gap_exclusions = 0
    for q in (16, 31, 46, 64, 256):
      for w in (1, 2, 9):
       X = w*q**3
       for s in (1, 5):
        Y = s*q**3
        A, P = Y*(X+1)+2, 2*X*Y*Y+1
        assert 2*A-1 > 2*Y*(X+1)
        assert 2*P < 4*Y*Y*(X+1)
        parameter_cases += 1
        for n in range(3, 13):
            k = 2*pell(P, n)[1]
            for p in range(n+1, 2*n):
                c = pell(A, p)[1]
                gap = 2*n-p
                # This exact lower ratio bound precedes any assumption
                # c<k*(Y+1); cross-multiplication keeps the audit integral.
                assert (1 << gap)*Y**(gap-1)*c > k*(X+1)**(p-n)
                if k*Y < c < k*(Y+1):
                    assert (1 << gap)*Y**(gap-1)*(Y+1) > (X+1)**(p-n)
                general_growth += 1
       for n in (7, 8, 12, 20, 33, 64):
            p = 2*n-1
            u = (2*q*q-3)*pell(2, p)[1]+3*p-1
            assert pell(2, p)[1] <= 4**(p-1) == 16**(n-1) <= q**(n-1)
            assert 6*n-3 <= q**(n-1)
            assert u+1 < 2*q**(n+1)
            assert (X+1)**(n-1) > 4*q**(n+1)
            # The low-modulus bound requires Y<=u, whereas the ratio
            # would require 2*(Y+1)>(X+1)^(n-1).  They cannot coexist.
            assert 2*(u+1) < (X+1)**(n-1)
            gap_exclusions += 1
    return dict(scale_parameter_cases=parameter_cases,
                exact_general_growth_cases=general_growth,
                uniform_gap_one_exclusion_cases=gap_exclusions,
                scope='Exact recurrence bounds and incompatible numerical intervals; '
                      'no complete candidate zero is asserted.')


def odd_index_and_zero_wrap_audit():
    odd_cases = even_exclusions = zero_wrap_cases = 0
    # The strong-rank and signed-step-down theorems supply p|m and
    # ell=+/-p modulo m.  Test their elementary parity consequence.
    for p in range(1, 65):
      for multiplier in range(1, 9):
        m = p*multiplier
        for sign in (-1, 1):
          for quotient in (1, 2, 5):
            ell = sign*p+quotient*m
            if ell <= 0:
                continue
            assert ell % p == 0
            if ell % 2:
                assert p % 2 == 1
                odd_cases += 1
            if p % 2 == 0:
                assert ell % 2 == 0
                even_exclusions += 1
    # These are index-lattice fixtures only.  Large p is required even
    # for zero wrap; actual Pell values at these indices are not formed.
    for q in (16, 31, 64, 76):
      for w, s in ((1, 1), (2, 3), (5, 2)):
        E = w*s*q**6
        target_multiple = E if E % 2 == 0 else 2*E
        for lam in (-1, 1):
            p = (2*target_multiple)//5
            p += 1-p % 2
            n = (target_multiple-p+lam)//2
            assert 2*n+p-lam == target_multiple
            assert n < p < 2*n and p % 2 == 1
            assert 0 < 2*n+p-lam < 3*p
            assert (2*n+p-lam) % E == 0 and E < 3*p
            zero_wrap_cases += 1
    return dict(odd_auxiliary_index_implication_cases=odd_cases,
                even_main_index_exclusions=even_exclusions,
                zero_wrap_index_lattice_cases=zero_wrap_cases,
                scope='Arithmetic consequences of the cited full strong-rank and step-down '
                      'hypotheses, plus index-lattice fixtures; no new rank theorem or candidate zero.')


def verify():
    return dict(status='PASS_SCOPED_WEAKENED86_INDEX_GAP',
                source=source_contract(), congruences=congruence_audit(),
                growth=growth_audit(), index_parity=odd_index_and_zero_wrap_audit(),
                global_necessary_condition='The main Pell index p is odd.',
                remaining_positive_root_branch='If R<0 and mu>0 then n<p<=2n-3, '
                    'Y<=(2*(q^2-1)-1)*psi_2(p)+3*p-1, and '
                    'j*psi_2(p)+2*n-s*p-lambda=0 modulo Y.',
                zero_wrap_condition='If also j=0 then s=-1 and E<3*p.',
                scope='Necessary restrictions only. The86-operation candidate remains unresolved '
                      'for R<0, including the remaining mu>0 cases and all mu<0 cases.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == json.loads(json.dumps(result)), 'receipt mismatch'
    print(result['status'])
    print(result['remaining_positive_root_branch'])
    print(result['scope'])

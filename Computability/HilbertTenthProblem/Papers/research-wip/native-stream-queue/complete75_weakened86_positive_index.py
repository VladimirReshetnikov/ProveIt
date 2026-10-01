"""Soundness of the unresolved86 candidate on its positive-index region.

The candidate circuit is unchanged. No universal86 bound is claimed.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import complete75_weakened_bound86_candidate as candidate

eliminated = candidate.eliminated


def original_factor_audit():
    original, _, pairs, source = candidate.sources()
    rng = random.Random(860101)
    negative_alpha = positive_index = negative_index = 0
    for case in range(512):
        signed = case >= 256
        values = {n: rng.randrange(-7, 8) if signed else rng.randrange(1, 8)
                  for n in candidate.RETAINED+['x']}
        if not signed:
            values['Z'] += values['alpha']
        B = rng.choice((16, 32, 64, 256))
        constants = dict(B=B, DC=3, DR=5, MC=B-2, MF=4,
                         cell_bits=B.bit_length()-1, inner_bits=3)
        env = eliminated.run(source, eliminated.fixed_inputs({**values, **constants}))
        X, Y, k, Delta = (env[n] for n in ('wn2', 'sn2', 'R10b', 'A'))
        restored = dict(q=env['q'], r=env['r_lhs'], W=env['W'],
                        tau=X*Y*Y*k+values['tau_gap'], ga=env['gamma_sum'],
                        phi=env['R10a']-env['index_rhs'], zquot=values['zplus']-1,
                        **{name: env[register] for name, register in eliminated.DEFINITIONS.items()})
        # This is the old101 slack, not the old87 slack alpha-Z.
        full = dict(values, **constants, **restored)
        full.update(alpha=values['F']+values['alpha'], i=Delta*values['i'])
        before = eliminated.run(original, eliminated.fixed_inputs(full))
        rr = [before[a]-before[b] for a, b in eliminated.baseline.prior.EQUALITIES]
        assert all(rr[i] == 0 for i in (0, 1, 3, 4, 6, 7, 9, 10, 15, 16, 18))
        U = values['j']*env['R10a']-env['r_lhs']
        V, y = env['aux_u_rhs'], values['y_aux']
        T2 = before['ic22']
        assert T2 == env['R16']
        assert rr[12] == Delta*(1-env['norm_strong'])
        expected = (1-rr[5], 1+rr[11], 1+rr[17],
                    1+rr[13]-T2*rr[14]*(U+V),
                    1+rr[8], 1+rr[2], env['norm_strong'], 1+rr[8]-rr[14])
        assert [env[n] for n in candidate.FACTOR_NAMES] == list(expected)
        product = 1
        for v in expected:
            product *= v
        assert env['polynomial'] == product-1
        assert env['W'] == env['marked_rhs']-values['Z']
        negative_alpha += values['alpha'] <= values['Z']
        positive_index += env['r_lhs'] > 0
        negative_index += env['r_lhs'] < 0
    pc = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert pc == {'M': 48, 'A': 38} and pairs == [('eight_units', 1)]
    return dict(complete_original19_factor_and_output_checks=512, signed_cases=256,
                nonpositive_old87_slack_cases=negative_alpha,
                positive_computed_index_cases=positive_index,
                negative_computed_index_cases=negative_index,
                polynomial_operations=len(source), operation_split=dict(pc),
                source_sha256=hashlib.sha256(json.dumps(source, sort_keys=True).encode()).hexdigest(),
                restored101_slack='F+alpha', restored_strong_coordinate='Delta*i')


def packing_audit():
    cases = boundaries = negative = weak_region = 0
    for B in (16, 32, 64, 128):
      for J in (1, 2, 5, 17):
       q = (B-1)*J+1
       M = q*q-1
       for MC in (2, B-2):
        for MF in (4, B-4):
         T = MC*J+1+q*(MF*J-1)
         assert 3*q+3 <= T < M
         for F in (1, 2, q//2, q-1):
          edge = q*q-q*F+1
          for Z in sorted({1, q, edge, edge+1, edge+2, 2*q*q}):
           S = Z+q*F-1
           G = q*q-Z-q*F
           R = G*M+(MC+q*(MF+B-1))*J
           assert R == (q*q-S)*M+T and R != 0
           assert (R > 0) == (S <= q*q)
           if R > 0:
            assert 1 <= Z <= q*q-q+1 < q*q
            assert 3*q+1 <= R-2 < R+2 < q**4
            assert q**6 > 2*(R+2)
            boundaries += S == q*q
            if S == q*q:
                assert G == -1 and R == T
            # The prior inverse alpha-Z can fail throughout this region.
            alpha = 1
            weak_region += alpha <= Z
           else:
            assert Z >= q*(q-F)+2 and Z > q-F
            negative += 1
           cases += 1
    assert boundaries and negative and weak_region
    # At the newly admitted boundary, the negative-index mask itself
    # must contradict the kernel's required population.
    mask_boundaries = 0
    for d in range(4, 9):
        B = 1 << d
        MC, MF = B-2, 4
        assert MC.bit_count()+MF.bit_count() == d
        for N in range(1, 5):
            q = B**N
            J = (q-1)//(B-1)
            minus = MC*J-1+q*(MF*J-1)
            assert 0 < minus < q*q-1 and minus.bit_count() == d*N+1
            assert minus.bit_count() < 3*d*N+2
            mask_boundaries += 1
    return dict(exact_untyped_packing_cases=cases, positive_boundary_cases=boundaries,
                negative_index_cases=negative, old_slack_inverse_fails_cases=weak_region,
                typed_negative_sign_boundary_cases=mask_boundaries,
                scope='Outer and mask fixtures, not full candidate zeros.')


def pell(A, n):
    return candidate.parent.pell(A, n)


def main_index_audit():
    residues = growth = input_branches = 0
    for A in range(6, 33):
        a, H = A-2, 4*A-5
        previous = 0
        for p in range(1, 49):
            D, c = pell(A, p)
            ep = D-a*c
            assert ep > previous
            previous = ep
            assert (ep-pow(2, p, H)) % H == 0
            X = ep % H
            assert 0 < X < H and (1 << p) >= X
            residues += 1
            if p >= 12:
                assert c > A*(A*A-1)**2 and c > 2*p
                growth += 1
            if p <= 3:
                continue
            gamma, rem = divmod(ep-X, H)
            assert rem == 0 and gamma > 1
            rho = gamma-1
            C = 1
            for v in (1, 2, p-1, p, p+1):
                mu, kappa = pell(A, v)
                for sign in (1, -1):
                    Z = C+rho*H-(sign*mu-a*kappa)
                    if Z <= 0:
                        continue
                    if sign > 0:
                        assert v < p and Z < 2*c
                    else:
                        assert Z == C+rho*H+mu+a*kappa
                        assert Z > a*kappa
                    input_branches += 1
    return dict(main_recurrence_and_least_residue_cases=residues,
                large_index_rank_size_cases=growth,
                signed_input_root_branch_cases=input_branches,
                scope='Exact recurrence/inequality fixtures; not full compiler or candidate zeros.')


def global_ratio_audit():
    """Check both forbidden Pell-index tails with exact recurrences."""
    endpoints = index_exclusions = duplication = 0
    for q in (16, 32, 64):
      for w in (1, 2, 5):
       for s in (1, 3):
        X, Y = w*q**3, s*q**3
        A, P = Y*(X+1)+2, 2*X*Y*Y+1
        doubled_parameter = 2*A*A-1
        assert P > A > Y+1 and doubled_parameter > P
        main = [pell(A, p)[1] for p in range(52)]
        for n in range(1, 25):
            k = 2*pell(P, n)[1]
            lower, upper = k*Y, k*(Y+1)
            assert main[n] < lower < upper < main[2*n]
            # This equality is checked from two separately evaluated
            # Pell recurrences, not used as a replacement for either.
            assert main[2*n] == 2*A*pell(doubled_parameter, n)[1]
            duplication += 1
            endpoints += 1
            for p in range(1, 2*n+4):
                if p <= n or p >= 2*n:
                    assert not lower < main[p] < upper
                    index_exclusions += 1
    return dict(exact_ratio_endpoint_cases=endpoints,
                independent_duplication_recurrence_cases=duplication,
                forbidden_main_index_cases=index_exclusions,
                conclusion='At a candidate zero the first/main indices obey n<p<2n, independently of R.',
                scope='Exact endpoint and exclusion fixtures; the two native norms are not jointly asserted zero.')


def strict_wrap_endpoint_audit():
    """Positive input-root fixtures with genuine main/input Pell values.

    These enforce the main scale, mask, main-root and signed input-root
    formulas.  They do not assert the first or auxiliary native norms,
    transport, or the full candidate polynomial is zero.
    """
    cases = endpoint_exclusions = input_index_cases = negative_indices = 0
    for t in (4, 5, 6):
        q = B = 1 << t
        M, J, F, C, x, b = q*q-1, 1, 1, 1, 1, 1
        MC, MF = B-2, 4
        alpha, u = q-F-C-2*t*x, 2*t*x+b
        assert alpha > 0 and MC.bit_count()+MF.bit_count() == t
        K = q*(q-F)*M+(MC+q*(MF+B-1))*J
        assert 0 < K < q**4
        for p in (3*t, 3*t+1, 3*t+5, 3*t+10):
          X = 1 << p
          assert X % q**3 == 0
          for s in (1, 2, 5):
            Y = s*q**3
            a = Y*(X+1)
            A, H = a+2, 4*a+3
            Delta = A*A-1
            D, c = pell(A, p)
            c_previous = pell(A, p-1)[1]
            ep = D-a*c
            assert D == A*c-c_previous and ep == 2*c-c_previous
            assert 0 < X < H and (ep-X) % H == 0
            gamma = (ep-X)//H
            assert gamma > 3 and c_previous > p
            for v in (1, 2, u, p-1):
              assert 0 < v < p
              mu, kappa = pell(A, v)
              ev = mu-a*kappa
              for sigma in (1, 2, 3):
                rho = gamma-sigma
                Z = C+rho*H-ev
                W = C-Z
                assert min(rho, sigma, Z, mu, kappa) > 0
                assert D == X+a*c+(rho+sigma)*H
                assert mu == W+a*kappa+rho*H
                assert D*D-Delta*c*c == mu*mu-Delta*kappa*kappa == 1
                assert 2*c-Z == c_previous+X+sigma*H+ev-C
                assert 2*c-Z > c_previous > p
                if v == u:
                    assert kappa > u and (kappa-u) % Delta == 0
                    input_index_cases += 1
                R = K-M*Z
                assert R == (q*(q-F)-Z)*M+(MC+q*(MF+B-1))*J
                negative_indices += R < 0
                for shift in (-2, 0, 2):
                    target = R+shift
                    assert target+2*M*c > p
                    assert 2*target < c
                    for sign in (-1, 1):
                        assert target != sign*p-2*M*c
                        endpoint_exclusions += 1
                cases += 1
    assert negative_indices == cases
    return dict(exact_positive_input_root_cases=cases,
                retained_input_index_congruence_cases=input_index_cases,
                negative_computed_index_cases=negative_indices,
                strict_forbidden_wrap_endpoint_checks=endpoint_exclusions,
                conclusion='For mu>0, p-2*(q^2-1)*c<R+epsilon-lambda<c/2; hence 0<=j<=2*(q^2-1)-1.',
                scope='Partial exact main/input-root and packing fixtures, not complete candidate zeros.')


def verify():
    return dict(status='PASS_SCOPED_WEAKENED86_POSITIVE_INDEX',
                source=original_factor_audit(), packing=packing_audit(),
                pell_branches=main_index_audit(),
                global_ratio=global_ratio_audit(),
                strict_wrap_endpoint=strict_wrap_endpoint_audit(),
                proved_region='Every positive candidate zero with computed R>0 has the correct ordinary input.',
                remaining_region='R<0; R=0 is impossible under the unchanged compiler mask bounds.',
                scope='The86-operation source is unchanged and remains an unresolved candidate. '
                      'The additional positive-index condition is not an uncharged universal bound. '
                      'Global main-index and input-root branch restrictions are necessary only.')


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
    print(result['proved_region'])
    print(result['remaining_region'])

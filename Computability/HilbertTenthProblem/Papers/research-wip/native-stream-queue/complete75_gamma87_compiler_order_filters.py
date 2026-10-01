"""Compiler parity and modular factor filters for the unresolved gamma87 source.

The exact half-binomial residue uses Lucas digit sums, without forming X,Y,H.
Packing fixtures are not compiled computation histories or false-input zeros.
"""
import argparse
from functools import lru_cache
from hashlib import sha256
from math import comb, gcd, isqrt
import json
from pathlib import Path
import random

import complete75_half_binomial_compiler as compiler


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p)+1))


def prime_divisors(n):
    factors, d = [], 2
    while d*d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


@lru_cache(None)
def field_tables(p):
    factorial = [1]*p
    for k in range(1, p):
        factorial[k] = factorial[k-1]*k % p
    inverse_factorial = [1]*p
    inverse_factorial[-1] = pow(factorial[-1], p-2, p)
    for k in range(p-1, 0, -1):
        inverse_factorial[k-1] = inverse_factorial[k]*k % p
    return tuple(factorial), tuple(inverse_factorial)


@lru_cache(None)
def weights(p, X, digit):
    """Prefix sums of binomial digit weights; fixed-p cache only."""
    factorial, inverse_factorial = field_tables(p)
    prefix, power = [0], 1
    for k in range(digit+1):
        coefficient = factorial[digit]*inverse_factorial[k]*inverse_factorial[digit-k] % p
        prefix.append((prefix[-1]+coefficient*power) % p)
        power = power*X % p
    return tuple(prefix)


def native_a_residue(R, p):
    assert R >= 3 and R % 2 and prime(p) and p % 2
    r = (R-1)//2
    n, threshold, digits = R-1, r, []
    while n or threshold:
        n, digit = divmod(n, p)
        threshold, bound = divmod(threshold, p)
        digits.append((digit, bound))
    X = pow(2, R, p)
    equal, greater = 1, 0
    for digit, bound in reversed(digits):
        sums = weights(p, X, digit)
        total = sums[-1]
        above = (total-sums[min(bound+1, len(sums)-1)]) % p
        exact = (sums[bound+1]-sums[bound]) % p if bound <= digit else 0
        greater, equal = (greater*total+equal*above) % p, equal*exact % p
    upper_tail = (equal+greater) % p
    value = upper_tail*pow(2, -1, p)*pow(X, -r, p)*(X+1) % p
    return value, len(digits)


def prime_order(ell):
    assert prime(ell) and ell > 2
    order = ell-1
    for p in prime_divisors(order):
        while order % p == 0 and pow(2, order//p, ell) == 1:
            order //= p
    assert pow(2, order, ell) == 1
    assert all(pow(2, order//p, ell) != 1 for p in prime_divisors(order))
    return order


def factor_certificate(R, trial_primes):
    """A squarefree lower divisor of gcd(2Delta,ord_H(2))."""
    assert R % 4 == 3
    factors, contributed, digit_work = [], {2}, 0
    for ell in trial_primes:
        residue, digits = native_a_residue(R, ell)
        digit_work += digits
        if (4*residue+3) % ell:
            continue
        order, hits = prime_order(ell), []
        for p in prime_divisors(order):
            if p == 2:
                contributed.add(2)
                continue
            a_p, digits = native_a_residue(R, p)
            digit_work += digits
            if ((a_p+2)**2-1) % p == 0:
                contributed.add(p)
                hits.append(dict(p=p, a_mod_p=a_p))
        factors.append(dict(prime_factor_of_H=ell, a_mod_ell=residue,
                            exact_order=order, discriminant_prime_hits=hits))
    lower = 1
    for p in sorted(contributed):
        lower *= p
    return dict(squarefree_lower_divisor=lower,
                ordinary_input_divisor_for_five_power_d=lower//gcd(lower, 10),
                proper_prime_certificates=factors,
                digit_stages=digit_work)


def direct_residue_checks():
    exact, modular, rng = 0, 0, random.Random(872031)
    primes = (3, 5, 7, 11, 17, 23, 31, 73, 103, 151)
    for R in range(3, 160, 4):
        r, X = (R-1)//2, 1 << R
        Y = sum(comb(2*r, r+j)*X**j for j in range(r+1))//2
        a = Y*(X+1)
        for p in primes:
            assert native_a_residue(R, p)[0] == a % p
            exact += 1
    for _ in range(256):
        R, p = 2*rng.randrange(2, 1000)+1, rng.choice(primes)
        r, X = (R-1)//2, pow(2, R, p)
        direct = sum(comb(2*r, r+j)*pow(X, j, p) for j in range(r+1))
        direct = direct*pow(2, -1, p)*(X+1) % p
        assert native_a_residue(R, p)[0] == direct
        modular += 1
    return dict(exact_integer_half_binomial_checks=exact,
                independent_direct_modular_tail_checks=modular)


def compiler_residue_checks():
    records, packings = [], 0
    for alphabet in range(2, 7):
        for k in range(2, 9):
            windows = [tuple((i//alphabet**j) % alphabet for j in range(9)) for i in range(k)]
            cc = compiler.compile_windows(windows, alphabet)
            assert cc.m % 2 == 0 and cc.d % 2 == cc.radix_bits % 2 == 1
            assert cc.anchor_unit == cc.m+6*alphabet-3 and cc.anchor_unit % 2 == 1
            assert cc.extra_dummy == k+12*alphabet
            MC = (pow(2, cc.d, 3)-1
                  -sum(pow(2, cc.radix_bits*e, 3) for e in cc.positions if e != 1)
                  -2*pow(2, cc.radix_bits*cc.extra_dummy, 3)) % 3
            MF = sum(value*pow(2, cc.radix_bits*e, 3)
                     for e, value in cc.MF_native_poly.items()) % 3
            predicted = 2 if k % 2 else 1 if alphabet % 2 == 0 else 0
            assert MF == 2 and MC == predicted
            records.append(dict(alphabet_size=alphabet, window_selectors=k,
                                MC_mod3=MC, MF_mod3=MF, odd_N_R_mod3=predicted,
                                fixed_cell_bits=cc.d))
    rng = random.Random(872032)
    for d in (5, 15, 25):
        B = 1 << d
        for N in range(1, 10):
            q, J = B**N, (B**N-1)//(B-1)
            for _ in range(16):
                # Numerical source identities do not require compiler masks.
                MC, MF = rng.randrange(1, B), rng.randrange(1, B)
                F, Z = rng.randrange(1, q), rng.randrange(1, q)
                R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
                assert R % J == 0
                assert R % 3 == (0 if N % 2 == 0 else (MC-MF-1) % 3)
                packings += 1
    return dict(actual_sparse_compiler_layouts=records,
                exact_packed_source_mod3_and_repunit_divisibility_checks=packings,
                universal_alphabet_instantiated=False)


def global_factor_checks():
    primes = (7, 23, 31, 47, 71, 73, 89, 103, 127, 151)
    # This larger example satisfies the packing/mask interfaces only.
    B, N, MC, MF, Z, F = 64, 1, 62, 4, 1, 20
    q, J = B**N, (B**N-1)//(B-1)
    R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
    assert R == 11531775 and R % 3 == 0
    assert 3*q+1 <= R < q**4 and R.bit_count() == 3*6+2
    assert MC.bit_count()+MF.bit_count() == 6 and MC % 4 == 2 and MF % 8 == 4
    low, high = MC*J+1, MF*J-1
    assert (Z-1) & low == F & high == 0
    cert = factor_certificate(R, primes)
    assert native_a_residue(R, 7)[0] == 1 and cert['squarefree_lower_divisor'] % 6 == 0
    # Here R divisible3 forces a divisible9, so the old local3 table has h=0.
    base = factor_certificate(7, primes)
    assert base['squarefree_lower_divisor'] % 17 == 0
    B17, N17, MC17, MF17, Z17, F17 = 32, 3, 26, 12, 1061, 17936
    q17, J17 = B17**N17, (B17**N17-1)//31
    R17 = ((q17*q17-Z17-q17*F17)*(q17*q17-1)
           +(MC17+q17*(MF17+B17-1))*J17)
    assert R17 == 521853468584832895 and R17 % 4 == 3
    assert (Z17-1) & (MC17*J17+1) == F17 & (MF17*J17-1) == 0
    assert R17.bit_count() == 3*15+2 and 3*q17+1 <= R17 < q17**4
    cert17 = factor_certificate(R17, (103,))
    assert cert17['squarefree_lower_divisor'] == 102
    assert cert17['ordinary_input_divisor_for_five_power_d'] == 51
    # Large exact packed integers audit the fast evaluator, not full histories.
    rng, records, nontrivial = random.Random(872033), [], 0
    for N in (1, 3, 5, 17, 125, 512):
        B, MC, MF = 32, 26, 12
        q, J, t = B**N, (B**N-1)//31, 5*N
        low, high = MC*J+1, MF*J-1
        for case in range(8):
            while True:
                F = rng.getrandbits(t) & ((q-1)^high)
                Z = 1+(rng.getrandbits(t) & ((q-1)^low))
                if F and Z < q:
                    break
            packed = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
            assert packed % 4 == 3 and 3*q+1 <= packed < q**4
            assert packed.bit_count() == 3*t+2 and packed % J == 0
            result = factor_certificate(packed, primes)
            nontrivial += result['squarefree_lower_divisor'] > 2
            records.append(dict(N=N, case=case, R_bits=packed.bit_length(),
                                R_sha256=sha256(packed.to_bytes((packed.bit_length()+7)//8, 'big')).hexdigest(),
                                certificate=result))
    return dict(nonlocal_three_example=dict(B=64, N=1, MC=62, MF=4, Z=1, F=20,
                                            R=R, certificate=cert,
                                            local_three_exponent=0, full_history=False),
                order17_component=dict(R=7, certificate=base, full_history=False),
                packed_order17_example=dict(B=B17, N=N17, MC=MC17, MF=MF17,
                                            Z=Z17, F=F17, R=R17, certificate=cert17,
                                            full_history=False),
                large_packing_audits=records, nontrivial_certificates=nontrivial,
                scope='Exact packed-mask and native-formula data only. Neither transport, ordinary input, nor a computation is supplied.')


def large_prime_power_bounds():
    cases = 0
    for ell in range(5, 1000, 2):
        if not prime(ell):
            continue
        powers = []
        for p in prime_divisors(ell-1):
            if p < 5:
                continue
            m = p
            while (ell-1) % m == 0:
                powers.append(m)
                m *= p
        for cofactor in range(3, 601, 6):
            H = ell*cofactor
            if (H-3) % 24:
                continue
            a = (H-3)//4
            for m in powers:
                for c in (1, 3):
                    if (a+c) % m:
                        continue
                    L = 4*m+1 if m % 3 == 1 else 2*m+1
                    N = (4*m-1 if m % 3 == 1 else 2*m-1) if c == 1 else 6*m-9
                    assert ell >= L and cofactor >= N and H >= L*N
                    cases += 1
    assert cases > 0
    return dict(prime_power_factor_pairs_checked=cases,
                scope='Admissible factor-pair implications, including order overestimates. No old complete-period sweep is repeated.')


def verify():
    return dict(status='PASS_GAMMA87_COMPILER_ORDER_FILTERS',
                modular_evaluator=direct_residue_checks(),
                actual_compiler=compiler_residue_checks(),
                factor_certificates=global_factor_checks(),
                excluded_large_prime_powers=large_prime_power_bounds(),
                complete_false_input_witness=False,
                established_universal_polynomial_bound=88,
                scope='Sharper genuine-compiler restrictions and certified period-gcd filters; gamma87 universality remains unresolved.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-receipt', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write_receipt:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])

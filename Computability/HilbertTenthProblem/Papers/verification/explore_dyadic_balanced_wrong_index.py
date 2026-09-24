#!/usr/bin/env python3
"""Dyadic wrong-index witnesses for the complete weakened 42-operation kernel.

The seven first/main equations are materialized. The enormous auxiliary Pell
coordinates are supplied by the proved exact-g CRT construction, not expanded.
No actual compiler packing, transport or false raw input is asserted.
"""
import argparse
import hashlib
import json
from math import comb, gcd, isqrt
from pathlib import Path

import explore_single_product_auxiliary_scale as dependency
from round37_1980_base_two_pell_regression import pell_power


def parameters(difference, degree):
    balance = 2 * difference**2 + 1
    quotient, remainder = divmod(balance, degree)
    assert difference > 0 and difference % 2 == 1
    assert degree > 1 and degree % 2 == 1 and remainder == 0
    r = degree + difference - 1
    p = degree + 2 * difference
    v = difference - 1 + quotient
    assert degree == 2*r+2-p and p-1 > r
    assert degree*v == p*(p-1-r)-(degree-1)
    return dict(difference=difference, degree=degree, quotient=quotient,
                r=r, p=p, J=2*r+1, Y_exponent=v)


def check_case(difference, degree, q):
    out = parameters(difference, degree)
    r, p, J, v = (out[name] for name in ('r', 'p', 'J', 'Y_exponent'))
    X, Y = 1 << p, 1 << v
    scale = q**3
    assert q >= 8 and q & (q-1) == 0
    assert q*q <= r < q**4 and r % 6 == 5
    assert X % scale == Y % scale == 0
    assert X > 4*p*Y
    # This exact bound implies Y*(1+(Y+2)/(XY))^(p-1) < Y+1.
    assert X*Y > (p-1)*(Y+2)*(Y+1)
    a = Y*(X+1)
    A = a+2
    Delta = A*A-1
    E = X*Y
    P = 2*X*Y*Y+1
    assert a > q**6 > J and E > r+1
    main_d, c = pell_power(A, p)
    first_d, k = pell_power(P, r+1)
    eta, zeta = c-Y*k, (Y+1)*k-c
    tau, tau_rem = divmod(first_d-1, 2)
    h, h_rem = divmod(k-r-1, E)
    gamma, gamma_rem = divmod(main_d-X-a*c, 4*a+3)
    assert min(eta, zeta, tau, h, gamma, X//scale, Y//scale) > 0
    assert tau_rem == h_rem == gamma_rem == 0
    residuals = [
        (E*E+X)*(Y*k)**2-tau*(tau+1),
        c-Y*k-eta,
        k-eta-zeta,
        k-r-1-h*E,
        a-E-Y,
        main_d-X-a*c-gamma*(4*a+3),
        main_d*main_d-1-Delta*c*c,
    ]
    assert residuals == [0]*7
    c_mod = dependency.pell_mod(A % p, p, p)[1]
    assert c_mod == c % p
    g = gcd(p, c)
    assert J % g == 0

    # Materialize all finite CRT precursor parameters, but not chi_R(s_aux)
    # or psi_R(s_aux). Their existence and signs use the published lemma.
    sigma = (-1)**((p-1)//2)
    modulus = c//g
    crt_t = (((-sigma*J-p)//g)*pow(4*p//g, -1, modulus)) % modulus
    if (-1)**crt_t != -sigma:
        crt_t += modulus
    aux_index = p+4*p*crt_t
    f = 2*main_d*main_d-1
    R = 2*Delta*c*main_d
    i = 4*Delta*Delta*main_d*main_d
    assert c % 2 == modulus % 2 == 1
    assert aux_index % 4 == p % 4 and (-1)**crt_t == -sigma
    assert (sigma*aux_index+J) % c == 0
    assert R*R == i*c*c == Delta*(f*f-1)
    assert R > f > 2*c > 2*J
    assert c > 2*p and R % (c*c) != 0
    binomial = comb(2*r, r)
    valuation = (binomial & -binomial).bit_length()-1
    threshold = scale.bit_length()-1
    assert valuation == r.bit_count() < threshold
    assert binomial % scale != 0
    out.update(q=q, scale=scale, r_mod_three=r % 3,
               X_bits=X.bit_length(), Y_bits=Y.bit_length(),
               c_bits=c.bit_length(), first_k_bits=k.bit_length(),
               A_mod_p=A % p, c_mod_p=c_mod, gcd_p_c=g,
               strict_ratio=True, seven_nonauxiliary_residuals=residuals,
               all_nonauxiliary_coordinates_positive=True,
               auxiliary_CRT_solvable=True, auxiliary_index_bits=aux_index.bit_length(),
               auxiliary_precursors_materialized=True,
               auxiliary_Pell_coordinates_materialized=False,
               all_ten_equations_supplied_by_proof=True,
               binomial_two_adic_valuation=valuation, required_valuation=threshold)
    return out


def check_rejected_case():
    out = parameters(31, 641)
    p, J, v = (out[name] for name in ('p', 'J', 'Y_exponent'))
    A_mod = (pow(2, v, p)*(pow(2, p, p)+1)+2) % p
    c_mod = dependency.pell_mod(A_mod, p, p)[1]
    g = gcd(p, c_mod)
    assert g == 37 and J % g == 11
    out.update(A_mod_p=A_mod, c_mod_p=c_mod, gcd_p_c=g,
               J_mod_g=J % g, auxiliary_CRT_solvable=False,
               scope='Excluded from this prescribed CRT family only')
    return out


def verify_parameter_identities():
    count = 0
    for difference in range(1, 102, 2):
        balance = 2*difference*difference+1
        divisors = set()
        for factor in range(1, isqrt(balance)+1):
            if balance % factor == 0:
                divisors.update((factor, balance//factor))
        for degree in sorted(divisors-{1}):
            parameters(difference, degree)
            count += 1
    return dict(cases=count, difference_range=[1,101],
                scope='All odd divisors greater than one in this bounded range; exponent identities only')


def dependency_hashes():
    here = Path(__file__).resolve().parent
    paths = [here/'explore_single_product_auxiliary_scale.py',
             here.parent/'1980'/'EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md',
             here/'round37_1980_base_two_pell_regression.py']
    return {str(path.relative_to(here.parent)).replace('\\', '/'):
            hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()
            for path in paths}


def verify():
    source = dependency.verify_source()
    assert source['kernel_operations'] == 42 and source['kernel_equations'] == 10
    return dict(status='PASS_DYADIC_WEAKENED42_KERNEL_COUNTEREXAMPLE',
                source=dict(kernel_operations=42, kernel_multiplications=24,
                            kernel_additions_subtractions=18, kernel_equations=10,
                            complete_candidate_operations=75,
                            source_unchanged_from_dependency=True),
                primary=check_case(59, 211, 16),
                secondary=check_case(35, 817, 16),
                smaller_q8_only=check_case(13, 113, 8),
                rejected_CRT_case=check_rejected_case(),
                parameter_identities=verify_parameter_identities(),
                dependencies=dependency_hashes(),
                dependency_hash_convention='SHA256 after CRLF-to-LF normalization',
                proof='../1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md',
                review='Author and two independent complete scoped proof/source reviews pass; fresh exact receipt checks pass',
                scope='Complete weakened42 kernel failure at q16 with odd r=2 modulo3, using a proved enormous auxiliary extension. No actual compiler packing, transport, raw-input witness, or full75 soundness conclusion.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    normalized = json.loads(json.dumps(result))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(normalized, indent=2)+'\n', encoding='utf-8')
    else:
        assert normalized == json.loads(path.read_text(encoding='utf-8'))
    print(result['status'])
    print({key: result['primary'][key] for key in ('q', 'r', 'p', 'J', 'Y_exponent', 'gcd_p_c')})

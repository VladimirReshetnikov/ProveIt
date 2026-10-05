#!/usr/bin/env python3
"""Independent finite checks for the fixed-prime carry theorem.

Fresh standard-library code only. Predecessor/author files are authenticated
and read as inert data; no supplied Python program is imported or executed.
The finite arithmetic below corroborates, but does not prove, the all-size
theorem challenged in the accompanying review.
"""
import argparse
import hashlib
import json
from math import comb, gcd, isqrt
from pathlib import Path

AUTHOR_PINS = {
    'complete83_fixed_prime_quotient_carries.md':
        '53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46',
    'complete83_fixed_prime_quotient_carries.py':
        '210506dc2ff70393a975d1768bea748a733f5f6c9b3b7790052c73336315912c',
    'complete83_fixed_prime_quotient_carries.json':
        '59ef0669c6708c820c67332667b288ac71c27d362e9793847dc7accd3d3b07d6',
}
DEPENDENCY_PINS = {
    'complete83_shared_projection_scout.json':
        'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
    'complete83_source_coupled_input_lifting.md':
        '822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
    'complete83_odd_primary_carry_budget.md':
        '4b884c4d9cc6fd7100c67b98caee4ec9f968653e7a03c3d41558dc0d5cbc5f95',
    'complete83_aggregate_input_budget.md':
        '803c6d47b503d611a641b456da3887a46a300c55023dfd1e2a7120de5299903f',
    'review_complete83_aggregate_input_budget.md':
        '00c080ae861b0cc176d070340119b031263ae3c6240cb3699d7b48f4d0954e32',
    'complete83_odd_prime_boundary.md':
        '59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da',
    'complete83_nondyadic_outer_family.md':
        '42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def vp(n, p):
    need(n != 0 and p > 1, 'valuation domain')
    n = abs(n)
    a = 0
    while n % p == 0:
        a += 1
        n //= p
    return a

def factors(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result

def carries(n, p):
    """Count literal grade-school carries when adding n+n in base p."""
    c = incoming = 0
    while n or incoming:
        digit = n % p
        n //= p
        incoming = (2*digit + incoming) // p
        c += incoming
    return c

def crt(equations):
    x, modulus = 0, 1
    for value, m in equations:
        need(gcd(modulus, m) == 1, 'CRT coprimality')
        x += modulus * (((value-x)*pow(modulus, -1, m)) % m)
        modulus *= m
    return x, modulus

def source_contract(packet_root):
    packet = json.loads((packet_root/'complete83_shared_projection_scout.json').read_bytes())['packet']
    rows = {row[0]: row for row in packet['source']}
    expected = [
        ['repunit', '*', 'Bm1', 'Jrep'], ['q', '+', 'repunit', 1],
        ['Lbig', '*', 'q', 'q'], ['q_minus_F', '-', 'q', 'F'],
        ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
        ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'],
        ['scaled_t', '*', 'twice_cell_bits', 'x'],
        ['marked_rhs', '-', 'C_after_alpha', 'scaled_t'],
        ['W', '-', 'marked_rhs', 'Z'],
        ['odd_index', '+', 'scaled_t', 'inner_bits'],
        ['gap_product', '*', 'repunit', 'q_minus_F'],
        ['gap', '+', 'gap_product', 'q_minus_FZ'],
        ['Lm1', '-', 'Lbig', 1], ['rproduct', '*', 'gap', 'Lm1'],
        ['qMF', '*', 'q', 'MF'], ['mask_factor', '+', 'MC', 'qMF'],
        ['mask', '*', 'mask_factor', 'Jrep'], ['r_lhs', '+', 'rproduct', 'mask'],
        ['kinner', '+', 'Kconstant', 'w'],
        ['innerC', '*', 'kinner', 'marked_rhs'],
        ['transport_partial', '+', 'innerC', 'q_minus_F'],
        ['local_rhs', '*', 'transport_quotient', 'repunit'],
        ['norm_transport', '-', 'transport_partial', 'local_rhs'],
    ]
    need(all(rows[r[0]] == r for r in expected), 'literal source interface')
    need(len(packet['source']) == 83 and packet['ordinary_input'] == 'x', 'unchanged full source')
    need(packet['ledger'] == {'A': 37, 'M': 46, 'total': 83}, 'source ledger')
    need(len(packet['free'])-len(packet['fixed_numerals'])-1 == 18, 'witness interface')
    names = ('q', 'K', 'z', 'd', 'x', 'b', 'MC', 'MF', 'J', 'w', 'h')
    zero = (0,)*len(names)
    def constant(n):
        return {zero: n} if n else {}
    def variable(name):
        exps = list(zero)
        exps[names.index(name)] = 1
        return {tuple(exps): 1}
    def plus(a, b, sign=1):
        result = dict(a)
        for e, c in b.items():
            result[e] = result.get(e, 0)+sign*c
            if not result[e]:
                del result[e]
        return result
    def times(a, b):
        result = {}
        for e, c in a.items():
            for f, d in b.items():
                key = tuple(i+j for i, j in zip(e, f))
                result[key] = result.get(key, 0)+c*d
        return {e: c for e, c in result.items() if c}
    V = {name: variable(name) for name in names}
    q, K, z = V['q'], V['K'], V['z']
    one = constant(1)
    scaled = times(constant(2), times(V['d'], V['x']))
    alpha = plus(plus(q, times(plus(K, constant(2)), z), -1), scaled, -1)
    env = {'q': q, 'repunit': plus(q, one, -1), 'F': times(K, z), 'Z': z,
           'alpha': alpha, 'twice_cell_bits': times(constant(2), V['d']),
           'x': V['x'], 'inner_bits': V['b'], 'MC': V['MC'], 'MF': V['MF'],
           'Jrep': V['J'], 'Kconstant': K, 'w': V['w'], 'transport_quotient': V['h']}
    # The literal q=repunit+1 row justifies the affine q cut. No quotient
    # relation or integer-valued witness is silently added to the source.
    for target, op, left, right in expected[2:]:
        a = constant(left) if isinstance(left, int) else env[left]
        b = constant(right) if isinstance(right, int) else env[right]
        env[target] = times(a, b) if op == '*' else plus(a, b, -1 if op == '-' else 1)
    q2 = times(q, q)
    qm = plus(q2, one, -1)
    a0 = plus(times(q2, qm), times(plus(V['MC'], times(q, V['MF'])), V['J']))
    g0 = times(plus(one, times(q, K)), qm)
    wanted = {'marked_rhs': z, 'W': {}, 'odd_index': plus(scaled, V['b']),
              'r_lhs': plus(a0, times(g0, z), -1),
              'norm_transport': plus(plus(times(V['w'], z), q),
                                     times(V['h'], plus(q, one, -1)), -1)}
    need(all(env[name] == value for name, value in wanted.items()), 'source polynomial identities')
    return {'literal_rows': len(expected), 'full_rows_guarded': 83,
            'retained_witnesses': 18, 'polynomial_term_counts': {k: len(v) for k, v in wanted.items()},
            'scope': 'Only the selected interface is independently expanded; no full source zero evaluated.'}

def forced_carries():
    checked = direct = 0
    signature = hashlib.sha256()
    for p in (3, 7, 11, 19, 31):
        for a in range(1, 4):
            for tau in range(8):
                b = a+tau
                e = max(1, 2*a-tau)
                need(e <= 2*a and b+e >= 3*a, 'exponent budget')
                for j in range(1, 5):
                    quotient = p**e*j-1
                    r = p**b*quotient-1
                    c = carries(r, p)
                    need(vp(r+1, p) == b, 'exact linear depth')
                    need(c == b+carries(quotient, p), 'carry decomposition')
                    need(c >= b+e >= 3*a, 'forced cube carries')
                    if r <= 2000:
                        need(vp(comb(2*r, r), p) == c, 'direct binomial check')
                        direct += 1
                    signature.update(f'{p},{a},{tau},{j},{c};'.encode())
                    checked += 1
    return {'cases': checked, 'direct_binomials': direct,
            'signature_sha256': signature.hexdigest(),
            'scope': 'Finite carry arithmetic, including tau>=2a; no compiler zeros.'}

def affine_crt_cases():
    checked = 0
    signature = hashlib.sha256()
    for factorization in ({3: 1, 7: 1, 11: 1}, {3: 2, 7: 2},
                          {3: 3, 11: 1}, {7: 1, 19: 2}):
        primes = sorted(factorization)
        A = 1
        for p, a in factorization.items():
            A *= p**a
        for mask in range(1, 1 << len(primes)):
            S = {p for i, p in enumerate(primes) if (mask >> i) & 1}
            for tau_seed in range(4):
                tau = {p: (tau_seed+i) % 4 for i, p in enumerate(primes)}
                powers = {p: p**(factorization[p]+tau[p]) for p in primes}
                Ag = 1
                for n in powers.values():
                    Ag *= n
                A_s = A_out = extra = 1
                for p, a in factorization.items():
                    if p in S:
                        A_s *= p**a
                        extra *= p**max(1, 2*a-tau[p])
                    else:
                        A_out *= p**a
                need(extra <= A_s*A_s, 'added modulus budget')
                m0, intercept, slope = 20, 2*A*A+8, 2*A+1
                equations = [(1, m0)]
                for p, a in factorization.items():
                    b = a+tau[p]
                    e = max(1, 2*a-tau[p]) if p in S else 0
                    modulus = p**(b+e)
                    target = -2*p**b if p in S else 0
                    z_residue = (intercept+1-target)*pow(slope, -1, modulus)
                    equations.append((z_residue % modulus, modulus))
                z0, step = crt(equations)
                if z0 == 0:
                    z0 = step
                need(step == m0*Ag*extra, 'combined CRT step')
                length = isqrt(3*A_out)+1
                chosen = None
                for j in range(length):
                    z = z0+step*j
                    R = intercept-slope*z
                    need(R % 2 == 1 and (R+1) % (2*Ag) == 0, 'odd affine quotient')
                    eta = (R+1)//(2*Ag)
                    if gcd(eta, A_out) == 1:
                        chosen = (j, z, R)
                        break
                need(chosen is not None, 'outside-S coprime interval')
                j, z, R = chosen
                need(0 < z <= step*length, 'positive representative bound')
                for p, a in factorization.items():
                    b = a+tau[p]
                    need(vp(R+1, p) == b, 'CRT exact depths')
                    if p in S:
                        e = max(1, 2*a-tau[p])
                        need(((R+1)//(2*p**b)+1) % p**e == 0, 'CRT quotient tail')
                signature.update(f'{A},{sorted(S)},{tau_seed},{j},{z},{R};'.encode())
                checked += 1
    return {'cases': checked, 'signature_sha256': signature.hexdigest(),
            'scope': 'Synthetic affine congruences; R may be signed; no positivity claim.'}

def larger_input_residues():
    cases = residues = roots = 0
    signature = hashlib.sha256()
    for p, base_ell in ((3, 2), (7, 3)):
        for a in (1, 2):
            for tau in (0, 1):
                b = a+tau
                ell = base_ell*p**(b-1)
                need(vp(pow(2, ell)-1, p) == b, 'base exponential valuation')
                for h in range(1, 2*a+1):
                    modulus = p**h
                    wide = p**(b+h)
                    u0, R = ell, ell*(modulus+2)
                    image = []
                    for k in range(modulus):
                        diff = (pow(2, R, wide)-pow(2, u0+ell*k, wide)) % wide
                        need(diff % p**b == 0, 'normalization integral')
                        image.append(diff//p**b)
                    need(len(set(image)) == modulus, 'input residue bijection')
                    # A separate exact-linear-depth r gives the local simple root.
                    r = p**b*(p+1)-1
                    eta = p+1
                    polynomial = lambda y: eta*(r+2)+r*(r+2)*y+r*(r-1)*p**b*y*y
                    root_residues = [y for y in range(modulus) if polynomial(y) % modulus == 0]
                    need(len(root_residues) == 1 and root_residues[0] % p != 0, 'unit simple root')
                    k = image.index(root_residues[0])
                    need(polynomial(image[k]) % modulus == 0, 'composed source-coupled root')
                    signature.update(f'{p},{a},{tau},{h},{k};'.encode())
                    cases += 1
                    residues += modulus
                    roots += 1
    return {'maps': cases, 'enumerated_residues': residues, 'local_roots': roots,
            'max_h_over_a': 2, 'signature_sha256': signature.hexdigest(),
            'scope': 'Residue lemma beyond the older h<=a range; not full source zeros.'}

def subsequence_checks():
    cases = 0
    records = []
    for d in (5, 25):
        B = 1 << d
        need((B+1)**2 > 12*d*d and B*B > 12*d*(d+1), 'uniform fixed-base margins')
        plus_S = factors(B+1)
        for j in range(3):
            n = 3**(2*j)
            D, A = d*n, (1 << (d*n))+1
            A_s = 1
            for p in plus_S:
                A_s *= p**vp(A, p)
            need(A_s == (B+1)*n, 'plus fixed-prime part')
            ell = 2*D*(D-1)
            need(A_s*A_s > 6*ell and n % 4 == 1, 'plus margin/subsequence')
            records.append({'shape': 'plus', 'd': d, 'n': n, 'A_s': A_s,
                            'ell': ell, 'S': sorted(plus_S)})
            cases += 1
        minus_S = factors(2*B-1)
        # The first nontrivial d=25 admissible m is enormous. Check its
        # congruence/subsequence algebra without constructing 2^(d*n).
        order = 1
        while pow(9, order, d) != 1:
            order += 1
        for j in (0, order):
            m = 9**j
            need(m % d == 1, 'minus selected m')
            n = ((d+1)*m-1)//d
            D = d*n
            A_s = (2*B-1)*m
            ell = 2*D*(D+1)
            need(n % 4 == 1 and D+1 == (d+1)*m, 'minus index algebra')
            need(A_s > B*n and A_s*A_s > 6*ell, 'minus margin')
            if D < 3000:
                A = (1 << (D+1))-1
                exact = 1
                for p in minus_S:
                    exact *= p**vp(A, p)
                need(exact == A_s, 'minus fixed-prime part')
            records.append({'shape': 'minus', 'd': d, 'm': m, 'n': n,
                            'A_s': A_s, 'ell': ell, 'S': sorted(minus_S),
                            'A_materialized': D < 3000})
            cases += 1
    return {'cases': cases, 'records': records,
            'scope': 'Small numeral cases and symbolic subsequence arithmetic, not compiler instances.'}

def make(args):
    pins = {}
    for name, expected in {**DEPENDENCY_PINS, **AUTHOR_PINS}.items():
        path = args.packet_root/name
        data = path.read_bytes()
        need(sha(data) == expected, 'pin mismatch: ' + name)
        pins[name] = {'sha256': expected, 'bytes': len(data)}
    author = json.loads((args.packet_root/'complete83_fixed_prime_quotient_carries.json').read_bytes())
    need(author['source_sha256'] == AUTHOR_PINS['complete83_fixed_prime_quotient_carries.py'],
         'author source binding')
    need({x['name']: x['sha256'] for x in author['dependencies']} == DEPENDENCY_PINS,
         'author dependency map')
    need(all(x['bytes'] == pins[x['name']]['bytes'] for x in author['dependencies']),
         'author dependency byte sizes')
    need(author['scope']['binary_condition_for_enlarged_z_proved'] is False
         and author['scope']['complete_positive_source_zeros'] == 0,
         'author scope boundary')
    return {'source_sha256': sha(Path(__file__).read_bytes()),
            'pins': pins, 'source_contract': source_contract(args.packet_root),
            'forced_carry_checks': forced_carries(),
            'affine_crt_checks': affine_crt_cases(),
            'larger_input_residue_checks': larger_input_residues(),
            'subsequence_checks': subsequence_checks(),
            'scope': {'author_or_predecessor_code_executed': False,
                      'binary_population_proved': False,
                      'full_actual_compiler_zero_exhibited': False}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet-root', type=Path, default=Path('/tmp'))
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = make(args)
    encoded = (json.dumps(result, indent=2, sort_keys=True)+'\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(encoded)
    else:
        need(args.expect.read_bytes() == encoded, 'receipt differs')
    print('PASS: independent finite carry, CRT, larger-input and subsequence checks.')

if __name__ == '__main__':
    main()

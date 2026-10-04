#!/usr/bin/env python3
"""Fresh finite evidence for a conditional, unchanged-source input-lifting theorem.

Predecessors are authenticated and read only as bytes/JSON. No imported helper,
source DAG evaluation, full Pell tuple, or actual compiler instance is executed.
Synthetic family constants below test arithmetic, not language membership.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

DEFAULT_ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS = {
    'complete83_nondyadic_outer_family.md': '42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
    'complete83_nondyadic_outer_family.json': '8041d3661c0cfc9c29ca25c99d08567e45a2ceed3dbca29caf22b792a8c97dd1',
    'complete83_odd_prime_boundary.md': '59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da',
    'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
    'complete83_shared_projection_math.md': '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
    'complete83_even_radix_boundary.md': 'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc',
    'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def factor(n):
    require(n > 0, 'factor domain')
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def vp(n, p):
    require(n != 0, 'valuation of zero')
    n = abs(n)
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def factorial_vp(n, p):
    v = 0
    while n:
        n //= p
        v += n
    return v


def central_vp(r, p):
    return factorial_vp(2*r, p) - 2*factorial_vp(r, p)


def crt(pairs):
    x, modulus = 0, 1
    for value, new_mod in pairs:
        require(math.gcd(modulus, new_mod) == 1, 'CRT coprimality')
        x += modulus * ((value-x)*pow(modulus, -1, new_mod) % new_mod)
        modulus *= new_mod
    return x, modulus


def bind_source(root):
    data = {}
    for name, expected in PINS.items():
        raw = (root/name).read_bytes()
        require(sha(raw) == expected, 'changed predecessor: '+name)
        data[name] = raw
    packet = json.loads(data['complete83_shared_projection_scout.json'])['packet']
    rows = {row[0]: row for row in packet['source']}
    # Literal source bindings, independently specified. No source is executed.
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
        ['mask', '*', 'mask_factor', 'Jrep'],
        ['r_lhs', '+', 'rproduct', 'mask'],
        ['kinner', '+', 'Kconstant', 'w'],
        ['innerC', '*', 'kinner', 'marked_rhs'],
        ['transport_partial', '+', 'innerC', 'q_minus_F'],
        ['local_rhs', '*', 'transport_quotient', 'repunit'],
        ['norm_transport', '-', 'transport_partial', 'local_rhs'],
    ]
    for row in expected:
        require(rows[row[0]] == row, 'literal row '+row[0])
    require(packet['ordinary_input'] == 'x', 'input port')
    require(len(packet['witnesses']) == 18, 'witness interface')
    return {'pins': PINS, 'literal_outer_rows': expected,
            'ordinary_input': 'x', 'positive_witnesses': 18,
            'scope': 'inert row authentication; no full DAG evaluation'}


def interval_checks():
    count = 0
    for A in range(3, 1500, 2):
        if A % 5 == 0:
            continue
        fs = factor(A)
        phi = A
        for p in fs:
            phi = phi // p * (p-1)
        L = math.isqrt(3*A)+1
        require(3*phi*phi >= A*4**len(fs), 'Euler product bound')
        require(L*phi > A*2**len(fs), 'strict interval margin')
        for slope in (1, 2, 7, 11):
            if math.gcd(slope, A) != 1:
                continue
            for eta in (0, 1, A//2, A-1):
                hits = [j for j in range(L) if math.gcd(eta-slope*j, A) == 1]
                require(hits, 'coprime affine interval')
                require(abs(len(hits)*A-L*phi) < A*2**len(fs), 'inclusion exclusion error')
                count += 1
    return {'cases': count, 'odd_A_below': 1500, 'five_excluded': True}


def carry_and_binary_checks():
    carry_cases, direct_binom_cases, binary_cases = 0, 0, 0
    for p in (3, 5, 7, 11, 13):
        for depth in (1, 2, 3):
            for h in range(1, 22):
                if h % p == 0:
                    continue
                r = p**depth*h-1
                left = central_vp(r, p)
                right = depth + central_vp(h, p)
                require(left == right, 'exact low carry decomposition')
                if r <= 1500:
                    require(vp(math.comb(2*r, r), p) == right, 'direct binomial carries')
                    direct_binom_cases += 1
                carry_cases += 1
    for r in range(25, 1000, 2):
        j, ell, e = vp(r+1, 2), vp(r+3, 2), vp(r-1, 2)
        u = max(j, ell)+2
        c = r.bit_count()
        X = 1 << u
        C = [math.comb(2*r, r+h) for h in range(4)]
        weighted = [vp(C[h], 2)+h*u for h in range(4)]
        require(weighted == [c, c+u-j, c+2*u+e-j, c+3*u+e-j-ell], 'four term valuations')
        require(vp(sum(C[h]*X**h for h in range(4)), 2) == c, 'binary dominance')
        binary_cases += 1
    return {'carry_cases': carry_cases, 'direct_binomial_cases': direct_binom_cases,
            'binary_four_term_cases': binary_cases}


def root_digits(poly, p, h):
    root, modulus = 0, 1
    for _ in range(h):
        candidates = [root+j*modulus for j in range(p)
                      if poly(root+j*modulus) % (modulus*p) == 0]
        require(len(candidates) == 1, 'unique linear Hensel root')
        root, modulus = candidates[0], modulus*p
    return root


def normalized_x(R, u0, ell, p, depth, k, h):
    mod = p**(depth+h)
    residue = (pow(2, R, mod)-pow(2, u0+ell*k, mod)) % mod
    require(residue % p**depth == 0, 'integral normalized X')
    return residue // p**depth


def inverse_input(R, u0, ell, p, depth, target, h):
    k, modulus = 0, 1
    for level in range(1, h+1):
        candidates = [k+j*modulus for j in range(p)
                      if normalized_x(R, u0, ell, p, depth, k+j*modulus, level)
                      == target % (modulus*p)]
        require(len(candidates) == 1, 'unique actual input lift')
        k, modulus = candidates[0], modulus*p
    return k


def local_lift_checks():
    count, residues, exact_values = 0, 0, 0
    for p in (3, 5, 7, 11):
        for depth in (1, 2):
            ell = (p-1)*p**(depth-1)
            require(vp(2**ell-1, p) == depth, 'diagnostic period depth')
            for eta in (2, 4, 8):
                if eta % p == 0:
                    continue
                r = p**depth*eta-1
                R = 2*r+1
                u0 = R % ell
                poly = lambda y: eta*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y
                for h in (1, 2):
                    vals = [normalized_x(R, u0, ell, p, depth, k, h)
                            for k in range(p**h)]
                    require(len(set(vals)) == p**h, 'residue permutation')
                    residues += len(vals)
                    root = root_digits(poly, p, h)
                    k = inverse_input(R, u0, ell, p, depth, root, h)
                    require(poly(vals[k]) % p**h == 0, 'composed local root')
                    require(root % p == eta % p != 0, 'unit root')
                    # Independent direct integer formula on a bounded subrange.
                    if u0+ell*k < 3000 and R < 3000:
                        X = (1 << R)-(1 << (u0+ell*k))
                        require(X % p**depth == 0, 'direct integer normalization')
                        require(poly(X//p**depth) % p**h == 0, 'direct composed root')
                        exact_values += 1
                    count += 1
    return {'local_lifts': count, 'permutation_residues': residues,
            'direct_integer_checks': exact_values,
            'scope': 'signed exponential algebra; not positive full-source zeros'}


def composed_crt_check():
    # A deliberately small algebra example exercises two nontrivial deficient
    # primes with one common positive X. It supplies no compiler masks/ports.
    r, R, u0, ell, A, q = 251, 503, 5, 6, 21, 42
    reqs, detail = [], []
    for p, depth in ((3, 2), (7, 1)):
        require(vp(r+1, p) == depth, 'CRT diagnostic tie')
        require(vp(2**ell-1, p) == depth, 'CRT diagnostic period')
        c = vp(math.comb(2*r, r), p)
        require(c == 2, 'two carries at each deficient prime')
        eta = (r+1)//p**depth
        poly = lambda y: eta*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y
        root = root_digits(poly, p, 1)
        k = inverse_input(R, u0, ell, p, depth, root, 1)
        reqs.append((k, p))
        detail.append({'p': p, 'depth': depth, 'central': c,
                       'normalized_root': root, 'input_residue': k})
    k, modulus = crt(reqs)
    require(k == 12 and modulus == A, 'nontrivial simultaneous CRT input')
    u = u0+ell*k
    require(u == 77 and u < R, 'positive common exponential difference')
    X = (1 << R)-(1 << u)
    require(X % q == 0, 'local example radix divides X')
    full_modulus = 2*q**3
    full_residue = sum(math.comb(2*r, r+j)*pow(X, j, full_modulus)
                       for j in range(r+1)) % full_modulus
    require(full_residue == 0, 'full finite half-binomial modular sum')
    return {'r': r, 'R': R, 'q': q, 'ell': ell, 'u0': u0,
            'A': A, 'input_k': k, 'u': u, 'prime_data': detail,
            'full_M_mod_2q3': full_residue,
            'scope': 'local two-prime algebra example; no compiler constants or full source zero'}


def family_cases():
    results = []
    for d in (5, 25):
        n, b, MC = 1, 5, 2
        D, B = d*n, 1 << d
        Q = B**n
        MF = B+3
        for K in (2, 3, 7, 8):
            plus = K % 5 != 3
            q = Q*(Q+1)//2 if plus else Q*(2*Q-1)
            A = Q+1 if plus else 2*Q-1
            t = D-1 if plus else D
            T = n*(D-1 if plus else D+1)
            ell, m0 = 2*d*T, 4*d if plus else 4*d//5
            J = (q-1)//(B-1)
            require((B-1)*J+1 == q, 'family repunit')
            A0 = q*q*(q*q-1)+(MC+q*MF)*J
            G0 = (1+q*K)*(q*q-1)
            modulus = d if plus else d//5
            if plus:
                zmod = (A0-b)*pow(G0, -1, modulus) % modulus
            elif modulus > 1:
                zmod = ((A0-b)//5)*pow(G0//5, -1, modulus) % modulus
            else:
                zmod = 0
            zclass, period = crt([(1, 4), (zmod, modulus)])
            require(period == m0, 'original z class')
            fs = factor(A)
            taus = {p: vp(D-1 if plus else D, p) for p in fs}
            g = math.prod(p**taus[p] for p in fs)
            zres = (A0+1)*pow(G0, -1, A*g) % (A*g)
            z0, zperiod = crt([(zclass, m0), (zres, A*g)])
            if z0 == 0:
                z0 = zperiod
            L = math.isqrt(3*A)+1
            z = next(z0+zperiod*j for j in range(L)
                     if math.gcd((A0-G0*(z0+zperiod*j)+1)//(2*A*g), A) == 1)
            R = A0-G0*z
            require(R % 4 == 3 and (R-b) % (2*d) == 0, 'index residue')
            require(z <= m0*A*g*L, 'small exact-depth representative')
            x0 = 5*n+((R-b)//(2*d)-5*n) % T
            u0 = 2*d*x0+b
            require((R-u0) % ell == 0, 'source input period')
            threshold = (K+2)*m0*A*g*L+2*d*(5*n+T*A)+1 < q
            if R <= 0:
                # Small diagnostic parameters need not meet the all-size threshold.
                results.append({'d': d, 'K': K, 'shape': 'plus' if plus else 'minus',
                                'threshold': threshold, 'positive_R': False,
                                'scope': 'synthetic congruence test only'})
                require(not threshold, 'threshold implies positive R')
                continue
            r = (R-1)//2
            reqs, signatures = [], []
            budget = True
            for p, a in fs.items():
                depth = a+taus[p]
                require(vp(r+1, p) == depth, 'forced exact linear tie')
                require(pow(2, ell, p**depth) == 1, 'period valuation lower')
                require(pow(2, ell, p**(depth+1)) != 1, 'period valuation upper')
                c = central_vp(r, p)
                sig = {'p': p, 'a': a, 'tau': taus[p], 'depth': depth, 'central': c}
                if c < 2*a:
                    budget = False
                elif c < 3*a:
                    h = 3*a-c
                    eta = (r+1)//p**depth
                    poly = lambda y: eta*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y
                    target = root_digits(poly, p, h)
                    k = inverse_input(R, u0, ell, p, depth, target, h)
                    reqs.append((k, p**h))
                    sig.update({'required_depth': h, 'input_residue': k})
                signatures.append(sig)
            k, Hreq = crt(reqs)
            require(Hreq <= A, 'CRT input budget')
            if budget:
                for sig in signatures:
                    p, a, depth, c = (sig[z] for z in ('p', 'a', 'depth', 'central'))
                    if c < 3*a:
                        h = 3*a-c
                        eta = (r+1)//p**depth
                        y = normalized_x(R, u0, ell, p, depth, k, h)
                        val = eta*(r+2)+r*(r+2)*y+r*(r-1)*p**depth*y*y
                        require(val % p**h == 0, 'simultaneous source-coupled roots')
            if threshold:
                require(q-(K+2)*z-2*d*(x0+(A-1)*T) > 0, 'entire positive input interval')
                require(3*q+1 < R < q**4-q**3, 'index bounds')
                require(R+5 < q**4 < 2**(8*D+4), 'binary denominator bound')
                require(u0 >= 10*D+b, 'binary input margin')
                require(vp(r+1, 2) < u0 and vp(r+3, 2) < u0, 'binary separation')
                for kk in (0, k, A-1):
                    u = u0+ell*kk
                    mod = q*(q-1)
                    require((pow(2, R, mod)-pow(2, u, mod)) % mod == 0, 'full source transport period')
            results.append({'d': d, 'K': K, 'shape': 'plus' if plus else 'minus',
                            'q': q, 'A': A, 'g': g, 'z': z, 'R': R,
                            'x0': x0, 'input_lift_k': k, 'Hreq': Hreq,
                            'threshold': threshold, 'odd_carry_budget': budget,
                            'binary_population_condition': R.bit_count() >= 3*t+2,
                            'prime_signatures': signatures,
                            'scope': 'synthetic fixed numerals; not an actual compiler instance'})
    return results


def build(root):
    return {'source_sha256': sha(Path(__file__).read_bytes()),
            'source_binding': bind_source(root),
            'affine_interval': interval_checks(),
            'carry_and_binary': carry_and_binary_checks(),
            'local_lifts': local_lift_checks(),
            'composed_crt': composed_crt_check(),
            'synthetic_family_cases': family_cases(),
            'scope': {
                'actual_compiler_zero_exhibited': False,
                'predecessor_programs_executed': False,
                'conditional_odd_carry_hypothesis': 'v_p(binomial(2r,r)) >= 2*v_p(A)',
                'conditional_binary_hypothesis': 'popcount(R) >= 3*v2(q)+2',
                'source_changed': False,
                'new_universal_operation_bound': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    raw = (json.dumps(build(args.root), sort_keys=True, indent=2)+'\n').encode()
    if args.output:
        with args.output.open('xb') as handle:
            handle.write(raw)
    else:
        require(raw == args.expect.read_bytes(), 'receipt mismatch')
    print('PASS: source-coupled conditional input lifting; no actual compiler zero evaluated')


if __name__ == '__main__':
    main()

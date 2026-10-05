#!/usr/bin/env python3
"""Fresh bounded corroboration; all frozen dependencies are inert bytes only."""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

PINS = {
    'complete83_source_coupled_input_lifting.md': '822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
    'complete83_aggregate_input_budget.md': '803c6d47b503d611a641b456da3887a46a300c55023dfd1e2a7120de5299903f',
    'review_complete83_aggregate_input_budget.md': '00c080ae861b0cc176d070340119b031263ae3c6240cb3699d7b48f4d0954e32',
    'complete83_odd_primary_carry_budget.md': '4b884c4d9cc6fd7100c67b98caee4ec9f968653e7a03c3d41558dc0d5cbc5f95',
    'complete83_odd_prime_boundary.md': '59fb701504a8cab48a4c29b8167ffe459c049feed00dc6a821003747e8a856da',
    'complete83_nondyadic_outer_family.md': '42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
    'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
}


def ck(test, message):
    if not test:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':')).encode()


def vp(n, p):
    ck(n != 0, 'valuation of zero')
    n, v = abs(n), 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def factor(n):
    result, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def central(n, p):
    def factorial_v(m):
        v = 0
        while m:
            m //= p
            v += m
        return v
    return factorial_v(2*n) - 2*factorial_v(n)


def crt(classes):
    x, modulus = 0, 1
    for residue, q in classes:
        ck(math.gcd(modulus, q) == 1, 'noncoprime CRT moduli')
        x += modulus * ((residue - x) * pow(modulus, -1, q) % q)
        modulus *= q
        x %= modulus
    return x, modulus


def source_guard(raw):
    packet = json.loads(raw)['packet']
    rows = packet['source']
    ck(len(rows) == 83, 'complete source count')
    d = {row[0]: row for row in rows}
    wanted = [
        ['repunit', '*', 'Bm1', 'Jrep'], ['q', '+', 'repunit', 1],
        ['Lbig', '*', 'q', 'q'], ['q_minus_F', '-', 'q', 'F'],
        ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
        ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'],
        ['scaled_t', '*', 'twice_cell_bits', 'x'],
        ['marked_rhs', '-', 'C_after_alpha', 'scaled_t'],
        ['W', '-', 'marked_rhs', 'Z'], ['odd_index', '+', 'scaled_t', 'inner_bits'],
        ['gap_product', '*', 'repunit', 'q_minus_F'],
        ['gap', '+', 'gap_product', 'q_minus_FZ'], ['Lm1', '-', 'Lbig', 1],
        ['rproduct', '*', 'gap', 'Lm1'], ['qMF', '*', 'q', 'MF'],
        ['mask_factor', '+', 'MC', 'qMF'], ['mask', '*', 'mask_factor', 'Jrep'],
        ['r_lhs', '+', 'rproduct', 'mask'], ['kinner', '+', 'Kconstant', 'w'],
        ['innerC', '*', 'kinner', 'marked_rhs'],
        ['transport_partial', '+', 'innerC', 'q_minus_F'],
        ['local_rhs', '*', 'transport_quotient', 'repunit'],
        ['norm_transport', '-', 'transport_partial', 'local_rhs'],
    ]
    ck(all(d.get(row[0]) == row for row in wanted), 'literal source binding')
    return {'complete_rows': len(rows), 'literal_rows': wanted, 'array_executed': False}


def subsequences():
    records = []
    for d in (1, 5, 25):
        B = 2**d
        for shape in ('plus', 'minus'):
            fixed = B+1 if shape == 'plus' else 2*B-1
            primes = factor(fixed)
            ck(3 in primes and 5 not in primes, 'fixed support')
            phi = 1 if d == 1 else 4*d//5
            for j in range(1, 9):
                m = 9**(phi*j)
                n = 9**j if shape == 'plus' else ((d+1)*m-1)//d
                D = d*n
                ck(n % 4 == 1, 'subsequence parity')
                if shape == 'minus':
                    ck(m % d == 1 % d and D+1 == (d+1)*m, 'minus subsequence')
                As = 1
                vals = {}
                for p, a0 in primes.items():
                    a = a0 + vp(n if shape == 'plus' else m, p)
                    mod = p**(a+1)
                    residue = (pow(B, n, mod)+1) % mod if shape == 'plus' else (pow(2, D+1, mod)-1) % mod
                    ck(residue % p**a == 0 and residue != 0, 'exact LTE valuation')
                    As *= p**a
                    vals[str(p)] = a
                ck(As == fixed*(n if shape == 'plus' else m), 'exact S-part')
                ck(As <= (2*B-1)*n, 'S-part upper bound')
                if shape == 'plus' or d >= 5:
                    ck(B*n < As, 'S-part lower bound')
                ell = 2*D*(D-1 if shape == 'plus' else D+1)
                if d >= 5:
                    ck(As*As > 6*ell, 'aggregate gain')
                records.append({'d': d, 'shape': shape, 'j': j, 'n': n, 'valuations': vals})
    return {'cases': len(records), 'actual_compiler_instances': 0,
            'scope': 'exact LTE and subsequence arithmetic; d=1,5 include relaxed compiler bounds',
            'records_sha256': digest(encoded(records))}


def forcing_cases():
    records, prime_checks, carry_checks = [], 0, 0
    primes = (3, 7, 11)
    for aset in itertools.product((1, 2), repeat=3):
        A = math.prod(p**a for p, a in zip(primes, aset))
        for case in range(12):
            tau = tuple((case+2*i) % 5 for i in range(3))
            chosen = {p for i, p in enumerate(primes) if (case >> i) & 1}
            if not chosen:
                chosen = {3}
            bs = tuple(a+t for a, t in zip(aset, tau))
            es = {p: max(1, 2*a-t) for p, a, t in zip(primes, aset, tau) if p in chosen}
            As = math.prod(p**a for p, a in zip(primes, aset) if p in chosen)
            Aout = A//As
            extra = math.prod(p**e for p, e in es.items())
            g = math.prod(p**t for p, t in zip(primes, tau))
            m0 = 4 if case % 2 == 0 else 20
            modulus = m0*A*g*extra
            length = math.isqrt(3*Aout)+1
            q, K = 16*A, case+1
            G0 = (1+q*K)*(q*q-1)
            A0 = 2+2*G0*modulus*length
            classes = [(1, m0)]
            for p, b in zip(primes, bs):
                mod = p**(b+es[p]) if p in chosen else p**b
                target = -2*p**b if p in chosen else 0
                classes.append(((A0+1-target)*pow(G0, -1, mod) % mod, mod))
            z0, got = crt(classes)
            ck(got == modulus, 'CRT budget')
            z0 = z0 or modulus
            eta0 = (A0-G0*z0+1)//(2*A*g)
            slope = G0*m0*extra//2
            ck(math.gcd(slope, Aout) == 1, 'outside unit slope')
            js = [j for j in range(length) if math.gcd(eta0-slope*j, Aout) == 1]
            ck(bool(js), 'coprime interval existence')
            j = js[0]
            z = z0+modulus*j
            R, r = A0-G0*z, (A0-G0*z-1)//2
            ck(0 < z <= modulus*length and r > 0 and R % 4 == 3, 'synthetic positivity and parity')
            H = 1
            vals = []
            for p, a, b in zip(primes, aset, bs):
                ck(vp(r+1, p) == b, 'all exact depths')
                eta = (r+1)//p**b
                c = central(r, p)
                ck(c == b+central(eta, p), 'carry identity')
                if p in chosen:
                    ck((eta+1) % p**es[p] == 0, 'forced quotient residue')
                    ck(c >= 3*a, 'forced complete carry')
                    carry_checks += 1
                else:
                    ck(c >= a, 'outside baseline carry')
                H *= p**max(3*a-c, 0)
                vals.append([p, a, b, c])
                prime_checks += 1
            ck(extra <= As*As and H <= Aout*Aout, 'gain and remaining CRT bound')
            records.append({'A': A, 'S': sorted(chosen), 'tau': tau, 'extra': extra,
                            'Lout': length, 'j': j, 'valuations': vals, 'Hreq': H})
    return {'cases': len(records), 'exact_depth_checks': prime_checks,
            'forced_S_carry_checks': carry_checks, 'actual_source_instances': 0,
            'scope': 'synthetic affine CRT models; positive A0 chosen independently of source masks',
            'records_sha256': digest(encoded(records))}


def scalar_checks():
    cases = 0
    for d in range(5, 201):
        B = 2**d
        ck(B*B > 12*d*(d+1), 'uniform scalar bound')
        for n in range(1, 102, 4):
            for sign in (-1, 1):
                ell = 2*d*n*(d*n+sign)
                ck(ell <= 2*d*(d+1)*n*n < B*B*n*n//6, 'ell bound')
                cases += 1
    # Pure endpoint check: strict ell*H<S0 makes all CRT residues positive.
    endpoints = 0
    for ell in range(1, 25):
        for H in range(1, 49):
            for margin in (1, 2, 13):
                S0 = ell*H+margin
                ck(S0-ell*(H-1) > 0, 'last residue positive')
                ck(H <= (S0+ell-1)//ell, 'full interval count')
                endpoints += 1
    return {'scalar_cases': cases, 'positive_endpoint_cases': endpoints}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--write', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    dependencies, blobs = [], {}
    for name, pin in PINS.items():
        raw = (args.root/name).read_bytes()
        ck(digest(raw) == pin, 'dependency pin '+name)
        blobs[name] = raw
        dependencies.append({'name': name, 'bytes': len(raw), 'sha256': pin})
    result = {'schema': 'fixed finite-prime quotient carries v1', 'status': 'PASS',
              'source_sha256': digest(Path(__file__).read_bytes()), 'dependencies': dependencies,
              'source_guard': source_guard(blobs['complete83_shared_projection_scout.json']),
              'subsequences': subsequences(), 'forcing': forcing_cases(),
              'scalar': scalar_checks(),
              'scope': {'unconditional_odd_scale_theorem': True,
                        'binary_condition_for_enlarged_z_proved': False,
                        'actual_compiler_examples_evaluated': 0,
                        'complete_positive_source_zeros': 0,
                        'predecessor_execution': False,
                        'new_circuit_or_gate_saving': False}}
    data = (json.dumps(result, sort_keys=True, indent=2)+'\n').encode()
    if args.write:
        args.write.write_bytes(data)
    if args.expect:
        ck(args.expect.read_bytes() == data, 'exact receipt replay')
    print(json.dumps({'status': 'PASS', 'receipt_sha256': digest(data),
                      'LTE_cases': result['subsequences']['cases'],
                      'forcing_cases': result['forcing']['cases']}, sort_keys=True))


if __name__ == '__main__':
    main()

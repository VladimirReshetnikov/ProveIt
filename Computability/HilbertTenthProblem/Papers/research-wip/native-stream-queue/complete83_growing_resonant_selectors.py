#!/usr/bin/env python3
"""Fresh bounded arithmetic for growing resonant selectors; predecessors inert."""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

PINS = {
 'complete83_fixed_prime_quotient_carries.md': '53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46',
 'complete83_subpower_selector_bound.md': '3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4',
 'complete83_source_coupled_input_lifting.md': '822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f',
 'complete83_nondyadic_outer_family.md': '42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23',
 'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
}

def require(ok, message):
    if not ok:
        raise ArithmeticError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def valuation(n, p):
    require(n != 0, 'zero valuation')
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent

def length(n):
    if n == 1:
        return 1
    primes = []
    rest, candidate = n, 2
    while candidate*candidate <= rest:
        if rest % candidate == 0:
            primes.append(candidate)
            while rest % candidate == 0:
                rest //= candidate
        candidate += 1
    if rest > 1:
        primes.append(rest)
    phi = n
    for p in primes:
        phi = phi//p*(p-1)
    return (2**len(primes)*n)//phi+1

def residue_checks():
    records = []
    for d in (5, 25):
        B, m = 2**d, 2**d-1
        for n in (1, 5, 9):
            Q = B**n
            rep = (Q-1)//m
            for MC in (2, B-4, B-2):
                mask = m-MC
                for shape in ('plus', 'minus'):
                    if shape == 'plus':
                        q, A, K = Q*(Q+1)//2, Q+1, 2
                        zA = 1+(m-MC//2)*rep
                        require(zA == Q-(MC//2)*rep and 1 < zA < Q, 'plus representative')
                    else:
                        q, A, K = Q*(2*Q-1), 2*Q-1, 8
                        zA = 2*mask*rep
                        require(0 < zA < 2*(Q-1), 'minus representative')
                    require((q-1) % m == 0 and gcd(m, A) == 1, 'source repunit and inverse')
                    J, MF = (q-1)//m, m+4
                    A0 = q*q*(q*q-1)+(MC+q*MF)*J
                    G0 = (1+q*K)*(q*q-1)
                    require(0 < zA < A and (m*zA+mask) % A == 0, 'canonical residue')
                    require((A0-G0*zA+1) % A == 0, 'actual affine packing at residue')
                    for h in (0, 1, 3, 50):
                        z = zA+A*h
                        require((A0-G0*z+1) % A == 0, 'resonant progression')
                    records.append([d,n,MC,shape,zA])
    return {'cases': len(records), 'records_sha256': sha(json.dumps(records).encode()),
            'scope': 'Relaxed fixed numerals satisfy the stated mask bounds; not actual compiler instances or full positive source zeros.'}

def shifted_interval_checks():
    cases, endpoints = 0, 0
    chosen_last = 0
    for N in (1, 3, 7, 9, 11, 21, 27, 33, 49, 63, 77, 99):
        L = length(N)
        for alpha in range(-N, N+1):
            for beta in range(1, min(N+1, 13)):
                if gcd(beta, N) != 1:
                    continue
                found = [j for j in range(1, L+1) if gcd(alpha+beta*j, N) == 1]
                require(found, 'shifted coprime interval')
                chosen_last += found[0] == L
                cases += 1
    for A in (3, 7, 15, 33):
        for zA in range(1, A):
            for M_over_A in (1, 4, 20, 63):
                M = A*M_over_A
                for h0 in (0, M_over_A-1):
                    z0 = zA+A*h0
                    require(0 < z0 <= M, 'initial representative')
                    for L in (1, 2, 7):
                        for j in (1, L):
                            z = z0+M*j
                            h = (z-zA)//A
                            require(z > M and z <= M*(L+1) <= 2*M*L, 'doubled bound')
                            require(h >= M_over_A and h < 2*M_over_A*L, 'quotient bounds')
                            endpoints += 1
    return {'coprime_cases': cases, 'first_valid_at_last_endpoint': chosen_last,
            'selector_endpoint_cases': endpoints,
            'scope': 'Finite affine interval and representative arithmetic only.'}

def three_adic_growth():
    records = []
    for d in (5, 25, 125):
        B = 2**d
        for shape in ('plus', 'minus'):
            base = B+1 if shape == 'plus' else 2*B-1
            a0 = valuation(base, 3)
            for index in range(1, 4):
                if shape == 'plus':
                    n = 9**index
                    exponent = d*n
                    a = a0+valuation(n, 3)
                    tau = valuation(exponent-1, 3)
                    mod = 3**(a+1)
                    remainder = (pow(2, exponent, mod)+1) % mod
                    scale = n
                else:
                    v = 9**((4*d//5)*index)
                    require(v % d == 1, 'minus congruence subsequence')
                    n = ((d+1)*v-1)//d
                    exponent = d*n+1
                    a = a0+valuation(v, 3)
                    tau = valuation(exponent-1, 3)
                    mod = 3**(a+1)
                    remainder = (pow(2, exponent, mod)-1) % mod
                    require((d+1)*v >= d*n, 'minus comparison')
                    scale = v
                require(tau == 0 and remainder != 0 and remainder % 3**a == 0, 'exact three-adic depth')
                e = max(1, 2*a-tau)
                require(e == 2*a and 3**e >= 9*scale*scale, 'extra modulus lower bound')
                require(3**e*(d+1)**2 >= 9*d*d*n*n, 'uniform quadratic lower bound')
                records.append({'d': d, 'shape': shape, 'index': index,
                                'n': n, 'a3': a, 'tau3': tau, 'e3': e})
    return {'cases': len(records), 'records': records,
            'scope': 'Exact modular LTE corroboration; Q, X, Y and Pell coordinates not materialized.'}

def build(root):
    data = {}
    deps = []
    for name, pin in PINS.items():
        raw = (root/name).read_bytes()
        require(sha(raw) == pin, 'dependency '+name)
        data[name] = raw
        deps.append({'name': name, 'sha256': pin, 'bytes': len(raw)})
    packet = json.loads(data['complete83_shared_projection_scout.json'])['packet']
    rows = {r[0]: r for r in packet['source']}
    wanted = [
      ['repunit','*','Bm1','Jrep'], ['q','+','repunit',1],
      ['Lbig','*','q','q'], ['q_minus_F','-','q','F'],
      ['q_minus_FZ','-','q_minus_F','Z'], ['gap_product','*','repunit','q_minus_F'],
      ['gap','+','gap_product','q_minus_FZ'], ['Lm1','-','Lbig',1],
      ['rproduct','*','gap','Lm1'], ['qMF','*','q','MF'],
      ['mask_factor','+','MC','qMF'], ['mask','*','mask_factor','Jrep'],
      ['r_lhs','+','rproduct','mask']]
    require(len(rows) == 83 and all(rows[r[0]] == r for r in wanted), 'literal source interface')
    return {'source_sha256': sha(Path(__file__).read_bytes()), 'dependencies': deps,
            'source_guard': {'full_rows': 83, 'literal_rows': wanted, 'array_evaluated': False},
            'residues': residue_checks(), 'shifted_search': shifted_interval_checks(),
            'three_adic_growth': three_adic_growth(),
            'scope': {'binary_population_proved': False, 'complete_compiler_zero_exhibited': False,
                      'source_changed': False, 'predecessor_programs_executed': False}}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root)
    raw = (json.dumps(result, indent=2, sort_keys=True)+'\n').encode()
    if args.output:
        with args.output.open('xb') as stream:
            stream.write(raw)
    else:
        require(args.expect.read_bytes() == raw, 'receipt differs')
    print('PASS: exact selector residues, shifted search and three-adic growth; no source zeros evaluated.')

if __name__ == '__main__':
    main()

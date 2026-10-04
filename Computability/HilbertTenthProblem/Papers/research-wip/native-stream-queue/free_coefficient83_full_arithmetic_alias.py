#!/usr/bin/env python3
"""Exact outer data and rational graph checks for a proof-defined positive zero.

The diagnostic constants are not a valid fixed-program recipe. The enormous
Pell witnesses are defined by the accompanying proof, never materialized.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

PINS = {
    'complete83_free_coefficient_scout.json': '682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
    'complete83_free_coefficient_scout.md': '867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
    'free_coefficient83_native_alias.md': '542775d7ff0ccd84f5fe94c32d6c396ad45a8cc033dd1cbd37ed72dedd40f96f',
    'first_index_scaled_obstruction.md': 'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
    '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
CASE = dict(d=9, N=3, b=5, B=512, q=134217728, J=262657,
            t=9159759548913079, MC=374, MF0=292, K=135578,
            F=64816286, Z=17584025, x=1)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def pell_mod(A, n, modulus):
    delta = (A*A-1) % modulus
    result, base = (1, 0), (A % modulus, 1)
    def multiply(x, y):
        return ((x[0]*y[0]+delta*x[1]*y[1]) % modulus,
                (x[0]*y[1]+x[1]*y[0]) % modulus)
    while n:
        if n & 1:
            result = multiply(result, base)
        base = multiply(base, base)
        n //= 2
    return result


def parameter_modulus(p, t, modulus):
    return (pow(2, p+t+1, modulus)+pow(2, t+1, modulus)+2) % modulus


def outer_case():
    z = CASE.copy()
    d, N, b, B, q, J, t = (z[k] for k in ('d', 'N', 'b', 'B', 'q', 'J', 't'))
    MC, MF0, K, F, Z, x = (z[k] for k in ('MC', 'MF0', 'K', 'F', 'Z', 'x'))
    require(B == 2**d and q == B**N and J*(B-1) == q-1, 'power/repunit')
    require(t >= 11 and t % 2 == 1, 'scaled family parameter')
    p, n = t*(t+2), t*(t+1)
    R = 2*n-1
    require(p % 4 == 3 and R % 4 == 3 and R-p == t*t-1 > 0, 'wrong index')
    require(p >= d*N and t+1 >= 3*d*N, 'positive dyadic scale quotients')
    require(0 < MC < B-1 and 0 < MF0 < B-1, 'necessary mask ranges')
    require(MC % 4 == 2 and MF0 % 8 == 4, 'necessary low mask bits')
    require(MC.bit_count()+MF0.bit_count() == d, 'necessary mask populations')
    MF = MF0+B-1
    G = q*q-q*F-Z
    packed = G*(q*q-1)+(MC+q*MF)*J
    require(packed == R and F > 0 and Z > 0 and F+Z < q, 'literal packing')
    require((2*q-1)*(q*q-1) < R < q**4-q**3, 'positive packing interval')
    u = 2*d*x+b
    W = 2**u
    C = Z+W
    alpha = q-F-2*Z-2*d*x-W
    require(0 < u < p and u % 2 == 1 and alpha > 0, 'input lift and slack')
    require(0 < K < B*B and 0 < C < q and 0 < W < q, 'outer bounds')
    wm = pow(2, p-d*N, q-1)
    require(((K+wm)*C+q-F-1) % (q-1) == 0, 'transport divisibility')
    cm = pell_mod(parameter_modulus(p, t, p), p, p)[1]
    gcd_cp = math.gcd(cm, p)
    require((R-p) % gcd_cp == 0, 'auxiliary CRT compatibility')
    modulus = 4*p
    cm4 = pell_mod(parameter_modulus(p, t, modulus), p, modulus)[1]
    g = math.gcd(cm4, modulus)
    require(g == gcd_cp and (p-R) % g == 0, 'odd c CRT modulus')
    reduced = modulus//g
    crt_j = ((p-R)//g)*pow(cm4//g, -1, reduced) % reduced
    require((R+cm4*crt_j) % modulus == p and crt_j >= 0, 'exact CRT coefficient')
    require(d % b != 0, 'explicit failure of B=(2^b)^L for integral L')
    power5 = 1
    while power5 < d:
        power5 *= 5
    require(power5 != d, 'explicit failure of the powers-of-five width recipe')
    z.update(p=p, n=n, R=R, MF=MF, G=G, u=u, W=W, C=C, alpha=alpha,
             w_mod_repunit=wm, c_mod_p=cm, gcd_c_p=gcd_cp,
             c_mod_4p=cm4, auxiliary_CRT_coefficient=crt_j,
             auxiliary_index_definition='v=R+c*auxiliary_CRT_coefficient',
             X_exponent=p, Y_exponent=t+1,
             w_exponent=p-d*N, s_exponent=t+1-3*d*N,
             c_bit_length_strict_lower_bound=p*(p-1),
             full_positive_zero='Proved by the Pell/CRT construction; huge witnesses not materialized',
             valid_fixed_program_recipe=False)
    return z


def execute(packet, assignment):
    require(set(assignment) == set(packet['free']), 'exact complete free-port assignment')
    env = dict(assignment)
    for name, op, a, b in packet['source']:
        require(name not in env and op in ('+', '-', '*'), 'acyclic literal row')
        x = env[a] if isinstance(a, str) else Fraction(a)
        y = env[b] if isinstance(b, str) else Fraction(b)
        env[name] = x+y if op == '+' else x-y if op == '-' else x*y
    return env


def rational_graph_checks(packet):
    results = []
    for seed in range(1, 17):
        B, J, w, s = 8, 1+seed, 2+seed, 1+seed % 3
        q = (B-1)*J+1
        X, Y = w*q, s*q**3
        E, a = X*Y, Y*(X+1)
        Delta, H = (a+1)*(a+3), 4*a+3
        k, c, D, tau = 7+seed, (7+seed)*Y+3, 2+7*seed, 1+3*seed
        F, Z, x, K, MC, MF = 1+seed, 2+seed, seed+1, seed+2, 2, 4
        R = (q*q-q*F-Z)*(q*q-1)+(MC+q*MF)*J
        W, kap, mu = 2+seed, 5+seed, 7+seed
        C, u = Z+W, 6*x+1
        rho = Fraction(mu-a*kap-W, H)
        gamma = Fraction(D-a*c-X, H)
        f, S, V, y = 2+seed, 3+seed, 5+2*seed, 4+seed
        supplied = dict(Bm1=B-1, MC=MC, MF=MF, Kconstant=K,
                        twice_cell_bits=6, inner_bits=1, x=x,
                        tau_root=tau, Jrep=J, w=w, s=s,
                        eta=c-k*Y, zeta=k-(c-k*Y), rho=rho, sigma=gamma-rho,
                        alpha=q-F-2*Z-6*x-W, delta=Fraction(kap-u, Delta),
                        y_aux=y, h=Fraction(k-R-1, E), F=F, Z=Z,
                        transport_quotient=Fraction((K+w)*C+q-F-1, q-1),
                        f=f, auxiliary_quotient=Fraction(V+c+R*f*f, c*f),
                        aux_coefficient_root=S)
        env = execute(packet, {name: Fraction(value) for name, value in supplied.items()})
        cuts = dict(wn2=X, sn2=Y, UM=E, R10b=k, R10a=c, R12=a,
                    a4m5=H, A=Delta, R14=D, W=W, marked_rhs=C,
                    odd_index=u, index_rhs=kap, exponent_rhs=mu,
                    r_lhs=R, aux_u_rhs=V, norm_index=1, norm_transport=1)
        require(all(env[name] == value for name, value in cuts.items()), 'triangular graph cut identities')
        factors = [tau*tau-X*Y*Y*(X*Y*Y+1)*k*k, D*D-Delta*c*c,
                   mu*mu-Delta*kap*kap, S*S*V*V-(S*S-1)*y*y,
                   1, 1, Delta*f*f-S*S]
        require([env[name] for name in packet['factors']] == factors, 'all seven literal factors')
        expected = math.prod(factors)-Delta
        require(env[packet['output']] == expected, 'complete rational output identity')
        results.append(dict(seed=seed, cuts=len(cuts), factors=[str(v) for v in factors],
                            output=str(expected), positive_zero=False))
    return dict(cases=results, complete_gate_evaluations=len(results)*len(packet['source']),
                cut_value_checks=sum(r['cuts'] for r in results),
                scope='Off-zero signed/rational graph identities, not the huge positive witness or compiler instances')


def verify(root):
    for name, pin in PINS.items():
        require(digest((root/name).read_bytes()) == pin, 'dependency pin '+name)
    packet = json.loads((root/'complete83_free_coefficient_scout.json').read_text())['packet']
    require(len(packet['source']) == 83 and len(packet['witnesses']) == 18,
            'literal complete 83 interface')
    require(packet['factors'] == ['norm_first', 'norm_main', 'norm_input', 'norm_aux',
                                 'norm_index', 'norm_transport', 'norm_strong'], 'factor order')
    return dict(status='PASS', source_sha256=digest(Path(__file__).read_bytes()),
                dependency_pins=PINS, outer_case=outer_case(),
                rational_graph_checks=rational_graph_checks(packet),
                scope='Full positive zero on diagnostic fixed numerals, proved parametrically; no false accepted input on a valid fixed-program slice',
                universal_soundness='UNPROVED', new_polynomial_emitted=False,
                enormous_witnesses_materialized=False)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--output', type=Path)
    g.add_argument('--expect', type=Path)
    args = ap.parse_args()
    result = verify(args.root)
    if args.expect:
        require(exact(result, json.loads(args.expect.read_text())), 'type-exact saved receipt')
    if args.output:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', actual_source_gates=83,
                          graph_checks=len(result['rational_graph_checks']['cases']),
                          valid_fixed_program_recipe=False,
                          enormous_witnesses_materialized=False)))


if __name__ == '__main__':
    main()

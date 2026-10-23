#!/usr/bin/env python3
"""Finite independent transcription check; imports no generator or prior auditor."""
import gzip
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIME = 1000000007


def literal(v):
    J, F, alpha, z, f, h, i, T, s, w, tau, eta, zeta, y, gamma = (
        v[n] for n in ['J', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 's', 'w', 'tau', 'eta', 'zeta', 'y', 'gamma'])
    beta, K0, MC, MF = (v[n] for n in ['beta', 'K0', 'MC', 'MF'])
    q = beta * J + 1
    C = q - F - alpha
    X, Y = w * q, s * q**3
    E, k = X * Y, eta + zeta
    c = k * Y + eta
    a = E + Y
    H = 4 * a + 3
    Delta = a * a + H
    D = X + a * c + gamma * H
    R = ((q - 1) * (q - F) + alpha) * (q*q - 1) + (MC + q * MF) * J
    V = c * (T * f - 1) - R * f*f
    I, Kaux = i * c*c, Delta * (f*f - 1)
    N0 = tau*tau - (X * Y*Y) * (X * Y*Y + 1) * k*k
    N1 = D*D - Delta * c*c
    Na = Kaux * (V*V - y*y) + y*y
    Nk = k - h * E - R
    Nt = (K0 + w) * C + q - F - z * (q - 1)
    S = I*I - Kaux
    return {'p72_relaxed': [(N0*N1-1)**2 + (Na*Nk*Nt-1)**2 + S*S],
            'p74_relaxed': [(N0-1)**2 + (Na-1)**2 + S*S + (N1*Nk*Nt-1)**2],
            'relaxed15_system61': [N0-1, N1-1, Na-1, Nk-1, Nt-1, S]}


def evaluate(c, v):
    env = dict(v)
    for name, op, x, y in c['source']:
        x = env[x] if isinstance(x, str) else x
        y = env[y] if isinstance(y, str) else y
        env[name] = (x+y if op == '+' else x-y if op == '-' else x*y) % PRIME
    if 'output' in c:
        return [env[c['output']]]
    return [((env[x] if isinstance(x, str) else x) -
             (env[y] if isinstance(y, str) else y)) % PRIME for x, y in c['comparisons']]


def main():
    circuits = {n: json.loads((HERE / (n + '.json')).read_text())
                for n in ['p72_relaxed', 'p74_relaxed', 'relaxed15_system61']}
    actual = {p: int.from_bytes(gzip.decompress((HERE / 'coefficients' / (n + '.bin.gz')).read_bytes()), 'little') % PRIME
              for p, n in {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}.items()}
    rng = random.Random(72080)
    comparisons = 0
    for j in range(500):
        v = {n: rng.randrange(-20, 21) for n in circuits['p72_relaxed']['witnesses']}
        v.update(actual if j % 2 else {n: rng.randrange(-20, 21) for n in actual})
        expected = literal(v)
        for name, c in circuits.items():
            got = evaluate(c, v)
            if got != [x % PRIME for x in expected[name]]:
                raise AssertionError((name, j, got))
            comparisons += len(got)
    result = {'status': 'PASS', 'assignments': 500, 'scalar_or_residual_comparisons': comparisons,
              'prime': PRIME, 'seed': 72080, 'actual_port_assignments': 250,
              'scope': 'Finite signed/degenerate transcription diagnostics only; no compiler or consistency proof.'}
    (HERE / 'INDEPENDENT_LITERAL_RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()

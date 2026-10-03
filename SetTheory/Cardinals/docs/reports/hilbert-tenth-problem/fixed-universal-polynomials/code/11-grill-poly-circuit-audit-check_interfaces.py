# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent bounded checks of algebraic boundary and positive-domain lemmas.
Does not materialize actual universal input or any complete Pell witness.
"""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent

def need(x, m):
    if not x:
        raise ValueError(m)

def value(w):
    return int(w[::-1], 2) if w else 0
counts = {}
c = 0
for u in range(2, 4097):
    n = u.bit_length()
    q = 1 << n
    s = q - u
    beta = 2 * u + 1 - q
    need(s > 0 and beta > 0 and (s + beta == u + 1), 'canonical converse')
    allowed = []
    for h in range(2, n + 3):
        qh = 1 << h
        if qh - u > 0 and 2 * u + 1 - qh > 0:
            allowed.append(h)
    need(allowed == [n], 'canonical soundness uniqueness')
    c += 1
counts['canonical_inputs'] = c

def sym(i):
    return '01' * (8 * i - 5) + '11'
bits = [sym(2) + sym(1), sym(1) + sym(2)]
c0, c1 = map(value, bits)
need([c0, c1, c1 - c0] == [3941247658, 3937053418, -4194240], 'block constants')
c = 0
for qB in (2, 3, 5):
    prefix = '01' * (8 * qB)
    a = value(prefix)
    p = 1 << len(prefix)
    need(a == 2 * ((1 << 16 * qB) - 1) // 3 and a > 0, 'prefix positive fixed recipe')
    for r, l in ((1, 2), (3, 4), (5, 3)):
        suffix = sym(r) + sym(l)
        ss = value(suffix)
        for x in range(1, 66):
            u = x + 1
            n = u.bit_length()
            w = format(u, 'b')[::-1]
            Q = 1 << 32 * n
            R = sum((int(b) << 32 * i for i, b in enumerate(w)))
            N = value(prefix + ''.join((bits[int(b)] for b in w)) + suffix)
            m = (1 << 32) - 1
            need(N > 0 and m * N == m * a + p * c0 * (Q - 1) + p * m * (c1 - c0) * R + p * m * ss * Q, 'full frame identity')
            c += 1
counts['literal_U15_frame_cases'] = c
c = 0
for k in (4, 5, 8, 13):
    for h in range(2, 34):
        q = 1 << h
        Q = q ** k
        B = (1 << k - 1) * Q
        J = sum((B ** j for j in range(h)))
        ell = h
        v = sum((sum((B ** i for i in range(j))) for j in range(1, h)))
        g = B - 1 - h
        need(v > 0 and g > 0 and (2 <= h <= B - 2) and ((B - 1) * v + ell == J), 'positive unrestricted exponent')
        need(ell + g == B - 1 and all((not 1 <= h + t * (B - 1) <= B - 2 for t in (-2, -1, 1, 2))), 'no residue alias')
        mask = sum(((2 * B) ** j for j in range(h)))
        A = J & mask
        need(A == 1 and (A - 1) // (Q - 1) + 1 == 1 and (q - 1 > 0) and (Q - 1 > 0), 'input output one shifted quotient')
        c += 1
counts['unrestricted_exponent_cases'] = c
a = 28392
b = 7 * a
k = 2 * b
K = 1 << k

def E(y):
    grill = lambda n: '0' + '10' * n
    word = '0' * (14 * y + 7) + grill(a - 3) + grill(7) + grill(a - 4) + '0' * (3 * a - 14 * y - 10)
    need(len(word) == b and word.endswith('00'), 'original E exact width')
    return word
EE = {j: E(j) for j in (0, 30, 270, 300, 539)}
W = {j: value(EE[j] + EE[539]) for j in (0, 30, 270, 300)}
c = 0
for M in range(4):
    prefix = EE[0] + EE[539] + (EE[270] + EE[539]) * M + EE[30] + EE[539]
    C = W[0] + K * W[270] * sum((K ** j for j in range(M))) + K ** (M + 1) * W[30]
    L = K ** (M + 2)
    need(C == value(prefix) and L == 1 << len(prefix) and (C > 0), 'five parameter C/L formulas')
    for N in range(1, 5):
        word = prefix + (EE[300] + EE[539]) * N
        X = value(word)
        T = K ** N
        P0 = L * T
        need((K - 1) * X == (K - 1) * C + L * W[300] * (T - 1), 'exact unary value')
        need(P0 == 1 << len(word) and 0 < 3 * X < P0, 'same width strong cone')
        zs = P0 - 3 * X
        zw = zs + 2 * X
        need(zs > 0 and zw > 0 and (X + zw == P0), 'retained weak positive slack')
        need(X + zw != P0 * 2 and X + zw != P0 * (1 << 6), 'reject padding')
        c += 1
counts['actual_alphabet_E_prefix_queue_cases'] = c
c = 0
for aa in range(4):
    for cc in range(4):
        for dd in range(4):
            delta = aa * aa + 4 * aa + 3
            need((dd * dd - delta * cc * cc) % 4 != 3, 'main norm sign')
            for ff in range(4):
                for uu in range(4):
                    for yy in range(4):
                        aux = delta * (ff * ff - 1)
                        need((aux * (uu * uu - yy * yy) + yy * yy) % 4 != 3, 'auxiliary norm sign')
                        c += 1
for gap in range(4):
    need(gap * gap % 4 != 3, 'root norm sign')
counts['exhaustive_norm_residue_cases'] = c
c = 0
for U in range(-20, 21):
    for r in range(-6, 7):
        for s in range(-6, 7):
            F = U * (1 + r * r + s * s) - 1
            need((F == 0) == (U == 1 and r == s == 0), 'sign-safe unit finalizer')
            c += 1
counts['integer_unit_finalizer_cases'] = c
print(json.dumps({'status': 'PASS_INTERFACES', 'counts': counts, 'actual_universal_tape_or_full_Pell_witness_materialized': False}, indent=2, sort_keys=True))

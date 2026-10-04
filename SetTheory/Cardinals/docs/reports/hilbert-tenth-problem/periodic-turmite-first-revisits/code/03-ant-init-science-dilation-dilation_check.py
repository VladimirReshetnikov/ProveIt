#!/usr/bin/env python3
"""Own arithmetic DAG and small exact checks. Executes no upstream code.
The Pell equivalence is an explicitly cited theorem, not re-proved by tests.
"""
import json, math, hashlib, itertools, argparse, sys
from pathlib import Path

class DAG:

    def __init__(self):
        self.nodes = []
        self.witnesses = []
        self.equations = []
        self.names = set()
        self.M = 0
        self.A = 0
        self.outputs = {}

    def wit(self, n):
        if n in self.names:
            raise ValueError(n)
        self.names.add(n)
        self.witnesses.append(n)
        return n

    def gate(self, op, a, b):
        out = 'g' + str(len(self.nodes))
        self.nodes.append((out, op, a, b))
        self.M += op == '*'
        self.A += op != '*'
        return out

    def add(self, a, b):
        return self.gate('+', a, b)

    def sub(self, a, b):
        return self.gate('-', a, b)

    def mul(self, a, b):
        return self.gate('*', a, b)

    def eq(self, a, b):
        self.equations.append((a, b))

    def pos(self, n):
        return self.wit(n)

    def nat(self, n):
        return self.sub(self.wit(n + 'Plus'), 1)

    def record(self):
        raw = json.dumps({'nodes': self.nodes, 'equations': self.equations, 'witnesses': self.witnesses}, separators=(',', ':'))
        return {'M': self.M, 'A': self.A, 'total': self.M + self.A, 'positive_witnesses': len(self.witnesses), 'equations': len(self.equations), 'sha256': hashlib.sha256(raw.encode()).hexdigest()}

def exp_macro(d, base, index, out, p):
    """out=base**index for base>=2,index>=0,out>0;25 positive witnesses."""
    k = d.add(index, 1)
    m = d.mul(base, out)
    w = d.pos(p + 'w')
    a = d.add(d.pos(p + 'aMinus1'), 1)
    T = d.pos(p + 'T')
    z = d.pos(p + 'z')
    x = d.pos(p + 'x')
    y = d.pos(p + 'y')
    u = d.pos(p + 'u')
    v = d.pos(p + 'v')
    s = d.pos(p + 's')
    t = d.pos(p + 't')
    beta = d.add(d.pos(p + 'betaMinus1'), 1)
    dwb = d.nat(p + 'dwb')
    dwk = d.nat(p + 'dwk')
    dyk = d.nat(p + 'dyk')
    dtm = d.pos(p + 'dtm')
    qb = d.pos(p + 'qb')
    qv = d.pos(p + 'qv')
    qab1 = d.nat(p + 'qab1')
    qab2 = d.nat(p + 'qab2')
    qsx1 = d.nat(p + 'qsx1')
    qsx2 = d.nat(p + 'qsx2')
    qtk1 = d.nat(p + 'qtk1')
    qtk2 = d.nat(p + 'qtk2')
    qpow1 = d.nat(p + 'qpow1')
    qpow2 = d.nat(p + 'qpow2')
    aa = d.mul(a, a)
    delta = d.sub(aa, 1)
    yy = d.mul(y, y)
    foury = d.mul(4, y)
    d.eq(d.mul(x, x), d.add(d.mul(delta, yy), 1))
    d.eq(d.mul(u, u), d.add(d.mul(delta, d.mul(v, v)), 1))
    d.eq(d.mul(s, s), d.add(d.mul(d.sub(d.mul(beta, beta), 1), d.mul(t, t)), 1))
    d.eq(beta, d.add(1, d.mul(foury, qb)))
    d.eq(d.add(beta, d.mul(u, qab1)), d.add(a, d.mul(u, qab2)))
    d.eq(v, d.mul(yy, qv))
    d.eq(d.add(s, d.mul(u, qsx1)), d.add(x, d.mul(u, qsx2)))
    d.eq(d.add(t, d.mul(foury, qtk1)), d.add(k, d.mul(foury, qtk2)))
    d.eq(y, d.add(k, dyk))
    d.eq(w, d.add(base, dwb))
    d.eq(w, d.add(k, dwk))
    d.eq(T, d.add(m, dtm))
    wp = d.add(w, 1)
    wz = d.mul(w, z)
    d.eq(aa, d.add(d.mul(d.sub(d.mul(wp, wp), 1), d.mul(wz, wz)), 1))
    d.eq(d.mul(d.mul(2, a), base), d.add(T, d.add(d.mul(base, base), 1)))
    d.eq(d.add(x, d.mul(T, qpow1)), d.add(d.add(d.mul(y, d.sub(a, base)), m), d.mul(T, qpow2)))

def dilation(d, C, Raw, p, reverse=False):
    n = d.nat(p + 'length')
    power = d.pos(p + 'radixPower')
    E = d.pos(p + 'binaryPower')
    B = d.pos(p + 'auxRadix')
    F = d.pos(p + 'auxPower')
    U = d.nat(p + 'repunit')
    D = d.nat(p + 'packedWord')
    L = d.pos(p + 'binomialRadix')
    Y = d.pos(p + 'coefficientPosition')
    Z = d.pos(p + 'binomialExpansion')
    q2 = d.nat(p + 'rawQuotient')
    qC = d.nat(p + 'outQuotient')
    q = d.nat(p + 'coefficientQuotient')
    odd = d.nat(p + 'oddHalf')
    r = d.nat(p + 'lowerRemainder')
    sr = d.pos(p + 'rawSlack')
    sc = d.pos(p + 'coefficientSlack')
    sl = d.pos(p + 'lowerSlack')
    so = d.pos(p + 'outSlack')
    value = d.nat(p + 'value')
    exp_macro(d, C, n, power, p + 'e1_')
    exp_macro(d, 2, n, E, p + 'e2_')
    exp_macro(d, 2, d.add(d.mul(C, power), 2), B, p + 'e3_')
    exp_macro(d, B, n, F, p + 'e4_')
    exp_macro(d, 2, d.add(U, 1), L, p + 'e5_')
    exp_macro(d, L, D, Y, p + 'e6_')
    exp_macro(d, d.add(L, 1), U, Z, p + 'e7_')
    d.eq(d.sub(F, 1), d.mul(d.sub(B, 1), U))
    x = d.sub(Raw, E)
    d.eq(d.add(x, sr), E)
    xnat = d.nat(p + 'rawPayload')
    d.eq(xnat, x)
    d.eq(D, d.add(d.mul(q2, d.sub(B, 2)), xnat))
    c = d.add(d.mul(2, odd), 1)
    d.eq(Z, d.add(d.mul(d.add(d.mul(q, L), c), Y), r))
    d.eq(d.add(c, sc), L)
    d.eq(d.add(r, sl), Y)
    if reverse:
        d.eq(d.mul(power, D), d.add(d.mul(qC, d.sub(d.mul(B, C), 1)), d.mul(C, value)))
    else:
        d.eq(D, d.add(d.mul(qC, d.sub(B, C)), value))
    d.eq(d.add(value, so), power)
    return {'length': n, 'power': power, 'value': value}

def build(mode):
    d = DAG()
    if mode == 'exp':
        exp_macro(d, 'base', 'index', 'output', 'p_')
        d.outputs = {'output': 'output'}
    elif mode in ('forward', 'reverse'):
        d.outputs = dilation(d, 'C', 'Raw', 'd_', mode == 'reverse')
    elif mode in ('pair', 'pair_inline', 'pair_positive'):
        left = dilation(d, 'G', 'RawLeft', 'L_', True)
        right = dilation(d, 'G', 'RawRight', 'R_', False)
        A = d.mul(left['power'], right['power'])
        B = right['power']
        T = d.add(d.mul(d.mul('G', B), left['value']), right['value'])
        d.outputs = {'A': A, 'B': B, 'T': T}
        if mode != 'pair_inline':
            d.eq('A', A)
            d.eq('B', B)
            d.eq('Tplus' if mode == 'pair_positive' else 'T', d.add(T, 1) if mode == 'pair_positive' else T)
    else:
        raise ValueError(mode)
    return d

def pell(a, n):
    x, y = (1, 0)
    for _ in range(n):
        x, y = (a * x + (a * a - 1) * y, x + a * y)
    return (x, y)

def check_pell_witness(base, index):
    k = index + 1
    out = base ** index
    m = base * out
    w = max(base, k)
    a, znum = pell(w + 1, w)
    if not znum % w == 0:
        raise AssertionError('Independent exact check failed')
    z = znum // w
    T = 2 * a * base - base * base - 1
    x, y = pell(a, k)
    u, v = pell(a, 2 * k * y)
    if not v % (y * y) == 0:
        raise AssertionError('Independent exact check failed')
    beta = a + u * ((1 - a) * pow(u, -1, 4 * y) % (4 * y))
    if beta <= 1:
        beta += u * 4 * y
    s, t = pell(beta, k)
    if not (x * x == (a * a - 1) * y * y + 1 and u * u == (a * a - 1) * v * v + 1 and (s * s == (beta * beta - 1) * t * t + 1)):
        raise AssertionError('Independent exact check failed')
    if not (beta > 1 and (beta - 1) % (4 * y) == 0 and ((beta - a) % u == 0) and (v > 0) and (v % (y * y) == 0) and ((s - x) % u == 0) and ((t - k) % (4 * y) == 0)):
        raise AssertionError('Independent exact check failed')
    if not (k <= y and m < T and (base <= w) and (k <= w) and (a * a == ((w + 1) ** 2 - 1) * (w * z) ** 2 + 1)):
        raise AssertionError('Independent exact check failed')
    if not (x - y * (a - base) - m) % T == 0:
        raise AssertionError('Independent exact check failed')
    return True

def check_dilation_small():
    count = 0
    for C in range(2, 10):
        for n in range(7):
            cp = C ** n
            B = 1
            while B <= max(cp + C, 2 ** n + 2):
                B *= 2
            U = (B ** n - 1) // (B - 1)
            for raw in range(2 ** n, 2 ** (n + 1)):
                payload = raw - 2 ** n
                bits = [payload >> i & 1 for i in range(n)]
                D = sum((b * B ** i for i, b in enumerate(bits)))
                v = sum((b * C ** i for i, b in enumerate(bits)))
                rv = sum((b * C ** (n - 1 - i) for i, b in enumerate(bits)))
                if not (B > cp + C and B > 2 ** n + 2 and (D & ~U == 0)):
                    raise AssertionError('Independent exact check failed')
                if not (D % (B - 2) == payload and D % (B - C) == v and (cp * D % (B * C - 1) == C * rv)):
                    raise AssertionError('Independent exact check failed')
                if not (0 <= v < cp and 0 <= rv < cp):
                    raise AssertionError('Independent exact check failed')
                count += 1
    extraction = 0
    for C, n in [(2, 0), (2, 1), (2, 2), (3, 1), (3, 2)]:
        cp = C ** n
        B = 1
        while B <= max(cp + C, 2 ** n + 2):
            B *= 2
        U = (B ** n - 1) // (B - 1)
        L = 2 ** (U + 1)
        Z = (L + 1) ** U
        for D in range(U + 2):
            Y = L ** D
            c = Z // Y % L
            if not c == (math.comb(U, D) if D <= U else 0):
                raise AssertionError('Independent exact check failed')
            if not bool(c % 2) == (D & ~U == 0):
                raise AssertionError('Independent exact check failed')
            extraction += 1
    return (count, extraction)

def check_pair():
    cases = 0
    for G in range(2, 8):
        for L in range(5):
            for R in range(5):
                for l in itertools.product((0, 1), repeat=L):
                    for r in itertools.product((0, 1), repeat=R):
                        left = sum((b * G ** j for j, b in enumerate(l)))
                        right = sum((b * G ** (R - 1 - j) for j, b in enumerate(r)))
                        T = G ** (R + 1) * left + right
                        tape = list(reversed(l)) + [0] + list(r)
                        ref = 0
                        for b in tape:
                            ref = ref * G + b
                        if not T == ref:
                            raise AssertionError('Independent exact check failed')
                        cases += 1
    return cases

def payload(obj):
    return {'nodes': obj.nodes, 'equations': obj.equations, 'witnesses': obj.witnesses, 'outputs': obj.outputs}

def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON object key: ' + key)
        result[key] = value
    return result

def reject_constant(value):
    raise ValueError('Non-finite JSON constant: ' + value)

def canonical(data):
    return json.dumps(data, sort_keys=True, separators=(',', ':'), allow_nan=False)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--output-dir', type=Path, help='Write newly built evidence into a NEW directory; refuses existing paths.')
    group.add_argument('--verify-dir', type=Path, help='Read-only verify existing evidence; defaults to final-evidence beside this script.')
    args = parser.parse_args()
    objects = {m: build(m) for m in ['exp', 'forward', 'reverse', 'pair', 'pair_inline', 'pair_positive']}
    checked, extraction = check_dilation_small()
    pell_tests = sum((check_pell_witness(b, 0) for b in [2, 3]))
    result = {'ledgers': {m: obj.record() for m, obj in objects.items()}, 'word_cases': checked, 'binomial_extraction_cases': extraction, 'pair_cases': check_pair(), 'pell_constructed_cases': pell_tests, 'scope': 'Own finite checks; full equivalence proof and cited Pell theorem are separate.'}
    expected = {mode + '-dag.json': payload(obj) for mode, obj in objects.items()}
    expected['check_receipt.json'] = result
    if args.output_dir is not None:
        target = args.output_dir.resolve()
        target.mkdir(parents=True, exist_ok=False)
        for name, data in expected.items():
            (target / name).write_text(json.dumps(data, indent=2) + '\n')
        status = 'built into new directory'
    else:
        target = (args.verify_dir or Path(__file__).resolve().parent / 'final-evidence').resolve()
        for name, data in expected.items():
            actual = json.loads((target / name).read_text(), object_pairs_hook=strict_object, parse_constant=reject_constant)
            if canonical(actual) != canonical(data):
                raise ValueError('Evidence mismatch: ' + str(target / name))
        status = 'read-only verification passed'
    print(json.dumps({'status': status, 'directory': str(target), 'result': result}, indent=2))
if __name__ == '__main__':
    main()

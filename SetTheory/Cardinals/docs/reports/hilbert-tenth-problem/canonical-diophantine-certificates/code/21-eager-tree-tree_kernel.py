#!/usr/bin/env python3
"""Own exact checker for the five-case eager tree-value application kernel.
No upstream program is imported or executed. Standard library only.
"""
from dataclasses import dataclass
from functools import lru_cache
from math import isqrt
from pathlib import Path
import hashlib
import json


def S(a):
    return 2 * a + 1


def F(a, b):
    return (a + b) * (a + b + 1) + 2 * b + 2


def split(n):
    if type(n) is not int or n < 0:
        raise ValueError('code must be a natural integer, not bool/float')
    if n == 0:
        return (0,)
    if n & 1:
        return (1, (n - 1) // 2)
    q = (n - 2) // 2
    w = (isqrt(8 * q + 1) - 1) // 2
    b = q - w * (w + 1) // 2
    a = w - b
    assert a >= 0 and b >= 0 and a < n and b < n and F(a, b) == n
    return (2, a, b)


@lru_cache(None)
def decode(n):
    d = split(n)
    return () if d[0] == 0 else tuple(decode(x) for x in d[1:])


def encode(tree):
    if len(tree) == 0:
        return 0
    if len(tree) == 1:
        return S(encode(tree[0]))
    assert len(tree) == 2
    return F(encode(tree[0]), encode(tree[1]))


class Exhausted(Exception):
    pass


class RepeatedActiveCall(Exception):
    pass


class Evaluation:
    """Memoized integer evaluator, recording ordered premise multiplicities."""
    def __init__(self, budget=1000, max_bits=8192):
        self.budget = budget
        self.max_bits = max_bits
        self.records = {}
        self.active = set()

    def app(self, x, y):
        if type(x) is not int or x < 0 or type(y) is not int or y < 0:
            raise ValueError("application codes must be exact natural integers")
        key = (x, y)
        if key in self.records:
            return self.records[key]['z']
        if key in self.active:
            raise RepeatedActiveCall(key)
        if self.budget <= 0 or max(x.bit_length(), y.bit_length()) > self.max_bits:
            raise Exhausted()
        self.budget -= 1
        self.active.add(key)
        try:
            a = b = c = u = v = 0
            premises = []
            sx = split(x)
            if sx[0] == 0:
                tag, z = 0, S(y)
            elif sx[0] == 1:
                a = sx[1]
                tag, z = 1, F(a, y)
            else:
                first, second = sx[1:]
                sf = split(first)
                if sf[0] == 0:
                    tag, b, z = 2, second, second
                elif sf[0] == 1:
                    tag, a, b = 3, sf[1], second
                    u = self.app(b, y)
                    v = self.app(a, y)
                    z = self.app(u, v)
                    premises = [(b, y), (a, y), (u, v)]
                else:
                    tag, a, b, c = 4, sf[1], sf[2], second
                    u = self.app(y, a)
                    z = self.app(u, b)
                    premises = [(y, a), (u, b)]
            if z.bit_length() > self.max_bits:
                raise Exhausted()
            h = 1 + sum(self.records[p]['h'] for p in premises)
            self.records[key] = dict(x=x, y=y, z=z, h=h, a=a, b=b, c=c,
                                     u=u, v=v, tag=tag, premises=premises)
            return z
        finally:
            self.active.discard(key)


def structural_app(x, y, budget):
    """Independent value-tree evaluator: no integer pairing, no memoization."""
    if budget[0] <= 0:
        raise Exhausted()
    budget[0] -= 1
    if len(x) == 0:
        return (y,), 1
    if len(x) == 1:
        return (x[0], y), 1
    left, right = x
    if len(left) == 0:
        return right, 1
    if len(left) == 1:
        u, hu = structural_app(right, y, budget)
        v, hv = structural_app(left[0], y, budget)
        z, hz = structural_app(u, v, budget)
        return z, 1 + hu + hv + hz
    u, hu = structural_app(y, left[0], budget)
    z, hz = structural_app(u, left[1], budget)
    return z, 1 + hu + hz


SCALARS = ['x', 'y', 'z', 'h', 'a', 'b', 'c', 'u', 'v', 'd', 'e', 'q', 'j', 'k']


def finalize_row(record, indices, N):
    r = {k: record[k] for k in SCALARS[:9]}
    a, b, c, y = r['a'], r['b'], r['c'], r['y']
    r.update(d=F(a, b), e=F(a, y), q=F(0, b), j=F(S(a), b), k=F(F(a, b), c))
    r['t'] = [int(i == record['tag']) for i in range(5)]
    r['pointers'] = [[0] * N for _ in range(3)]
    for slot, p in enumerate(record['premises']):
        r['pointers'][slot][indices[p]] = 1
    return r


def certificate(evaluation, root, pad=0):
    # Root first; neither ordering nor reachability of all rows is assumed.
    keys = [root] + [k for k in evaluation.records if k != root]
    N = len(keys) + pad
    indices = {k: i for i, k in enumerate(keys)}
    rows = [finalize_row(evaluation.records[k], indices, N) for k in keys]
    for _ in range(pad):
        r = dict(x=0, y=0, z=1, h=1, a=0, b=0, c=0, u=0, v=0,
                 tag=0, premises=[])
        rows.append(finalize_row(r, indices, N))
    return rows


@dataclass
class G:
    value: int
    degree: int
    circuit: object

    def __add__(self, other):
        other = self.circuit.coerce(other)
        self.circuit.A += 1
        return G(self.value + other.value, max(self.degree, other.degree), self.circuit)

    __radd__ = __add__

    def __sub__(self, other):
        other = self.circuit.coerce(other)
        self.circuit.A += 1
        return G(self.value - other.value, max(self.degree, other.degree), self.circuit)

    def __mul__(self, other):
        other = self.circuit.coerce(other)
        self.circuit.M += 1
        return G(self.value * other.value, self.degree + other.degree, self.circuit)

    __rmul__ = __mul__


class Circuit:
    def __init__(self):
        self.A = self.M = 0

    def coerce(self, value):
        return value if isinstance(value, G) else G(value, 0, self)

    def var(self, value):
        return G(value, 1, self)

    def sum(self, terms):
        terms = list(terms)
        if not terms:
            return self.coerce(0)
        out = terms[0]
        for x in terms[1:]:
            out = out + x
        return out


def valid_domain(rows, p, n, o):
    if type(rows) is not list or not rows or any(type(v) is not int or v < 0 for v in [p, n, o]):
        return False
    N = len(rows)
    for row in rows:
        if type(row) is not dict or set(row) != set(SCALARS + ['t', 'pointers']):
            return False
        if type(row['t']) is not list or type(row['pointers']) is not list:
            return False
        if len(row['t']) != 5 or len(row['pointers']) != 3:
            return False
        if any(type(a) is not list or len(a) != N for a in row['pointers']):
            return False
        values = [row[k] for k in SCALARS] + row['t'] + sum(row['pointers'], [])
        if any(type(v) is not int or v < 0 for v in values):
            return False
    return True


def polynomial(rows, p, n, o):
    if not valid_domain(rows, p, n, o):
        raise ValueError('malformed certificate or non-natural coordinate')
    N = len(rows)
    C = Circuit()
    rs = []
    lifted = [{**{k: C.var(row[k]) for k in SCALARS},
               't': [C.var(x) for x in row['t']],
               'pointers': [[C.var(x) for x in ar] for ar in row['pointers']]}
              for row in rows]
    def pair(a, b):
        s = a + b
        return s * (s + 1) + 2 * b + 2
    def stem(a):
        return 2 * a + 1
    for r in lifted:
        x, y, z, h, a, b, c, u, v, d, e, q, j, k = [r[name] for name in SCALARS]
        t0, t1, t2, t3, t4 = r['t']
        sa, sy = stem(a), stem(y)
        active = t3 + t4
        rs.extend([
            C.sum(r['t']) - 1,
            d - pair(a, b), e - pair(a, y), q - pair(C.coerce(0), b),
            j - pair(sa, b), k - pair(d, c),
            x - C.sum([t1 * sa, t2 * q, t3 * j, t4 * k]),
            t0 * (z - sy), t1 * (z - e), t2 * (z - b),
        ])
        rowsums = [C.sum(ps) for ps in r['pointers']]
        rs.extend([rowsums[0] - active, rowsums[1] - active, rowsums[2] - t3])
        targets = [
            [t3 * b + t4 * y, t3 * y + t4 * a, active * u],
            [t3 * a + t4 * u, t3 * y + t4 * b, t3 * v + t4 * z],
            [t3 * u, t3 * v, t3 * z],
        ]
        for slot in range(3):
            for col, field in enumerate(['x', 'y', 'z']):
                rs.append(C.sum(r['pointers'][slot][jj] * lifted[jj][field]
                                for jj in range(N)) - targets[slot][col])
        rs.append(h - 1 - C.sum(r['pointers'][slot][jj] * lifted[jj]['h']
                               for slot in range(3) for jj in range(N)))
    rs.extend([lifted[0]['x'] - C.var(p), lifted[0]['y'] - C.var(n), lifted[0]['z'] - C.var(o)])
    assert len(rs) == 23 * N + 3
    assert max(r.degree for r in rs) == 2
    before = dict(M=C.M, A=C.A)
    result = C.sum(r * r for r in rs)
    return dict(value=result.value, residuals=[r.value for r in rs],
                degree_bound=result.degree, witnesses=3*N*N+19*N,
                residual_count=len(rs), certificate_gates=before,
                polynomial_gates=dict(M=C.M, A=C.A))


def cyclic_counterfeit(output=0):
    I, omega = 10, 1014
    ev = Evaluation()
    assert ev.app(I, omega) == omega
    fake = dict(x=omega, y=omega, z=output, h=1, a=I, b=I, c=0,
                u=omega, v=omega, tag=3,
                premises=[(I, omega), (I, omega), (omega, omega)])
    ev.records[(omega, omega)] = fake
    return certificate(ev, (omega, omega))


def main():
    bijections = 10000
    for n in range(bijections):
        assert encode(decode(n)) == n
    for a in range(80):
        assert split(S(a)) == (1, a)
        for b in range(80):
            assert split(F(a,b)) == (2,a,b)
    assert F(S(0), S(0)) == 10
    assert F(S(10), 10) == 1014

    checked = cycles = exhausted = structural = 0
    max_witnesses = 0
    cases_by_tag = [0]*5
    for x in range(32):
        for y in range(24):
            ev = Evaluation(budget=250, max_bits=4096)
            try:
                z = ev.app(x,y)
            except RepeatedActiveCall:
                cycles += 1
                continue
            except (Exhausted, RecursionError):
                exhausted += 1
                continue
            rows = certificate(ev, (x,y))
            result = polynomial(rows, x,y,z)
            assert result['value'] == 0
            max_witnesses = max(max_witnesses, result['witnesses'])
            for r in rows:
                cases_by_tag[r['t'].index(1)] += 1
            checked += 1
            tree, h = structural_app(decode(x), decode(y), [100000])
            assert encode(tree) == z and h == ev.records[(x,y)]['h']
            structural += 1

    ev = Evaluation()
    assert ev.app(10,10) == 10
    example = certificate(ev, (10,10))
    er = polynomial(example,10,10,10)
    assert len(example) == 4 and example[0]['h'] == 4
    for pad in range(4):
        assert polynomial(certificate(ev,(10,10),pad),10,10,10)['value'] == 0
    for bad in [True, 1.0, -1]:
        assert not valid_domain(example, bad, 10, 10)
    for target in range(12):
        cf = cyclic_counterfeit(target)
        cr = polynomial(cf,1014,1014,target)
        assert cr['value'] == 81
        assert [v for v in cr['residuals'] if v] == [-9]
        # Height residuals are numbered 22 modulo 23.
        assert all(v == 0 for i,v in enumerate(cr['residuals']) if i % 23 != 22)
    try:
        Evaluation().app(1014,1014)
    except RepeatedActiveCall:
        pass
    else:
        raise AssertionError('omega should have a repeated active call')

    # Interrupted/rejected calls must not poison later uses of an evaluator.
    interrupted = Evaluation(budget=1)
    try:
        interrupted.app(10,10)
    except Exhausted:
        pass
    else:
        raise AssertionError('one-call budget should be exhausted')
    assert not interrupted.active
    interrupted.budget = 100
    assert interrupted.app(10,10) == 10
    assert interrupted.records[(10,10)]['h'] == 4 and not interrupted.active
    reused_cycle = Evaluation()
    for _ in range(2):
        try:
            reused_cycle.app(1014,1014)
        except RepeatedActiveCall:
            pass
        else:
            raise AssertionError('genuine cycle should remain detectable')
        assert not reused_cycle.active
        assert reused_cycle.app(0,0) == 1 and not reused_cycle.active

    compression=[]
    a=10
    for level in range(9):
        ev=Evaluation(budget=1000,max_bits=32768)
        assert ev.app(a,10)==10
        rows=certificate(ev,(a,10))
        pr=polynomial(rows,a,10,10)
        assert pr['value']==0
        assert len(rows)==level+4
        h=ev.records[(a,10)]['h']
        assert h==9*(2**level)-5
        tree, sh = structural_app(decode(a),decode(10),[100000])
        assert encode(tree)==10 and sh==h
        compression.append(dict(level=level, input_bits=a.bit_length(),
                                distinct_calls=len(rows), unfolded_calls=h))
        a=F(S(a),a)

    # Counter exact literal-ledger polynomials from the documented schedule.
    ledgers=[]
    for N in range(1,10):
        leaf=Evaluation(); leaf.app(0,0)
        rows=certificate(leaf,(0,0),pad=N-1)
        pr=polynomial(rows,0,0,1)
        assert pr['value']==0
        assert pr['certificate_gates'] == dict(M=12*N*N+33*N, A=15*N*N+46*N+3)
        assert pr['polynomial_gates'] == dict(M=12*N*N+56*N+3, A=15*N*N+69*N+5)
        ledgers.append(dict(N=N,**{k:pr[k] for k in ['witnesses','residual_count','certificate_gates','polynomial_gates']}))

    here=Path(__file__).resolve().parent
    receipt=dict(status='finite exact tests passed; not a proof-assistant verification',
                 code_roundtrips=bijections, constructor_pairs=80*80,
                 bounded_pair_trials=32*24, terminating_certificates=checked,
                 structural_agreements=structural, detected_recursive_cycles=cycles,
                 budget_or_size_inconclusive=exhausted, certified_rows_by_tag=cases_by_tag,
                 max_test_witnesses=max_witnesses, cyclic_false_outputs_rejected=12,
                 cyclic_nonheight_residuals_all_zero=True, cyclic_sos_value=81,
                 interrupted_evaluator_reuse_checks=3,
                 identity_example={k:er[k] for k in er if k!='residuals'},
                 compression=compression,ledgers=ledgers,
                 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (here/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (here/'identity_certificate.json').write_text(json.dumps(dict(p=10,n=10,o=10,rows=example),indent=2)+'\n')
    (here/'cyclic_counterfeit.json').write_text(json.dumps(dict(p=1014,n=1014,o=0,rows=cyclic_counterfeit(0)),indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':
    main()

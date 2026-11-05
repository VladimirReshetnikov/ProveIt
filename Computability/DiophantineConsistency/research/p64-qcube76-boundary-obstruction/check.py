#!/usr/bin/env python3
"""Finite graph-identity spot check; it does not construct a zero."""
import hashlib
import json
import random
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
FILES = {
    'old': ('p64-qcube77-candidate/graph.json',
            '8cda8e5729f7af6b725631a0a9a5b5d8886c24a4e62d94d889ada47ce54e7315'),
    'new': ('p64-qcube76-transport-candidate/graph.json',
            '58b259ef212dded883ef0e36aedad303d07dad5ae00d7b1c6674ce4178a09de8'),
}


def read_graph(which):
    rel, expected = FILES[which]
    raw = (RESEARCH / rel).read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{which} graph hash changed')
    return json.loads(raw)


def evaluate(graph, ports, witness):
    env = dict(zip(graph['fixed_numerals'], ports))
    env.update(zip(graph['witnesses'], witness))
    def val(x):
        return x if isinstance(x, int) else env[x]
    for name, op, left, right in graph['source']:
        a, b = val(left), val(right)
        env[name] = {'+': lambda: a + b, '-': lambda: a - b,
                     '*': lambda: a * b}[op]()
    return env


old, new = read_graph('old'), read_graph('new')
rng = random.Random(762026)
zero_count = 0
checked = 0
for _ in range(500):
    beta = rng.randint(1, 8)
    J = rng.randint(1, 8)
    q = beta * J + 1
    if q < 4:
        continue
    w = rng.randint(1, 8)
    F, alpha = 1, 1
    C = q - F - alpha
    K0 = (q - 2) * (w + 1)
    z = q - 3 + (q - 2) * w
    MC, MF = rng.randint(0, 8), rng.randint(0, 8)
    inputs = [J, F, alpha, z] + [rng.randint(1, 8) for _ in range(10)]
    inputs[8] = w
    a = evaluate(old, [beta, K0, MC, MF], inputs)
    assert C > 0 and a['Lt'] == 0
    gap_old = (q - 1) * (q - F) + alpha
    delta = gap_old - (q - 1)
    F2, C2, z2 = q - 1, 1, w
    K02 = (w + 1) * (q - 1) - w
    MC2 = MC + delta * beta * (q + 1)
    inputs2 = inputs.copy()
    inputs2[1:4] = [F2, C2, z2]
    b = evaluate(new, [beta, K02, MC2, MF], inputs2)
    assert delta > 0 and K02 >= 0 and MC2 >= 0
    assert F2 > 0 and C2 > 0 and z2 > 0 and q - F2 - C2 == 0
    assert b['Lt'] == 0
    for field in ('R', 'A0', 'M', 'W', 'Na', 'Lt', 'polynomial'):
        assert a[field] == b[field], field
    zero_count += int(a['polynomial'] == 0)
    checked += 1
print('PASS: changed-port cases:', checked, 'seed zeros:', zero_count)

zero_count = 0
checked = 0
for _ in range(500):
    beta = rng.randint(1, 8)
    J = rng.randint(1, 8)
    q = beta * J + 1
    if q < 5:
        continue
    w = rng.randint(1, 8)
    F, alpha = 2, 1
    C = q - F - alpha
    L = (q - 1) * (w + 1) - 1
    K0 = L - w
    z = (w + 1) * C - 1
    MC, MF = rng.randint(0, 8), rng.randint(0, 8)
    inputs = [J, F, alpha, z] + [rng.randint(1, 8) for _ in range(10)]
    inputs[8] = w
    ports = [beta, K0, MC, MF]
    a = evaluate(old, ports, inputs)
    assert C > 0 and z > 0 and K0 >= 0 and a['Lt'] == 0
    assert (L + 1) % (q - 1) == 0
    numerator = L * q + 1
    assert numerator % (q - 1) == 0
    F2, C2, z2 = F - 1, C + q, z + numerator // (q - 1)
    inputs2 = inputs.copy()
    inputs2[1:4] = [F2, C2, z2]
    b = evaluate(new, ports, inputs2)
    assert F2 > 0 and C2 > 0 and z2 > 0 and q - F2 - C2 < 0
    assert b['Lt'] == 0
    for field in ('R', 'A0', 'M', 'W', 'Na', 'Lt', 'polynomial'):
        assert a[field] == b[field], field
    zero_count += int(a['polynomial'] == 0)
    checked += 1
print('PASS: fixed-port conditional cases:', checked, 'seed zeros:', zero_count)

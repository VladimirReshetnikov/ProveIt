#!/usr/bin/env python3
"""External symbolic leading-term certificate for the all-equal diagonal.

This reads the inert 65-gate graph and performs exact arithmetic; it is not
a Lean proof or a formal binding to TeX/PDF bytes.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
GRAPH = HERE.parent / 'carrier65-independent/INCOMING_CARRIER65.json'
assert hashlib.sha256(GRAPH.read_bytes()).hexdigest() == 'bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7'
graph = json.loads(GRAPH.read_text())

# A polynomial is a sparse dictionary of exponent tuples to integer values.
def add(a, b, sign=1):
    c = a.copy()
    for exponent, coefficient in b.items():
        c[exponent] = c.get(exponent, 0) + sign * coefficient
        if not c[exponent]: del c[exponent]
    return c

def mul(a, b):
    c = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple(x + y for x, y in zip(ea, eb))
            c[e] = c.get(e, 0) + ca * cb
            if not c[e]: del c[e]
    return c

def const(n, arity):
    return {(0,) * arity: n} if n else {}

def sym(i, arity):
    e = [0] * arity
    e[i] = 1
    return {tuple(e): 1}

# Check the exact generic cancellation identity independently of coefficient
# degree calculations. Symbols below are X, a, c, H, gamma.
X, a, c, H, g = [sym(i, 5) for i in range(5)]
root = add(X, mul(g, H)); ac = mul(a, c); c2 = mul(c, c)
left = add(mul(add(root, ac), add(root, ac)), mul(add(mul(a, a), H), c2), -1)
right = add(add(mul(root, root), mul(const(2, 5), mul(ac, root))), mul(H, c2), -1)
assert left == right

# Each pair is an upper bound in t and the exact coefficient at that bound,
# with coefficients in Z[beta,K,mu,omega]. A zero coefficient is rejected:
# it would require keeping more t terms. The known main-norm cancellation is
# handled by its independently checked identity above.
def leading_add(a, b, sign=1):
    da, ca = a; db, cb = b
    if da > db: return a
    if db > da: return (db, cb if sign == 1 else mul(const(-1, 4), cb))
    result = add(ca, cb, sign)
    assert result, 'cancelled leading t coefficient requires more terms'
    return da, result

def leading_mul(a, b):
    d = a[0] + b[0]; c = mul(a[1], b[1])
    assert c
    return d, c

ops = {'+': leading_add, '-': lambda a,b: leading_add(a,b,-1), '*': leading_mul}
env = {name: (1, const(1, 4)) for name in graph['witnesses']}
env.update({name: (0, sym(i, 4)) for i,name in enumerate(graph['fixed_numerals'])})
env.update({n: (0, const(n, 4)) for n in (1, 3, 4)})
for name, op, a, b in graph['source']:
    if name == 'N1':
        # (X + gamma H)^2 + 2ac(X + gamma H) - Hc²
        r = leading_add(env['X'], leading_mul(env['gamma'], env['H']))
        first = leading_mul(r, r)
        second = leading_mul((0, const(2, 4)), leading_mul(leading_mul(env['ac'], r), (0, const(1, 4))))
        third = leading_mul(env['H'], env['c2'])
        env[name] = leading_add(leading_add(first, second), third, -1)
    else:
        env[name] = ops[op](env[a], env[b])

expected = {'N0': (22, -4, 14), 'N1': (18, 16, 11), 'Na': (62, 64, 34),
            'Nt': (2, -2, 0), 'scaled_Ns': (46, -16, 28),
            'polynomial': (150, -131072, 87)}
for name, (degree, coefficient, beta_power) in expected.items():
    assert env[name] == (degree, {(beta_power, 0, 0, 0): coefficient}), (name, env[name])
    print(f'{name}: degree {degree}, coefficient {coefficient} * beta^{beta_power}')
print('External formal-coefficient arithmetic passed; beta != 0 makes the final leading coefficient nonzero.')

#!/usr/bin/env python3
"""Compact polynomial-only evaluation of the norm of five square roots.

This independently derived evaluator groups four radicals into two pairs,
then evaluates their norm in one quadratic algebra for the fifth radical.
No floating-point arithmetic, roots, divisions, or exponentiation gates.
"""
import ast
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


class Circuit:
    def __init__(self):
        self.nodes = []
        self.cache = {}

    def lift(self, x):
        return x if isinstance(x, Wire) else Wire(self, ('const', int(x)))

    def leaf(self, name):
        return Wire(self, ('leaf', name))

    def op(self, op, a, b):
        a, b = self.lift(a), self.lift(b)
        if a.ref[0] == 'const' and b.ref[0] == 'const':
            x, y = a.ref[1], b.ref[1]
            return self.lift({'add': lambda: x+y, 'sub': lambda: x-y,
                              'mul': lambda: x*y}[op]())
        if op in ('add', 'mul') and repr(a.ref) > repr(b.ref):
            a, b = b, a
        if op == 'add':
            if a.ref == ('const', 0): return b
            if b.ref == ('const', 0): return a
        if op == 'sub':
            if b.ref == ('const', 0): return a
            if a.ref == b.ref: return self.lift(0)
        if op == 'mul':
            if ('const', 0) in (a.ref, b.ref): return self.lift(0)
            if a.ref == ('const', 1): return b
            if b.ref == ('const', 1): return a
        key = (op, a.ref, b.ref)
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(key)
        return Wire(self, ('node', self.cache[key]))

    def export(self, out, inputs, ports):
        live = set()
        def visit(ref):
            if ref[0] != 'node' or ref[1] in live: return
            live.add(ref[1])
            _, a, b = self.nodes[ref[1]]
            visit(a); visit(b)
        visit(out.ref)
        order = sorted(live)
        ids = {old: new for new, old in enumerate(order)}
        def remap(ref):
            return ['node', ids[ref[1]]] if ref[0] == 'node' else list(ref)
        nodes = [[self.nodes[i][0], remap(self.nodes[i][1]), remap(self.nodes[i][2])]
                 for i in order]
        return {'variables': inputs, 'fixed_numerals': ports,
                'nodes': nodes, 'output': remap(out.ref),
                'operations': len(nodes),
                'counts': {op: sum(n[0] == op for n in nodes)
                           for op in ('add', 'sub', 'mul')},
                'convention': 'Every live binary addition, subtraction, and multiplication costs one; fixed integer leaves and reuse are free.'}


class Wire:
    def __init__(self, circuit, ref): self.c, self.ref = circuit, ref
    def __add__(self, other): return self.c.op('add', self, other)
    __radd__ = __add__
    def __sub__(self, other): return self.c.op('sub', self, other)
    def __rsub__(self, other): return self.c.op('sub', other, self)
    def __mul__(self, other): return self.c.op('mul', self, other)
    __rmul__ = __mul__
    def __neg__(self): return 0-self
    def __pow__(self, n):
        if not isinstance(n, int) or n < 0: raise ValueError('nonconstant power')
        out, b = self.c.lift(1), self
        while n:
            if n & 1: out = out*b
            n >>= 1
            if n: b = b*b
        return out


class Quad:
    """a+b*sqrt(d), implemented with polynomial arithmetic only."""
    def __init__(self, a, b, d): self.a, self.b, self.d = a, b, d
    def lift(self, x): return x if isinstance(x, Quad) else Quad(x, 0, self.d)
    def __add__(self, x):
        x = self.lift(x); return Quad(self.a+x.a, self.b+x.b, self.d)
    __radd__ = __add__
    def __neg__(self): return Quad(-self.a, -self.b, self.d)
    def __sub__(self, x): return self + -self.lift(x)
    def __rsub__(self, x): return self.lift(x) + -self
    def __mul__(self, x):
        x = self.lift(x)
        return Quad(self.a*x.a+self.d*self.b*x.b,
                    self.a*x.b+self.b*x.a, self.d)
    __rmul__ = __mul__
    def square(self):
        return Quad(self.a*self.a+self.d*self.b*self.b,
                    2*self.a*self.b, self.d)
    def __pow__(self, n):
        if n == 2: return self.square()
        if n == 0: return self.lift(1)
        out = self.lift(1)
        for _ in range(n): out = out*self
        return out
    def norm(self): return self.a*self.a-self.d*self.b*self.b


def norm4(x, d):
    """The exact product over all sixteen signs, valid over any Q-algebra."""
    a, b, c, e = d
    p, q = a*b, c*e
    u, v = a+b, c+e
    s = x**2-u-v
    k = s**2-4*u*v+4*(p+q)
    l = -4*(s+2*v)
    m = -4*(s+2*u)
    n = -8
    even = k**2+p*l**2-q*(m**2+p*n*n)
    odd = 2*k*l-2*q*m*n
    return even**2-p*odd**2


def norm5(x, d):
    xx = Quad(x, 1, d[4])
    lifted = [Quad(z, 0, d[4]) for z in d[:4]]
    ans = norm4(xx, lifted)
    return ans.norm()


def eval_expr(s, env):
    def visit(n):
        if isinstance(n, ast.Constant): return n.value
        if isinstance(n, ast.Name): return env[n.id]
        if isinstance(n, ast.UnaryOp): return -visit(n.operand)
        a, b = visit(n.left), visit(n.right)
        if isinstance(n.op, ast.Add): return a+b
        if isinstance(n.op, ast.Sub): return a-b
        if isinstance(n.op, ast.Mult): return a*b
        if isinstance(n.op, ast.Pow): return a**b
        raise ValueError(ast.dump(n))
    return visit(ast.parse(s, mode='eval').body)


def eval_dag(dag, inputs, ports, modulus):
    env = dict(ports); env.update(inputs)
    values = []
    def get(r):
        return (r[1] if r[0] == 'const' else
                env[r[1]] if r[0] == 'leaf' else values[r[1]]) % modulus
    for op, a, b in dag['nodes']:
        x, y = get(a), get(b)
        values.append((x+y if op == 'add' else x-y if op == 'sub' else x*y) % modulus)
    return get(dag['output'])


def compile_packet(packet):
    c = Circuit()
    env = {v: c.leaf(v) for v in packet['variables']+packet['fixed_numerals']}
    is13 = packet['variable_count'] == 13
    is14 = packet['variable_count'] == 14
    for name, value in packet['polynomial_abbreviations']:
        if (is13 or is14) and name.startswith('n') and name[1:].isdigit():
            break
        env[name] = eval_expr(value, env)
    if is13:
        out = norm5(env['carrier'], [env['rad'+str(i)] for i in range(5)])
    else:
        if is14:
            rows = [eval_expr(packet['factored_residuals'][0], env),
                    norm4(env['carrier'], [env['rad'+str(i)] for i in range(4)])]
        else:
            rows = [eval_expr(s, env) for s in packet['factored_residuals']]
        if packet['finalizer'] == 'sos':
            out = sum(r*r for r in rows)
        else:
            out = c.lift(1)
            for r in rows: out = out*(1+4*r)
            out = out-1
    dag = c.export(out, packet['variables'], packet['fixed_numerals'])
    dag.update({'name': packet['name']+'_compact', 'domain': packet['domain'],
                'exact_degree': packet['exact_degree'],
                'coefficient_binding': 'coefficients/BINDING.json',
                'source_packet': packet['name']+'.json',
                'norm_identity': 'Pair the first four radicals into two pairs; use the exact four-root norm, evaluated in the quadratic algebra of the fifth radical.'})
    return dag


if __name__ == '__main__':
    # First check the abstract formula against all sign combinations in a
    # finite multiquadratic algebra, using the independent checker when present.
    import itertools
    checks = 0
    for roots in itertools.product(range(-2, 3), repeat=5):
        d = [v*v for v in roots]
        x = sum(roots)+3
        expected = 1
        for signs in itertools.product((-1, 1), repeat=5):
            expected *= x+sum(a*b for a, b in zip(signs, roots))
        if norm5(x, d) != expected:
            raise ValueError(('norm identity', x, d))
        checks += 1
    c = Circuit()
    x = c.leaf('x')
    ds = [c.leaf('d'+str(i)) for i in range(5)]
    dag = c.export(norm5(x, ds), ['x']+['d'+str(i) for i in range(5)], [])
    (ROOT/'abstract_norm5_dag.json').write_text(json.dumps(dag, indent=2)+'\n')
    print(json.dumps({'finite_integer_factor_diagnostics': checks,
                      'generic_norm5_operations': dag['operations'],
                      'counts': dag['counts']}))
    metrics = {}
    for path in sorted(ROOT.glob('*.json')):
        try: packet = json.loads(path.read_text())
        except (ValueError, OSError): continue
        if not isinstance(packet, dict) or 'factored_residuals' not in packet:
            continue
        if not packet.get('name', '').startswith(('parity', 'centered')):
            continue
        built = compile_packet(packet)
        (ROOT/(packet['name']+'_dag.json')).write_text(json.dumps(built, indent=2)+'\n')
        metrics[packet['name']] = {k: built[k] for k in ('operations', 'counts', 'exact_degree')}
    (ROOT/'COMPACT_METRICS.json').write_text(json.dumps(metrics, indent=2)+'\n')
    print(json.dumps(metrics, indent=2))

# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent arithmetic checks for the newly emitted input-loader code.

Executes only our emitter and this independent checker, never upstream code.
No test claims to materialize complete Pell witnesses or the enormous unary
queue. Frozen recoder JSON is data, compared to independent kernel formulas.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import random
import input_loaders as loader
ROOT = Path(__file__).resolve().parent
LITERAL_PATH = ROOT.parent / 'input-research/literal/literal_tables.json'
INPUT_BASE = 1 << 50

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

class TestDAG:
    """Independent small DAG implementation of the agreed operand API."""

    def __init__(self):
        self.constants = []
        self.intern = {}
        self.inputs = {}
        self.nodes = []

    def recipe(self, op, *args):
        if op in ('add', 'sub', 'mul'):
            require(all((isinstance(a, int) and a < 0 for a in args)), 'a fixed constant recipe contains a nonconstant operand')
        else:
            require(op in ('int', 'pow2', 'geom4'), 'unsupported recipe')
            require(len(args) == 1 and isinstance(args[0], int), 'bad recipe')
            require(op == 'int' or args[0] >= 0, 'negative fixed exponent')
        row = (op,) + args
        if row not in self.intern:
            self.constants.append(row)
            self.intern[row] = -len(self.constants)
        return self.intern[row]

    def const(self, value):
        return self.recipe('int', value)

    def input(self, name, role='witness'):
        require(name not in self.inputs, 'duplicate input allocation')
        ref = INPUT_BASE + len(self.inputs)
        self.inputs[name] = ref
        return ref

    def _integer(self, ref, value):
        return ref < 0 and self.constants[-ref - 1] == ('int', value)

    def emit(self, op, a, b):
        if op == 'add':
            if self._integer(a, 0):
                return b
            if self._integer(b, 0):
                return a
        if op == 'sub' and self._integer(b, 0):
            return a
        if op == 'mul':
            if self._integer(a, 0) or self._integer(b, 0):
                return self.const(0)
            if self._integer(a, 1):
                return b
            if self._integer(b, 1):
                return a
        if a < 0 and b < 0:
            return self.recipe(op, a, b)
        self.nodes.append((op, a, b))
        return len(self.nodes) - 1

    def add(self, a, b):
        return self.emit('add', a, b)

    def sub(self, a, b):
        return self.emit('sub', a, b)

    def mul(self, a, b):
        return self.emit('mul', a, b)

    def power(self, base, exponent):
        require(exponent >= 0, 'bad power')
        if exponent == 0:
            return self.const(1)
        result = base
        for bit in bin(exponent)[3:]:
            result = self.mul(result, result)
            if bit == '1':
                result = self.mul(result, base)
        return result

    def total(self, values):
        values = list(values)
        if not values:
            return self.const(0)
        value = values[0]
        for x in values[1:]:
            value = self.add(value, x)
        return value

    def evaluate(self, values, modulus=None):
        env = {ref: values[name] for name, ref in self.inputs.items()}

        def reduce(x):
            return x if modulus is None else x % modulus
        for i, row in enumerate(self.constants):
            op, *args = row
            if op == 'int':
                out = args[0]
            elif op == 'pow2':
                out = 2 ** args[0] if modulus is None else pow(2, args[0], modulus)
            elif op == 'geom4':
                out = (4 ** args[0] - 1) // 3 if modulus is None else (pow(4, args[0], modulus) - 1) * pow(3, -1, modulus)
            else:
                a, b = (env[x] for x in args)
                out = a + b if op == 'add' else a - b if op == 'sub' else a * b
            env[-i - 1] = reduce(out)
        for i, (op, left, right) in enumerate(self.nodes):
            a, b = (env[left], env[right])
            env[i] = reduce(a + b if op == 'add' else a - b if op == 'sub' else a * b)
        return env

def kernel_residuals(v, prefix, q, r):
    """Ten raw Pell-kernel comparisons, independently assembled."""
    a, c, d, f, h, i, j, k, o, s, w, tau, eta, zeta, ga, y = (v[prefix + n] for n in ('a', 'c', 'd', 'f', 'h', 'i', 'j', 'k', 'o', 's', 'w', 'tau', 'eta', 'zeta', 'ga', 'y_aux'))
    W, Y = (w * q, s * q)
    U = W * Y
    D = a * a + 4 * a + 3
    ic2 = i * c * c
    H = j * c - 2 * r - 1
    return [(U * U + W) * (k * Y) ** 2 - tau * (tau + 1), c - k * Y - eta, k - eta - zeta, k - r - 1 - h * U, a - U - Y, d - W - c * a - ga * (4 * a + 3), d * d - D * c * c - 1, ic2 * ic2 - D * (f * f - 1), ic2 * ic2 * (H * H - y * y) - 1 + y * y, H - o * f + c]

def manual_recoder(v, width, modulus=None):
    """All 34 residuals without evaluating a source instruction list."""
    q, P, J, K, Ahat, z, x = (v[n] for n in ('q', 'P', 'J', 'K', 'Ahat', 'z', 'x'))
    Q = q ** width if modulus is None else pow(q, width, modulus)
    B = (2 ** (width - 1) if modulus is None else pow(2, width - 1, modulus)) * Q
    S = q * P
    out = [(B - 1) * J + 1 - P, (2 * B - 1) * K + 1 - S, x + v['input_slack'] - q, Ahat + Q - (Q - 1) * v['quotient_hat'] - z - 2, z + v['output_slack'] - Q]
    out += kernel_residuals(v, 'geo__', q, J)
    out += [v['geo__s'] - 2 * v['geo__odd_half'] - 1, J + v['geo__bound_beta'] - v['geo__w'] * q, B + v['geo__index_beta'] - J]
    qs = 16 * S
    F0, F1, F2 = (v[n] for n in ('and__F0', 'and__F1', 'and__F2'))
    F3 = 16 * Ahat - 8
    out += [v['and__r'] - F0 - qs * (F1 + qs * (F2 + qs * F3)), F0 + F1 + F2 + F3 + 1 - qs, v['and__s'] - 2 * v['and__odd_half'] - 1, v['and__r'] + v['and__bound_beta'] - v['and__w'] * qs]
    out += kernel_residuals(v, 'and__', qs, v['and__r'])
    out += [F1 + F3 - 16 * x * J - 12, F2 + F3 - 16 * K - 10]
    require(len(out) == 34, 'manual comparison count')
    return out if modulus is None else [x % modulus for x in out]

def literal_E(size, y):
    a = 28 * (size + 1)
    bits = [0] * (14 * y + 7) + [0] + [1, 0] * (a - 3) + [0] + [1, 0] * 7 + [0] + [1, 0] * (a - 4) + [0] * (3 * a - 14 * y - 10)
    require(len(bits) == 7 * a, 'literal E width')
    value = sum((bit << i for i, bit in enumerate(bits)))
    return (value, len(bits))

def graph_checks(dag, packet):
    roots = [ref for pair in packet['residuals'] for ref in pair]
    roots += [packet['X'], packet['target_width']]
    used = set()
    todo = list(roots)
    while todo:
        node = todo.pop()
        if 0 <= node < INPUT_BASE and node not in used:
            used.add(node)
            todo.extend(dag.nodes[node][1:])
    require(used == set(range(len(dag.nodes))), 'unused paid input-loader gates')
    counts = Counter((row[0] for row in dag.nodes))
    require(counts == {'mul': 173, 'add': 108, 'sub': 29}, 'exact input-loader gate census ' + str(counts))
    require(len(dag.inputs) == 112, 'input count')
    a = packet['namespaces'][loader.CANONICAL_NS]['auxiliaries']
    b = packet['namespaces'][loader.EXPONENT_NS]['auxiliaries']
    require(len(a) == len(b) == 49 and (not set(a.values()) & set(b.values())), 'namespace collision')
    require(len(set(dag.inputs.values())) == 112, 'input alias')
    require(len(packet['residuals']) == 75, 'comparison count')
    return dict(operations=len(dag.nodes), multiplications=counts['mul'], additions=counts['add'], subtractions=counts['sub'], comparisons=75, positive_existentials=106, external_positive_ports=6, native_width_binding_comparison_not_included=True, all_paid_gates_reachable=True)

def backend_check(lit, exact_V):
    from compact_dag import DAG, MAGIC, ROW, INPUT_BASE as NATIVE_INPUT_BASE
    path = ROOT / 'input_backend_probe.cdag'
    d = DAG(path)
    p = loader.build(d, lit)
    require(len(d.degrees) == 310 and d.counts == {'*': 173, '+': 108, '-': 29}, 'actual compact backend loader ledger')
    require(d.input_count == 112 and d.input_roles.get('external') == 6 and (d.input_roles.get('witness') == 106), 'backend roles/domains')
    require(d.pool.value_exact(p['literal']['V']) == exact_V, 'backend fixed V numeral')
    require(max((max(d._degree(a), d._degree(b)) for a, b in p['residuals'])) == 397489, 'loader residual structural degree')
    residuals = [d.sub(a, b) for a, b in p['residuals']]
    diagnostic = d.total([d.mul(r, r) for r in residuals] + [d.mul(p['target_width'], p['target_width'])])
    manifest = d.finish(diagnostic, {'purpose': 'Diagnostic reachability only; not the finalizer or a claimed zero relation', 'loader_operations_before_diagnostic': 310})
    return {'loader_operations': 310, 'loader_multiplications': 173, 'loader_additions': 108, 'loader_subtractions': 29, 'loader_max_comparison_degree_upper': 397489, 'all_loader_gates_and_inputs_live': manifest['ledger']['all_gates_live'] and manifest['ledger']['all_inputs_live'], 'fixed_V_exactly_matches_independent_literal': True, 'probe_source_sha256': manifest['source_sha256']}

def run():
    rng = random.Random(130397488)
    recoder_cases = 0
    for width in (4, 5, 8, 16, 24, 32):
        d = TestDAG()
        x = d.input('x')
        z = d.input('z')
        p = loader.build_recoder(d, width, 'test', x, z)
        for case in range(128):
            values = {name: rng.randrange(1, 8) if case < 64 else rng.randrange(-4, 5) for name in d.inputs}
            env = d.evaluate(values)
            supplied = {name: values['test__' + name] for name in p['auxiliaries']}
            supplied.update(x=values['x'], z=values['z'])
            require([env[a] - env[b] for a, b in p['residuals']] == manual_recoder(supplied, width), 'recoder full residual identity')
            recoder_cases += 1
    lit = json.loads(LITERAL_PATH.read_text())
    dag = TestDAG()
    p = loader.build(dag, lit)
    ledger = graph_checks(dag, p)
    left, b = literal_E(1013, 300)
    right, b2 = literal_E(1013, 539)
    require(b == b2 == 198744, 'literal input widths')
    env = dag.evaluate({name: 1 for name in dag.inputs}, modulus=1000000007)
    require(env[p['literal']['V']] == (left + (right << b)) % 1000000007, 'actual fixed V literal/recipe mismatch')
    V = left + (right << b)
    require(0 < 3 * V < 2 ** (2 * b), 'actual repeated E pair strong cone')
    composition_cases = 0
    for modulus in (1000000007, 1000000009, 998244353):
        for case in range(64):
            values = {name: rng.randrange(1, 10) if case < 32 else rng.randrange(-4, 5) for name in dag.inputs}
            env = dag.evaluate(values, modulus)
            aux = lambda ns: {name: values[ns + '__' + name] for name in p['namespaces'][ns]['auxiliaries']}
            c = aux(loader.CANONICAL_NS)
            c.update(x=values['x'] + 1, z=values[loader.CANONICAL_NS + '__spread'])
            e = aux(loader.EXPONENT_NS)
            e.update(x=1, z=1)
            Q0 = pow(c['q'], 32, modulus)
            Q1 = pow(e['q'], 397488, modulus)
            B1 = pow(2, 397487, modulus) * Q1
            N, T, X, ell, v, g, beta = (values['input_loader__' + n] for n in ('N', 'T', 'X', 'ell', 'v', 'g', 'canonical_beta'))
            a, ps, s, C, L = (values[n] for n in ('a_e', 'p_e', 's_e', 'C_e', 'L_e'))
            m = 2 ** 32 - 1
            K = pow(2, 397488, modulus)
            expected = manual_recoder(c, 32, modulus)
            expected += [c['input_slack'] + beta - c['x'] - 1, m * N - m * a - ps * 3941247658 * (Q0 - 1) - ps * m * -4194240 * c['z'] - ps * m * s * Q0]
            expected += manual_recoder(e, 397488, modulus)
            expected += [(B1 - 1) * v + ell - e['J'], ell + g - B1 + 1, ell - N - 1, K * T - Q1, (K - 1) * X - (K - 1) * C - L * (V % modulus) * (T - 1)]
            actual = [(env[a] - env[b]) % modulus for a, b in p['residuals']]
            require(actual == [x % modulus for x in expected], 'full composition residual mismatch')
            require(env[p['target_width']] == L * T % modulus, 'exact target-width port')
            composition_cases += 1
    canonical_cases = 0
    exponent_cases = 0
    loader_cases = 0
    for u in range(2, 1025):
        n = u.bit_length()
        q = 2 ** n
        slack = q - u
        beta = 2 * u + 1 - q
        require(slack > 0 and beta > 0 and (slack + beta == u + 1), 'canonical boundary')
        for n2 in (max(2, n - 1), n, n + 1):
            valid = 2 ** n2 - u > 0 and 2 * u + 1 - 2 ** n2 > 0
            require(valid == (n2 == n), 'canonical uniqueness')
        canonical_cases += 1
    for width in (4, 5, 8, 32):
        for N in range(1, 33):
            h = N + 1
            q = 2 ** h
            Q = q ** width
            B = 2 ** (width - 1) * Q
            J = sum((B ** i for i in range(h)))
            v = (J - h) // (B - 1)
            g = B - 1 - h
            require(v > 0 and g > 0 and ((B - 1) * v + h == J), 'positive exponent extraction')
            require(1 <= h <= B - 2 and Q == (2 ** width) ** (N + 1), 'alias-free scale')
            exponent_cases += 1
    for size in (2, 3, 5):
        a, b = literal_E(size, 0)
        v, w = literal_E(size, 1)
        K = 2 ** (2 * b)
        Vsmall = v + (a << b)
        for repeat in range(1, 9):
            prefix = a + (v << b)
            L = 2 ** (2 * b)
            T = K ** repeat
            X = prefix + L * sum((Vsmall * K ** j for j in range(repeat)))
            require((K - 1) * X == (K - 1) * prefix + L * Vsmall * (T - 1), 'unary exact value')
            require(0 < 3 * X < L * T, 'unary strong cone')
            loader_cases += 1
    backend = backend_check(lit, V)
    literal_hash = hashlib.sha256(LITERAL_PATH.read_bytes()).hexdigest()
    return {'status': 'PASS_INPUT_LOADERS', 'ledger': ledger, 'compact_backend': backend, 'full_recoder_residual_identity_cases': recoder_cases, 'full_composition_modular_identity_cases': composition_cases, 'canonical_boundary_cases': canonical_cases, 'positive_exponent_extraction_cases': exponent_cases, 'literal_unary_value_width_cases': loader_cases, 'actual_literal_E_pair_checked': True, 'actual_E_pair_bit_length': V.bit_length(), 'literal_tables_sha256': literal_hash, 'recoder_receipt_sha256': loader.RECEIPT_SHA256, 'full_Pell_witnesses_materialized': False, 'unary_universal_input_materialized': False}
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = run()
    path = ROOT / 'input_validation.json'
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n')
    else:
        require(json.loads(path.read_text()) == result, 'validation receipt mismatch')
    print(json.dumps(result, indent=2))

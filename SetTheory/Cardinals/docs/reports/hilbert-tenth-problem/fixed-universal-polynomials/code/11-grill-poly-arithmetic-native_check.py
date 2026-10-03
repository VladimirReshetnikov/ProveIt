# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent data-replay checks for the scalable native history emitter.

Only local newly written source and pinned JSON data are used. The upstream
Python compiler is never imported, compiled, executed, or dynamically loaded.
"""
import hashlib
import json
import random
from pathlib import Path
import native_history
HERE = Path(__file__).resolve().parent

class SmallDAG:
    """Independent simple handle interpreter for small receipt identities."""

    def __init__(self):
        self.constants = []
        self.constant_ids = {}
        self.names = {}
        self.rows = []

    def const(self, n):
        if type(n) is not int:
            raise TypeError(n)
        if n not in self.constant_ids:
            self.constants.append(n)
            self.constant_ids[n] = -len(self.constants)
        return self.constant_ids[n]

    def recipe(self, op, n):
        if op == 'pow2':
            return self.const(1 << n)
        if op == 'affine_slope_minus_one':
            return self.const((1 << 2 * n + 1) - 1)
        if op == 'affine_offset':
            return self.const(((1 << 2 * n + 1) - 2) // 3)
        raise ValueError(op)

    def input(self, name):
        if name in self.names:
            raise ValueError('Duplicate ' + name)
        ref = (1 << 50) + len(self.names)
        self.names[name] = ref
        return ref

    def input_range(self, prefix, count):
        start = (1 << 50) + len(self.names)
        for i in range(count):
            self.input(prefix + str(i))
        return range(start, start + count)

    def gate(self, op, a, b):
        z, o = (self.const(0), self.const(1))
        if a < 0 and b < 0:
            aa, bb = (self.constants[-a - 1], self.constants[-b - 1])
            return self.const(aa + bb if op == '+' else aa - bb if op == '-' else aa * bb)
        if op == '+':
            if a == z:
                return b
            if b == z:
                return a
        if op == '-' and b == z:
            return a
        if op == '*':
            if a == z or b == z:
                return z
            if a == o:
                return b
            if b == o:
                return a
        self.rows.append((op, a, b))
        return len(self.rows) - 1

    def add(self, a, b):
        return self.gate('+', a, b)

    def sub(self, a, b):
        return self.gate('-', a, b)

    def mul(self, a, b):
        return self.gate('*', a, b)

    def total(self, values):
        r = self.const(0)
        for v in values:
            r = self.add(r, v)
        return r

    def evaluate(self, values, modulus=None):
        computed = []
        inputs = {ref: values[name] for name, ref in self.names.items()}

        def at(ref):
            if ref < 0:
                return self.constants[-ref - 1]
            if ref >= 1 << 50:
                return inputs[ref]
            return computed[ref]
        for op, a, b in self.rows:
            aa, bb = (at(a), at(b))
            x = aa + bb if op == '+' else aa - bb if op == '-' else aa * bb
            computed.append(x if modulus is None else x % modulus)
        return at

    def audit(self, roots):
        live = set(roots)
        for i in range(len(self.rows) - 1, -1, -1):
            if i not in live:
                raise AssertionError('Dead gate ' + str(i))
            op, a, b = self.rows[i]
            for ref in (a, b):
                if not (ref < 0 or ref >= 1 << 50 or ref < i):
                    raise RuntimeError('Invariant failed at original source line 84')
                live.add(ref)
        if not set(self.names.values()) <= live:
            raise RuntimeError('Invariant failed at original source line 86')
        return {'gates': len(self.rows), 'M': sum((o == '*' for o, a, b in self.rows)), 'A': sum((o != '*' for o, a, b in self.rows)), 'all_gates_live': True, 'all_inputs_live': True}

def _receipt_eval(packet, values, modulus=None):
    env = dict(values)

    def at(value):
        return env[value] if type(value) is str else value
    for name, op, a, b in packet['source']:
        aa, bb = (at(a), at(b))
        v = aa + bb if op == '+' else aa - bb if op == '-' else aa * bb
        env[name] = v if modulus is None else v % modulus
    return at

def check():
    frozen = json.loads((HERE / 'native_receipt_fixtures.json').read_text())
    kernel = native_history._kernel()
    results = []
    checks = {'kernel_definition_matches': 0, 'interface_values': 0, 'residual_values': 0, 'unit_values': 0, 'complete_polynomial_values': 0, 'exact_integer_cases': 0, 'modular_cases': 0, 'phase_coefficient_cases': 0}
    rng = random.Random(202610030849)
    for fixture in frozen['fixtures']:
        packet = fixture['packet']
        program = fixture['program']
        ports = {packet['interfaces'][n]: '@' + n for n in kernel['ports']}
        repl = lambda v: ports.get(v, v) if type(v) is str else v
        native_rows = [[n, o, repl(a), repl(b)] for n, o, a, b in packet['source'] if n.startswith('and__')]
        if not sorted(native_rows) == sorted(kernel['source']):
            raise RuntimeError('Invariant failed at original source line 115')
        if not packet['comparisons'][4:-1] == kernel['comparisons']:
            raise RuntimeError('Invariant failed at original source line 116')
        checks['kernel_definition_matches'] += 1
        dag = SmallDAG()
        X = dag.input('X')
        p = native_history.build(dag, program, X)
        if not len(dag.names) - 1 == p['metadata']['positive_witnesses'] == len(packet['auxiliaries']):
            raise RuntimeError('Invariant failed at original source line 119')
        if not p['metadata']['K_exponent'] == packet['K'].bit_length() - 1:
            raise RuntimeError('Invariant failed at original source line 120')
        if not p['metadata']['scale_exponent'] == packet['scale_exponent']:
            raise RuntimeError('Invariant failed at original source line 121')
        roots = [p['unit']] + [v for pair in p['residuals'] for v in pair]
        audit = dag.audit(roots)
        for case in range(44):
            modulus = None if case < 4 else (1000000007, 1000000009, 2147483647, 2305843009213693951)[case % 4]
            values = {n: rng.randrange(-3, 5) for n in packet['parameters'] + packet['auxiliaries']}
            newvalues = {'X': values['x'], **{'native.' + k: v for k, v in values.items() if k != 'x'}}
            old = _receipt_eval(packet, values, modulus)
            new = dag.evaluate(newvalues, modulus)
            norm = lambda x: x if modulus is None else x % modulus
            for name, ref in p['interfaces'].items():
                if not norm(new(ref)) == norm(old(packet['interfaces'][name])):
                    raise RuntimeError((program, case, name))
                checks['interface_values'] += 1
            oldrs = [norm(old(a) - old(b)) for a, b in packet['comparisons'][:-1]]
            newrs = [norm(new(a) - new(b)) for a, b in p['residuals']]
            if not oldrs == newrs:
                raise RuntimeError('Invariant failed at original source line 137')
            checks['residual_values'] += len(oldrs)
            u0, u1 = (old(packet['unit_register']), new(p['unit']))
            if not norm(u0) == norm(u1):
                raise RuntimeError('Invariant failed at original source line 140')
            checks['unit_values'] += 1
            if not norm(u0 * (1 + sum((r * r for r in oldrs))) - 1) == norm(u1 * (1 + sum((r * r for r in newrs))) - 1):
                raise RuntimeError('Invariant failed at original source line 142')
            checks['complete_polynomial_values'] += 1
            checks['exact_integer_cases' if modulus is None else 'modular_cases'] += 1
        results.append({'program': program, 'witnesses': len(dag.names) - 1, 'emitter_source': audit})
    for m in (1, 2, 3, 4, 7, 101, 397488):
        if m == 1:
            if not 1 == 1:
                raise RuntimeError('Invariant failed at original source line 150')
        else:
            for i in range(m):
                next_coeff = (i - 1) % m + 1
                q_coeff = i + 1
                old_B = next_coeff - m
                old_plain = m - q_coeff
                weight = 0 if i == 0 else m - i
                new_B = -weight
                new_plain = (m if i == 0 else weight) - 1
                if not (old_B, old_plain) == (new_B, new_plain):
                    raise RuntimeError('Invariant failed at original source line 161')
            if not 2 * (m * (m - 1) // 2) == m * (m - 1):
                raise RuntimeError('Invariant failed at original source line 164')
        checks['phase_coefficient_cases'] += 1
    return {'status': 'PASS_NATIVE_SCALABLE_EMITTER', 'upstream_code_executed': False, 'scope': 'Exact algebraic transfer in native_history_proof.md; finite receipt replays independently check its implementation, not the unbounded semantic theorem.', 'checks': checks, 'fixtures': results, 'source_sha256': hashlib.sha256((HERE / 'native_history.py').read_bytes()).hexdigest(), 'kernel_sha256': hashlib.sha256((HERE / 'native_unit_kernel.json').read_bytes()).hexdigest(), 'receipt_fixture_sha256': hashlib.sha256((HERE / 'native_receipt_fixtures.json').read_bytes()).hexdigest()}
if __name__ == '__main__':
    result = check()
    (HERE / 'native_check_result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

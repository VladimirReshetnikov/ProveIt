"""Finite, stdlib-only audit of one polynomial-preserving output-DAG rewrite."""
from pathlib import Path
import hashlib, json, os, re

def require(condition, message='audit requirement failed'):
    if not condition:
        raise RuntimeError(message)
D = Path(__file__).resolve().parents[2]
P = D / 'candidates/free-j-polarized-positive/source/positive/p13_free_J.json'
W = Path(__file__).resolve().parent
OUT = Path(os.environ.get('ADAPTIVE_FACTOR87_OUT', str(W)))
OUT.mkdir(parents=True, exist_ok=True)
h = lambda b: hashlib.sha256(b).hexdigest()
raw = P.read_bytes()
require(h(raw) == 'a6c378ffe706da6ccb17250c31183b0cbff7bdd2c21b85cf0fc393a73bd987b8')
p = json.loads(raw)
rows = p['source']
require(len(rows) == 88 and p['output'] == 'P13')
syntax = D / 'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean'
native = D / 'Lean/DiophantineConsistency/NativeAdaptiveGraph.lean'
def gate_rows(text):
    result = []
    for line in text.splitlines():
        m = re.fullmatch(r'\s*let (\w+) := (\w+) ([*+\-]) (\w+)\s*', line)
        if m:
            n, a, op, b = m.groups()
            result.append([n, op, int(a) if a.isdecimal() else a,
                           int(b) if b.isdecimal() else b])
    return result
syntax_body = syntax.read_text().split('def expressionAt', 1)[1].split('\ndef expression :', 1)[0]
native_body = native.read_text().split('-- BEGIN LITERAL GRAPH', 1)[1].split('-- END LITERAL GRAPH', 1)[0]
require(gate_rows(syntax_body) == rows, 'actual adaptive syntax gate schedule differs')
require(gate_rows(native_body) == rows, 'actual native graph gate schedule differs')
old = [['g22', '*', 'k', 'qm'], ['W', '+', 1, 'g22'], ['M', '*', 'q3', 'qm'], ['g25', '*', 'K0', 'q'], ['g26', '+', 'X', 'g25'], ['g27', '*', 'C', 'g26'], ['g28', '*', 'F', 'q'], ['Bt', '-', 'g27', 'g28'], ['g30', '+', 'ell', 'k'], ['g31', '+', 'g30', 'r'], ['g32', '*', 'M', 'g31'], ['g33', '*', 'Y', 'qm'], ['g34', '+', 'g32', 'g33'], ['g35', '*', 'W', 'q3'], ['g36', '*', 'Bt', 'g35'], ['Z', '-', 'g34', 'g36']]
new = [['M', '*', 'q3', 'qm'], ['g25', '*', 'K0', 'q'], ['g26', '+', 'X', 'g25'], ['g27', '*', 'C', 'g26'], ['g28', '*', 'F', 'q'], ['Bt', '-', 'g27', 'g28'], ['g30', '+', 'ell', 'k'], ['g31', '+', 'g30', 'r'], ['root_skew', '*', 'k', 'Bt'], ['root_inner', '-', 'g31', 'root_skew'], ['root_scaled', '*', 'M', 'root_inner'], ['g33', '*', 'Y', 'qm'], ['root_btq3', '*', 'Bt', 'q3'], ['root_sum', '+', 'root_scaled', 'g33'], ['Z', '-', 'root_sum', 'root_btq3']]
indices = [i for i in range(len(rows) - len(old) + 1) if rows[i:i + len(old)] == old]
require(len(indices) == 1)
idx = indices[0]
child = rows[:idx] + new + rows[idx + len(old):]
require(len(child) == 87)
inputs = p['witnesses']
ports = p['fixed_numerals']
known = set(inputs + ports)
require(len(known) == 17)
for n, op, a, b in child:
    require(n not in known and op in ('+', '-', '*'))
    for x in (a, b):
        require(isinstance(x, int) or x in known)
    known.add(n)
producers = {r[0]: r for r in child}
live = {'P13'}
pending = ['P13']
while pending:
    n = pending.pop()
    if n in producers:
        for x in producers[n][2:]:
            if isinstance(x, str) and x not in live:
                live.add(x)
                pending.append(x)
require(all((r[0] in live for r in child)))
require(all((x in live for x in inputs + ports)))
count = {op: sum((r[1] == op for r in child)) for op in ('*', '+', '-')}
require(count == {'*': 47, '+': 22, '-': 18})
N = 6
zero = (0,) * N
var = lambda i: {tuple((int(j == i) for j in range(N))): 1}

def add(a, b):
    z = dict(a)
    for e, c in b.items():
        z[e] = z.get(e, 0) + c
    return {e: c for e, c in z.items() if c}

def neg(a):
    return {e: -c for e, c in a.items()}

def sub(a, b):
    return add(a, neg(b))

def mul(a, b):
    z = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            e = tuple((x + y for x, y in zip(ea, eb)))
            z[e] = z.get(e, 0) + ca * cb
    return {e: c for e, c in z.items() if c}
q3, qm, k, bt, g, y = map(var, range(6))
one = {zero: 1}
M = mul(q3, qm)
left = sub(add(mul(M, g), mul(y, qm)), mul(bt, mul(add(one, mul(k, qm)), q3)))
right = sub(add(mul(M, sub(g, mul(k, bt))), mul(y, qm)), mul(bt, q3))
require(left == right)
def eval_root(circuit):
    # Treat Bt and g31 as formal cut inputs and evaluate the actual gate rows.
    env = dict(zip(['q3', 'qm', 'k', 'Bt', 'g31', 'Y'], [q3, qm, k, bt, g, y]))
    for name, op, a, b in circuit:
        if name in env:
            continue
        left_value = {zero: a} if isinstance(a, int) else env.get(a)
        right_value = {zero: b} if isinstance(b, int) else env.get(b)
        if left_value is not None and right_value is not None:
            env[name] = {'+': add, '-': sub, '*': mul}[op](left_value, right_value)
    require('Z' in env, 'root cut did not evaluate')
    return env['Z']
require(eval_root(rows) == left, 'parent root gates differ from formal identity')
require(eval_root(child) == right, 'candidate root gates differ from formal identity')
wrong = add(add(mul(M, sub(g, mul(k, bt))), mul(y, qm)), mul(bt, q3))
require(left != wrong)
mutated = [list(row) for row in child]
next(row for row in mutated if row[0] == 'Z')[1] = '+'
require(eval_root(mutated) != left, 'mutated candidate root was not rejected')
out = {'name': 'adaptive-positive13-first-root-factor87', 'scope': 'output-only graph: exact local integer-polynomial identity, unchanged surrounding gates and finite topology/liveness/count; no HA proof, fixed-port calibration, converse, global minimum, or new exact-degree audit', 'parent_sha256': h(raw), 'witnesses': inputs, 'fixed_numerals': ports, 'source': child, 'output': 'P13', 'operations': 87, 'operation_breakdown': count, 'degree': 'same polynomial as parent; parent degree metadata not independently checked', 'rewrite_offset': idx, 'removed_rows': old, 'replacement_rows': new, 'retained_source_rows_equal': True, 'local_formal_monomials': len(left), 'mutated_sign_rejected': True}
payload = (json.dumps(out, indent=2) + '\n').encode()
(OUT / 'candidate.json').write_bytes(payload)
receipt = {'status': 'PASS', 'parent_sha256': h(raw), 'candidate_sha256': h(payload), 'auditor_sha256': h(Path(__file__).read_bytes()), 'syntax_sha256': h(syntax.read_bytes()), 'native_sha256': h(native.read_bytes()), 'operations': 87, 'operation_breakdown': count, 'live_inputs': len(inputs), 'live_ports': len(ports), 'live_gates': 87, 'actual_parent_and_candidate_root_gates_checked': True, 'local_formal_monomials': len(left), 'mutated_sign_rejected': True, 'scope': out['scope']}
(OUT / 'AUDIT.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))

#!/usr/bin/env python3
"""Independent complete alias remap, sparse-ring norm and actual degree controls."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT_SHA = '327296a42616d5646502e9487075be32fe14402dbbad5b2925c8d8ff2718a371'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(raw):
    return sha256(raw).hexdigest()


def evaluate(rows, inputs, prime=None):
    env = dict(inputs)
    def val(x):
        return x if type(x) is int else env[x]
    for name, op, a, b in rows:
        u, v = val(a), val(b)
        need(op in ('+', '-', '*'), 'binary arithmetic operation')
        out = u+v if op == '+' else u-v if op == '-' else u*v
        env[name] = out if prime is None else out % prime
    return env


def verify_remap(parent, child, remap):
    """Check every hypothesis of the unbounded gate-order induction."""
    old, new = parent['source'], child['source']
    alias = remap['alias']
    deleted = alias['deleted_index']
    need(remap['parent_sha256'] == child['parent_sha256'] == PARENT_SHA,
         'same complete parent')
    need(alias['deleted_register'] == 'qm1' and alias['retained_register'] == 'bJ',
         'exact eliminated alias')
    need(old[deleted] == alias['old_definition'] == ['qm1', '-', 'q', 1],
         'exact removed subtraction')
    need([r for r in old[:deleted] if r[0] == 'q'] ==
         [alias['premise']] == [['q', '+', 'bJ', 1]], 'earlier exact q=bJ+1')
    need([r for r in old[:deleted] if r[0] == 'bJ'] == [['bJ', '*', 'beta', 'J']],
         'retained product already available')
    retained = remap['retained_gates']
    need([r['parent_index'] for r in retained] ==
         [i for i in range(len(old)) if i != deleted], 'complete parent coverage')
    need([r['child_index'] for r in retained] == list(range(len(new))),
         'complete ordered child coverage')
    for entry in retained:
        i, j = entry['parent_index'], entry['child_index']
        name, op, a, b = old[i]
        a = 'bJ' if a == 'qm1' else a
        b = 'bJ' if b == 'qm1' else b
        need(new[j] == [name, op, a, b] and entry['register'] == name,
             'every retained gate is exactly the advertised operand substitution')
    need(all('qm1' not in row for row in new), 'no deleted value remains referenced')
    return retained


def line_degree(values, prime):
    order = -1
    level = 0
    values = list(values)
    while values:
        if values[0]:
            order = level
        values = [(b-a) % prime for a, b in zip(values, values[1:])]
        level += 1
    return order


def main():
    parent_raw = (HERE/'source/parent-equation.json').read_bytes()
    need(digest(parent_raw) == PARENT_SHA, 'exact frozen123-operation parent')
    parent = json.loads(parent_raw)
    child = load(HERE/'equation.json')
    remap = load(HERE/'PREFIX_REMAP.json')
    retained = verify_remap(parent, child, remap)
    need(child['domain'] == parent['domain'] == 'strictly positive integers',
         'unchanged positive domain')
    need(child['witnesses'] == parent['witnesses'] and
         len(set(child['witnesses'])) == 10, 'all ten unchanged witnesses')
    need(child['fixed_numerals'] == parent['fixed_numerals'] ==
         ['beta', 'K0', 'MC', 'MF'], 'whole unchanged fixed tuple')
    need(child['output'] == parent['output'] == 'N', 'same final output')
    provenance = load(HERE/'PROVENANCE.json')
    need(provenance['parent_equation_sha256'] == PARENT_SHA, 'parent provenance pin')

    # This copied peer helper contains an independently written sparse-ring
    # oracle. Its main() is not called; no author builder/verifier is imported.
    oracle_path = HERE/'source/independent_norm_oracle.py'
    need(digest(oracle_path.read_bytes()) == provenance['oracle_sha256'],
         'independent sparse-ring oracle pin')
    spec = importlib.util.spec_from_file_location('independent_sparse_ring_oracle', oracle_path)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    u = oracle.variable(0)
    need(((u+1)-1).t == u.t, 'universal additive cancellation over Z')
    need(((u+1)+1).t != u.t, 'wrong subtraction polarity rejected algebraically')

    rows = child['source']
    available = set(child['witnesses']+child['fixed_numerals'])
    need(len(available) == 14, 'distinct witnesses and ports')
    degrees = {v:1 for v in child['witnesses']} | {v:0 for v in child['fixed_numerals']}
    dependencies = {}
    for name, op, a, b in rows:
        need(name not in available and op in ('+', '-', '*'), 'fresh arithmetic gate')
        need(all(type(x) is int or x in available for x in (a, b)), 'topological circuit')
        available.add(name)
        dependencies[name] = (a, b)
        da, db = (0 if type(x) is int else degrees[x] for x in (a, b))
        degrees[name] = da+db if op == '*' else max(da, db)
    live, todo = set(), ['N']
    while todo:
        x = todo.pop()
        if type(x) is int or x in live:
            continue
        live.add(x)
        todo.extend(dependencies.get(x, ()))
    need(live == available, 'every gate, unknown and fixed port live')
    counts = Counter(r[1] for r in rows)
    need(len(rows) == child['operations'] == 122 and
         dict(counts) == child['operation_breakdown'] == {'*':73, '+':30, '-':19},
         'actual122-operation census')
    need(degrees['N'] == child['syntactic_degree'] == parent['syntactic_degree'] == 928,
         'unchanged syntactic degree928')
    need(all(degrees[name] == degree for name, degree in child['register_degrees'].items()),
         'every stated register degree')
    need(child['exact_degree'] == parent['exact_degree'] == 816,
         'unchanged exact degree claim')

    x, a, b, c, d, omega = [oracle.variable(i) for i in range(6)]
    start = next(i for i, row in enumerate(rows) if row[0] == 'ab')
    tail = rows[start:]
    need(tail == parent['source'][-28:] and len(tail) == 28,
         'whole sixteen-root norm tail unchanged')
    norm = oracle.evaluate(tail, dict(fs=x*x, fa=a, fb=b, fc=c, fd=d))['N']
    need(norm.t == oracle.norm_oracle(x, [a, b, c, d]).t,
         'literal tail equals independent product of all16 conjugates')
    centered = oracle.evaluate(tail, dict(fs=x*x, fa=a, fb=b, fc=x*x-omega, fd=d))['N']
    weights = (58, 78, 84, 0, 64, 102)
    weighted = {m:sum(e*w for e, w in zip(m, weights)) for m in centered.t}
    top = {m:centered.t[m] for m, w in weighted.items() if w == max(weighted.values())}
    need(max(weighted.values()) == 816 and top == {(0,0,0,0,0,8):1},
         'unique weight816 term is omega^8 with coefficient1')

    coefficients, coefficient_pins = {}, {}
    need(child['coefficient_binding'] == parent['coefficient_binding'] ==
         load(HERE/'coefficients/BINDING.json'), 'whole binding unchanged')
    for name, pin in child['coefficient_binding']['ports'].items():
        blob = (HERE/'coefficients'/pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'],
             'complete authentic fixed payload '+name)
        coefficients[name] = int.from_bytes(raw, 'little')
        need(coefficients[name].bit_length() == pin['bits'], 'actual coefficient width')
        coefficient_pins[name] = dict(raw_sha256=digest(raw), bits=pin['bits'])
    need(coefficients['beta'] == 2**590069-1 > 0, 'nonzero actual beta')

    rng = random.Random(122816)
    diagnostics = 0
    for prime in (1009, (1 << 127)-1):
        for _ in range(50):
            inputs = {name:rng.randrange(-20, 21) for name in child['witnesses']}
            inputs.update({name:value % prime for name, value in coefficients.items()})
            want, have = evaluate(parent['source'], inputs, prime), evaluate(rows, inputs, prime)
            need(want['qm1'] == have['bJ'] and
                 all(want[r['register']] == have[r['register']] for r in retained),
                 'all retained registers and the deleted alias agree at actual tuple')
            diagnostics += 1
    free_port_diagnostics = 0
    for _ in range(50):
        # Small signed free ports: this controls the circuit independently of
        # the numerical coefficient specialization. Exact proof is above.
        inputs = {name:rng.randrange(-3, 4) for name in child['witnesses']+child['fixed_numerals']}
        want, have = evaluate(parent['source'], inputs), evaluate(rows, inputs)
        need(want['qm1'] == have['bJ'] and
             all(want[r['register']] == have[r['register']] for r in retained),
             'all retained registers agree over signed free ports')
        free_port_diagnostics += 1
    slices = []
    for prime in ((1 << 127)-1, (1 << 89)-1):
        direction = {name:rng.randrange(1, prime) for name in child['witnesses']}
        base = {name:rng.randrange(1, prime) for name in child['witnesses']}
        inputs = {name:value % prime for name, value in coefficients.items()}
        values = []
        for t in range(930):
            env = inputs | {name:(base[name]+t*direction[name]) % prime for name in child['witnesses']}
            values.append(evaluate(rows, env, prime)['N'])
        degree = line_degree(values, prime)
        need(degree == 816, 'whole actual-tuple circuit line attains degree816')
        slices.append(dict(prime_bits=prime.bit_length(), degree=degree))

    controls = []
    wrong_operand = deepcopy(child)
    i = next(i for i, r in enumerate(rows) if r[0] == 'G1')
    wrong_operand['source'][i][2] = 'q'
    cases = [('wrong_retained_operand', parent, wrong_operand, remap)]
    wrong_definition = deepcopy(parent)
    i = next(i for i, r in enumerate(parent['source']) if r[0] == 'q')
    wrong_definition['source'][i][3] = 2
    cases.append(('wrong_alias_definition', wrong_definition, child, remap))
    missing_gate = deepcopy(remap)
    missing_gate['retained_gates'].pop()
    cases.append(('missing_prefix_gate', parent, child, missing_gate))
    for label, p, q, r in cases:
        try:
            verify_remap(p, q, r)
        except ValueError:
            controls.append(label)
        else:
            raise ValueError('corrupted remap unexpectedly accepted: '+label)
    bad_local = evaluate([['bad', '+', 'q', 1]], {'q':u+1})['bad']
    need(bad_local.t != u.t, 'corrupted local operation actually evaluated and rejected')
    controls.append('wrong_subtraction_polarity')

    for path, pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/path).read_bytes()) == pin, 'generated artifact seal '+path)
    for path in ('parent-check.json', 'parent-check-optimized.json'):
        receipt = load(HERE/'source'/path)
        need(receipt['status'] == 'PASS' and receipt['equation_sha256'] == PARENT_SHA,
             'frozen123-operation parent receipt '+path)
    inherited = load(HERE/'source/original-replays.json')
    need(inherited['status'] == 'PASS' and inherited['source_unchanged'] and
         all(r['exit_code'] == 0 for r in inherited['replays']),
         'complete original parent normal/-O replay receipts')

    report = dict(status='PASS', optimized_python=bool(sys.flags.optimize), positive_variables=10,
        operations=122, operation_breakdown=dict(counts), exact_degree=816, syntactic_degree=928,
        full_remapped_gates=len(retained), removed_gate='qm1', reused_gate='bJ',
        generic_cancellation_identity=True, universal_norm_terms=len(norm.t),
        centered_norm_terms=len(centered.t), unique_weight816_term='omega^8',
        actual_tuple_every_retained_gate_diagnostics=diagnostics,
        free_signed_port_every_retained_gate_diagnostics=free_port_diagnostics,
        actual_tuple_degree_slices=slices, corruptions_rejected=controls,
        whole_fixed_tuple=coefficient_pins,
        parent_equation_sha256=PARENT_SHA,
        equation_sha256=digest((HERE/'equation.json').read_bytes()),
        scope='Exact universal complete-polynomial identity from local cancellation and full ordered gate substitution; authentic original compact44 specialization. Upper/exact degree transferred unchanged, with independent16-fold norm/weighted expansion and actual degree controls. No new internal-ZFC proof or Lean.')
    target = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE/target).write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

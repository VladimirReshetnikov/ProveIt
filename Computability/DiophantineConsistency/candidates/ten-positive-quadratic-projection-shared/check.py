#!/usr/bin/env python3
"""Independent105-gate circuit, exact symmetric octic and payload checker."""
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
PARENT_SHA = 'a0472d086ac0e0a2058c75e0cc15c6340125dd869c1f16d053609c3331fbffa9'


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
        need(op in ('+', '-', '*'), 'arithmetic operation')
        w = u+v if op == '+' else u-v if op == '-' else u*v
        env[name] = w if prime is None else w % prime
    return env


def line_degree(values, prime):
    degree, level = -1, 0
    values = list(values)
    while values:
        if values[0]:
            degree = level
        values = [(b-a) % prime for a, b in zip(values, values[1:])]
        level += 1
    return degree


def main():
    raw = (HERE/'source/parent-equation.json').read_bytes()
    need(digest(raw) == PARENT_SHA, 'complete frozen106-operation parent')
    parent, child = json.loads(raw), load(HERE/'equation.json')
    old, rows = parent['source'], child['source']
    remap, provenance = load(HERE/'PREFIX_REMAP.json'), load(HERE/'PROVENANCE.json')
    need(child['parent_sha256'] == remap['parent_sha256'] ==
         provenance['parent_equation_sha256'] == PARENT_SHA, 'consistent parent pins')
    need(child['domain'] == parent['domain'] == 'strictly positive integers' and
         child['witnesses'] == parent['witnesses'] and len(set(child['witnesses'])) == 10,
         'complete unchanged positive unknown list')
    need(child['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'],
         'whole unchanged fixed tuple')
    need(rows[:92] == old[:92], 'every literal prefix row byte-for-byte identical')
    need(remap['prefix'] == [dict(parent_index=i, child_index=i, register=r[0])
                             for i, r in enumerate(old[:92])], 'complete ordered prefix remap')
    replacement = remap['replaced_tail']
    need(replacement['parent_indices'] == list(range(92,106)) and
         replacement['child_indices'] == list(range(92,105)) and
         replacement['old_rows'] == old[92:] and replacement['new_rows'] == rows[92:],
         'complete literal old/new norm tails covered')
    need(child['output'] == parent['output'] == 'N', 'same final output')
    available = set(child['witnesses']+child['fixed_numerals'])
    dependencies = {}
    degrees = {v:1 for v in child['witnesses']} | {v:0 for v in child['fixed_numerals']}
    for name, op, a, b in rows:
        need(name not in available and op in ('+', '-', '*'), 'fresh binary gate')
        need(all(type(x) is int or x in available for x in (a,b)), 'topological circuit')
        available.add(name)
        dependencies[name] = (a,b)
        da, db = (0 if type(x) is int else degrees[x] for x in (a,b))
        degrees[name] = da+db if op == '*' else max(da,db)
    live, todo = set(), ['N']
    while todo:
        v = todo.pop()
        if type(v) is int or v in live:
            continue
        live.add(v)
        todo.extend(dependencies.get(v,()))
    need(live == available, 'all105 gates, ten unknowns and four ports live')
    counts = Counter(r[1] for r in rows)
    need(len(rows) == child['operations'] == 105 and
         dict(counts) == child['operation_breakdown'] == {'*':61, '+':26, '-':18},
         '105 live operations with one multiplication saved')
    need(degrees['N'] == child['syntactic_degree'] == parent['syntactic_degree'] == 464,
         'unchanged syntactic bound464')
    need(child['exact_degree'] == parent['exact_degree'] == 408 and
         all(degrees[name] == d for name,d in child['register_degrees'].items()),
         'every stated degree contract')

    oracle_path = HERE/'source/independent_norm_oracle.py'
    need(digest(oracle_path.read_bytes()) == provenance['oracle_sha256'], 'independent ring oracle pin')
    spec = importlib.util.spec_from_file_location('independent_sparse_ring_oracle',oracle_path)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    x,a,b,c,d,omega = [oracle.variable(i) for i in range(6)]
    old_tail,new_tail = old[92:],rows[92:]
    old_poly = oracle.evaluate(old_tail,dict(fs=x*x,fa=a,fb=b,fc=c))
    new_poly = oracle.evaluate(new_tail,dict(fs=x*x,fa=a,fb=b,fc=c))
    independent = oracle.norm_oracle(x,[a,b,c])
    need(old_poly['Pe'].t == new_poly['Pe'].t, 'exact free symmetric inner-form identity')
    need(old_poly['N'].t == new_poly['N'].t == independent.t,
         'complete old/new literal outputs equal the independent8-conjugate product')
    s = oracle.variable(0)
    need(((s-a-b-c)**2-4*(a*b+(a+b)*c)).t ==
         ((s+c-a-b)**2-4*(s*c+a*b)).t,
         'inner identity with s independent of a square substitution')
    centered = oracle.evaluate(new_tail,dict(fs=x*x,fa=a,fb=b,fc=x*x-omega))['N']
    weights = (58,78,84,0,0,102)
    weighted = {m:sum(e*w for e,w in zip(m,weights)) for m in centered.t}
    top = {m:centered.t[m] for m,w in weighted.items() if w == max(weighted.values())}
    need(max(weighted.values()) == 408 and top == {(0,0,0,0,0,4):1},
         'same unique centered weight408 term omega^4')
    bad = deepcopy(new_tail)
    bad[-1][1] = '+'
    need(oracle.evaluate(bad,dict(fs=x*x,fa=a,fb=b,fc=c))['N'].t != independent.t,
         'corrupted final norm operation actually evaluated and rejected')
    bad_inner = deepcopy(new_tail)
    i = next(i for i,r in enumerate(bad_inner) if r[0] == 'U')
    bad_inner[i][1] = '-'
    need(oracle.evaluate(bad_inner,dict(fs=x*x,fa=a,fb=b,fc=c))['N'].t != independent.t,
         'incorrect symmetric pair sum actually evaluated and rejected')
    coefficients, coefficient_pins = {}, {}
    need(child['coefficient_binding'] == parent['coefficient_binding'] ==
         load(HERE/'coefficients/BINDING.json'), 'unchanged complete binding')
    for name,pin in child['coefficient_binding']['ports'].items():
        blob = (HERE/'coefficients'/pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'],
             'complete authentic payload '+name)
        coefficients[name] = int.from_bytes(raw,'little')
        need(coefficients[name].bit_length() == pin['bits'], 'actual coefficient width')
        coefficient_pins[name] = dict(raw_sha256=digest(raw),bits=pin['bits'])
    beta = coefficients['beta']
    need(beta == 2**590069-1 and beta % 2 == 1 and beta >= 11 and
         0 < coefficients['MC'] < beta < coefficients['MF'] < 2*beta and coefficients['K0'] > 0,
         'actual complete tuple meets inherited proof hypotheses')
    rng = random.Random(105408)
    diagnostics = 0
    for prime in (1009,(1<<127)-1):
        for _ in range(50):
            env = {v:rng.randrange(-20,21) for v in child['witnesses']}
            env.update({v:c % prime for v,c in coefficients.items()})
            want,have = evaluate(old,env,prime),evaluate(rows,env,prime)
            need(all(want[r[0]] == have[r[0]] for r in rows[:92]) and
                 want['Pe'] == have['Pe'] and want['N'] == have['N'],
                 'every shared-prefix register and final output unchanged at actual tuple')
            diagnostics += 1
    free_controls = 0
    for _ in range(50):
        env = {v:rng.randrange(-3,4) for v in child['witnesses']+child['fixed_numerals']}
        want,have = evaluate(old,env),evaluate(rows,env)
        need(want['N'] == have['N'], 'complete signed free-port circuit identity')
        free_controls += 1
    slices = []
    for prime in ((1<<127)-1,(1<<89)-1):
        direction = {v:rng.randrange(1,prime) for v in child['witnesses']}
        base = {v:rng.randrange(1,prime) for v in child['witnesses']}
        ports = {v:c % prime for v,c in coefficients.items()}
        values = [evaluate(rows,ports | {v:(base[v]+t*direction[v]) % prime
                    for v in child['witnesses']},prime)['N'] for t in range(466)]
        degree = line_degree(values,prime)
        need(degree == 408,'whole actual-tuple line attains degree408')
        slices.append(dict(prime_bits=prime.bit_length(),degree=degree))
    display = load(HERE/'DISPLAY_BINDING.json')
    proof_pin = digest((HERE/'source/ordinary-proof.md').read_bytes())
    need(display['equation_sha256'] == digest((HERE/'equation.json').read_bytes()) and
         display['literal_registers'] == rows and display['norm_rows'] == new_tail and
         display['proof_sha256'] == provenance['ordinary_proof_sha256'] == proof_pin,
         'complete105-gate display binding and inherited ordinary proof')
    for name in ('parent-check.json','parent-check-optimized.json'):
        receipt = load(HERE/'source'/name)
        need(receipt['status'] == 'PASS' and receipt['equation_sha256'] == PARENT_SHA and
             receipt['ordinary_proof_sha256'] == proof_pin and receipt['exact_degree'] == 408,
             'frozen complete106parent receipts')
    for name in ('proof-peer.json','proof-peer-optimized.json'):
        peer = load(HERE/'source'/name)
        need(peer['status'] == 'PASS' and peer['proof_sha256'] == proof_pin,
             'independent ordinary proof peer remains bound')
    for name,pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/name).read_bytes()) == pin,'generated artifact seal '+name)
    report = dict(status='PASS',optimized_python=bool(sys.flags.optimize),positive_variables=10,
        operations=105,operation_breakdown=dict(counts),exact_degree=408,syntactic_degree=464,
        identical_literal_prefix_gates=92,parent_norm_tail_gates=14,new_norm_tail_gates=13,
        universal_norm_terms=len(independent.t),centered_norm_terms=len(centered.t),
        unique_weight408_term='omega^4',exact_symmetric_inner_and_full_output_identities=True,
        actual_tuple_whole_circuit_controls=diagnostics,free_signed_port_controls=free_controls,
        actual_tuple_degree_slices=slices,corrupt_norm_sign_and_pair_sum_rejected=True,
        whole_fixed_tuple=coefficient_pins,parent_equation_sha256=PARENT_SHA,
        equation_sha256=digest((HERE/'equation.json').read_bytes()),ordinary_proof_sha256=proof_pin,
        scope='Exact universal full-polynomial identity with106parent by complete literal prefix and independent sparse-ring tail certificates; actual fixedtuple unchanged. Degree and ordinary positive-zero equivalence transfer. No new native calibration, Lean or internal-ZFC proof.')
    name = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE/name).write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()

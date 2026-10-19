#!/usr/bin/env python3
"""Measure exact FC13B function-dispatch packing, preserving equality completion.

This is a data-format experiment, not a Turing machine. The selector slot is
deliberately excluded from Eq-congruence; the sibling note proves that this
preserves satisfiability without an infinite-model hypothesis. Every Boolean
regrouping is checked.
"""
from __future__ import annotations
from hashlib import sha256
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent
HOST = ROOT / 'ProveIt/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
OUT = ROOT / 'formalism_dispatch_results'
REF = ROOT / 'reference'


def reference(local, inherited):
    path = REF / local
    return path if path.exists() else HOST / inherited


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    sys.modules[name] = value
    spec.loader.exec_module(value)
    return value


K = module('equational_search', reference('equational_search.py', 'code/70-c244-equational-equational_search.py'))
B = module('build_equations', reference('build_equations.py', 'code/70-c244-equational-build_equations.py'))
SOURCE = K.freeze(json.loads(reference('FC13B_complete.json', 'data/70-c244-equational-reference-FC13B_complete.json').read_text()))
OLD = K.freeze(json.loads(reference('baseline_grouped.json', 'data/70-c244-equational-grouped.json').read_text()))
FUNCTIONS = {'V': 2, 'C': 3, 'I': 2, 'A': 2, 'U': 2, 'F': 2}


def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for part in partitions(rest):
        yield ((first,),) + part
        for i in range(len(part)):
            yield part[:i] + ((first,) + part[i],) + part[i+1:]


def model_regression():
    """Six selectors which are distinct objects but equivalent under Eq.

    This checks the dispatch construction itself, not the FC13B theory.
    """
    carrier = tuple(product(range(2), range(7)))
    fns = {f: (lambda *xs, i=i: (i + sum((j+1)*x for j, x in enumerate(xs))) % 2)
           for i, f in enumerate(FUNCTIONS)}
    handlers = {(0, i+1): f for i, f in enumerate(FUNCTIONS)}
    def dispatch(tag, *args):
        if tag not in handlers:
            return (0, 0)
        f = handlers[tag]
        return (fns[f](*(x[0] for x in args[:FUNCTIONS[f]])), 0)
    checks = 0
    for selector in carrier:
        for args in product(carrier, repeat=3):
            canonical = tuple((x[0], 0) for x in args)
            assert dispatch(selector, *args)[0] == dispatch(selector, *canonical)[0]
            checks += 1
    zeros = ((0, 0),)*3
    # All tag constants have the same Eq-class, while H may distinguish them.
    assert dispatch((0, 1), *zeros)[0] != dispatch((0, 4), *zeros)[0]
    return checks


def run(partition):
    groups = [g for g in partition if len(g) > 1]
    mapping = {f: (f'H{i}', max(FUNCTIONS[x] for x in group)+1)
               for i, group in enumerate(groups) for f in group}
    signature = dict(B.SIGNATURE)
    for f in mapping:
        del signature[f]
        signature['tag_'+f] = 0
    for h, arity in mapping.values():
        signature[h] = arity

    def term(t):
        if isinstance(t, str):
            return t
        name, *args = t
        args = tuple(term(x) for x in args)
        if name in mapping:
            h, arity = mapping[name]
            return (h, ('tag_'+name,), *args, *((B.D,)*(arity-1-len(args))))
        return (name, *args)

    def literal(lit):
        return lit[:2] + tuple(term(x) for x in lit[2:])

    equations = [B.SHEFFER, B.TOP_DEFINITION]
    group_record = []
    checked_assignments = 0
    for group in OLD['source_groups']:
        indices = group['source_indices']
        if len(indices) == 1 and 15 <= indices[0] <= 20:
            f = list(FUNCTIONS)[indices[0]-15]
            if f in mapping:
                continue
        clauses = [tuple(literal(lit) for lit in SOURCE[i]) for i in indices]
        equation = tuple(term(t) for t in group['equation'])
        assert B.check_equation(clauses, equation)
        equations.append(equation)
        atoms = {B.atom(l) for c in clauses for l in c}
        checked_assignments += 1 << len(atoms)
        group_record.append({'source_indices': indices, 'equation': equation})

    for i, group in enumerate(groups):
        h = f'H{i}'
        arity = max(FUNCTIONS[f] for f in group)+1
        xs = tuple(f'x{j}' for j in range(arity-1))
        ys = tuple(f'y{j}' for j in range(arity-1))
        # The selector is the same actual variable t on both sides. Eq is
        # required to respect the original object arguments only.
        clause = tuple((False, 'Eq', x, y) for x, y in zip(xs, ys)) + (
            (True, 'Eq', (h, 't', *xs), (h, 't', *ys)),)
        atoms = [B.atom(l) for l in clause]
        # A fixed linear-size Horn-to-NAND formula. Its truth table is checked.
        antecedent = atoms[0]
        for atom in atoms[1:-1]:
            antecedent = B.N(B.TOP, B.N(antecedent, atom))
        equation = (B.TOP, B.N(antecedent, B.N(B.TOP, atoms[-1])))
        assert B.check_equation([clause], equation)
        equations.append(equation)
        checked_assignments += 1 << len(atoms)
        group_record.append({'dispatch_group': group, 'equation': equation})

    start, target = B.N(B.TOP, B.TOP), B.TOP
    bits, metrics = B.encode_packet(equations, signature, start, target)
    decoded = B.decode_packet(bits, list(signature))
    assert decoded == (signature, [B.canonical_equation(e) for e in equations], start, target)
    clauses = 23 - sum(len(g)-1 for g in groups)
    record = {'partition': partition, 'clauses_after_equality_completion': clauses,
              'proper_function_symbols_before_boolean_reduction': len(partition),
              'introduced_tag_constants': sum(map(len, groups)),
              'checked_boolean_assignments': checked_assignments, **metrics}
    payload = {'signature': signature, 'equations': equations, 'start': start,
               'target': target, 'groups': group_record,
               'scope': 'Exact finite equational data; no binary interpreter or state bound.'}
    return record, payload, bits


def main():
    OUT.mkdir(exist_ok=True)
    results = []
    best = None
    for partition in partitions(tuple(FUNCTIONS)):
        record, payload, bits = run(partition)
        results.append(record)
        if best is None or record['complete_packet_bits'] < best[0]['complete_packet_bits']:
            best = record, payload, bits
    assert len(results) == 203
    baseline = next(r for r in results if len(r['partition']) == 6)
    assert baseline['complete_packet_bits'] == 2324
    record, payload, bits = best
    (OUT/'best.json').write_text(json.dumps(payload, indent=2)+'\n')
    (OUT/'best.bits').write_text(bits+'\n')
    (OUT/'best.equations').write_text('\n'.join(
        f'{i}: {B.pretty(a)} = {B.pretty(b)}' for i,(a,b) in enumerate(payload['equations']))+'\n')
    all_packed = next(r for r in results if len(r['partition']) == 1)
    evidence = {'scope': '203 exact dispatch partitions with object-coordinate congruence under the stated fixed Horn encoding; no global minimality or machine states.',
                'baseline': baseline, 'best': record, 'all_functions_packed': all_packed,
                'dispatch_model_assignments_checked': model_regression(),
                'packet_roundtrips': len(results), 'all_partitions': results,
                'best_packet_sha256': sha256((bits+'\n').encode()).hexdigest()}
    (OUT/'verification.json').write_text(json.dumps(evidence, indent=2)+'\n')
    print(json.dumps({k:v for k,v in evidence.items() if k != 'all_partitions'}, indent=2))


if __name__ == '__main__':
    main()

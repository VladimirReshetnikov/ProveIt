"""Audit all named formula occurrences in the worked mirror certificates.

This is an untrusted diagnostic, not a proof checker or a universal proof
normalizer. It inspects goals, transport motives, all nested D matrices,
and Q-resource bodies after computation-packet expansion. Independently
running the serialized certificates through a kernel remains necessary.

Usage from a delivery root:
    python tools/audit_named_formulas.py --kernel-dir . \
        --output evidence/named_formula_audit.json
"""
import argparse
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path


CHILDREN = ('major', 'minor', 'premise', 'continuation')
RULES = {'Hyp', 'Computation', 'Tr', 'QE', 'DI', 'DE', 'Neutral'}


def inspect_proof(proof, constructors):
    visited = set()
    totals = Counter()
    issues = []

    def issue(path, kind, value):
        issues.append({'path': path, 'kind': kind, 'value': repr(value)[:500]})

    def formula(value, path):
        if not isinstance(value, tuple) or not value:
            issue(path, 'not a named formula', value)
            return
        tag = value[0]
        totals['formula_' + str(tag)] += 1
        if tag == 'eq' and len(value) == 3:
            return
        if tag == 'q' and len(value) == 3:
            formula(value[2], path + '/Qbody')
            return
        if tag != 'd' or len(value) != 4:
            issue(path, 'unrecognized formula', value)
            return
        _, witness, index, body = value
        if not isinstance(body, tuple) or not body:
            issue(path, 'malformed D matrix', body)
            return
        if body[0] == 'eq' and len(body) == 3:
            totals['atomic_D_occurrences'] += 1
            left, right = body[1:]
            mirrored = (isinstance(right, tuple) and len(right) == 5
                        and right[0] == 'i'
                        and right[1] == constructors.V(index)
                        and right[2] == left)
            if not mirrored:
                issue(path, 'nonmirrored atomic D', value)
        elif body[0] != 'd':
            issue(path, 'noncanonical compound D matrix', value)
        formula(body, path + '/Dbody')

    def visit(node, path):
        if id(node) in visited:
            return
        visited.add(id(node))
        totals['proof_nodes'] += 1
        rule = node.get('rule')
        if rule not in RULES:
            issue(path, 'unrecognized proof rule', rule)
        formula(node['goal'], path + '/goal')
        if rule == 'Tr':
            formula(node['motive'], path + '/motive')
            if node['major']['goal'][1] == 0:
                totals['literal_zero_source_transports'] += 1
        if rule == 'DI':
            mode = node.get('mode')
            totals['DI_mode_' + str(mode)] += 1
            body = node['goal'][3]
            required = 'progress' if body[0] == 'eq' else 'case'
            if mode != required:
                issue(path, 'DI mode disagrees with root', mode)
        for key, value in node.items():
            if key in CHILDREN:
                visit(value, path + '/' + key)
            elif isinstance(value, dict) and 'rule' in value and 'goal' in value:
                issue(path + '/' + key, 'unexpected proof-child field', key)
    visit(proof, 'root')
    return dict(sorted(totals.items())), issues


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--kernel-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    tests = args.kernel_dir.resolve() / 'tests'
    sys.path.insert(0, str(tests))
    spec = importlib.util.spec_from_file_location('audited_mirror_examples',
                                                 tests / 'mirrored_cases.py')
    examples = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(examples)
    rows = []
    failures = 0
    for case in examples.proof_cases():
        counts, issues = inspect_proof(examples.P.expand_proof(case['proof']), examples.P)
        if case['expected'] and (issues or counts.get('literal_zero_source_transports', 0)):
            failures += 1
        rows.append({'name': case['name'], 'expected_accept': case['expected'],
                     'counts': counts, 'formula_or_mode_issues': issues})
    result = {
        'scope': 'Named proof goals, transport motives, every nested D, and Q bodies after computation expansion.',
        'limitations': [
            'This diagnostic does not replace the independent raw-certificate kernel checks.',
            'It checks all formula occurrences for mirror-shaped D matrices; it is not a general verifier of named proof rules.',
            'The delivered producer demonstrates the worked numerical/equational zero-source transformations. Inherited generic Q/D normalizer branches are not claimed to implement a universal mirrored-calculus proof translation.'
        ],
        'case_count': len(rows),
        'positive_cases_with_audit_failures': failures,
        'status': 'PASS' if failures == 0 else 'FAIL',
        'cases': rows,
    }
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(json.dumps({'status': result['status'], 'case_count': len(rows),
                      'positive_cases_with_audit_failures': failures}))
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()

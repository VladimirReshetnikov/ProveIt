#!/usr/bin/env python3
"""Independent targeted review of the EPSC2 default-index checker patch."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def rejected(call):
    try:
        call()
    except ValueError:
        return True
    return False


def audit(directory):
    old = load('review_old', directory / 'epsc2_original.py')
    new = load('review_new', directory / 'epsc2_default_indices.py')

    # A true full cross-variable specialization, deliberately expressed with
    # out-of-scope raw payloads. The consequent identifies the instantiated
    # variable and the original parameter q.
    raw = new.Imp(new.All(new.Rel(0, 100)), new.Rel(50, 100))
    env = (0, 1, 2, 3)
    proof = ['imp', 0, ['all', 1, 3, ['close', 3, 2]]]
    a = new.check_tree([new.Entry(False, raw, env)], proof)
    normal = old.Imp(old.All(old.Rel(0, 4)), old.Rel(3, 3))
    b = old.check_tree([old.Entry(False, normal, env)], proof)
    assert a == b
    assert rejected(lambda: old.check_tree([old.Entry(False, raw, env)], proof))

    # A satisfiable pair cannot be closed by colliding a fresh existential
    # witness with q. F forall x R(x,q) and T R(q,q) are jointly satisfiable.
    roots = [new.Entry(True, new.Rel(3, 3), env),
             new.Entry(False, new.All(new.Rel(0, 100)), env)]
    assert rejected(lambda: new.check_tree(roots, ['all', 1, ['close', 0, 2]]))
    assert rejected(lambda: new.check_tree(roots, ['all', 1, 3, ['close', 0, 2]]))

    # Numeric variable payloads are not eigenparameter names. Even a huge
    # out-of-range index may only select the final existing environment slot.
    huge = 1 << 100000
    assert new.select_last(env, huge) == 3
    assert new.select_last((7,), huge) == 7
    assert [new.select_last(env, i) for i in range(6)] == [0, 1, 2, 3, 3, 3]

    # Inspect the actual three projection sites and exercise their boundary.
    projections = []
    def visit(node):
        if node[0] == 'hole':
            projections.append(node[1:])
        elif node[0] in ('imp', 'all'):
            for child in node[1:]:
                visit(child)
    visit(new.TEMPLATE)
    assert sorted(projections) == sorted([(2, 0, 4, 3), (1, 0, 4, 3), (0, 1, 4, 3)])
    for projection in projections:
        exposed = new.Entry(True, new.Hole(*projection), (5, 6, 7, 8, 9),
                            new.All(new.Rel(0, 100))).exposed()
        assert len(exposed.environment) == 4 and exposed.matrix is None
        child = exposed.child(exposed.formula[1],
                              environment=(10,) + exposed.environment)
        assert child.atom() == (10, 8)

    # Untrusted certificate syntax cannot insert a template hole or fake a
    # Bottom conclusion. The public entry always supplies its fixed axioms.
    invalid = [
        {'matrices': [['hole', 0, 1, 2, 3]], 'proof': ['bottom', 0]},
        {'matrices': [['rel', True, 0]], 'proof': ['bottom', 0]},
        {'matrices': [['rel', -1, 0]], 'proof': ['bottom', 0]},
        {'matrices': [['rel', 100, 100]], 'proof': ['bottom', 0]},
        {'matrices': [], 'proof': ['bottom', 0], 'target': ['bot']},
    ]
    assert all(rejected(lambda cert=cert: new.check_refutation(cert)) for cert in invalid)

    # Resource failure must propagate out of the numeric acceptance layer;
    # it is neither an accepted refutation nor a skipped/rejected candidate.
    resources = []
    original = new.check_refutation
    try:
        for exception in (MemoryError, RecursionError, OverflowError):
            def fail(_certificate, exception=exception):
                raise exception('injected reviewer resource failure')
            new.check_refutation = fail
            try:
                new.accepts_number(0)
            except exception:
                resources.append(exception.__name__)
            else:
                raise AssertionError('Resource failure did not propagate')
    finally:
        new.check_refutation = original

    return {'status': 'PASS',
            'independent_constructed_collision_specialization': a,
            'fresh_witness_spurious_closures_rejected': 2,
            'exact_projection_sites': projections,
            'huge_index_bit_length': huge.bit_length(),
            'malformed_or_false_public_certificates_rejected': len(invalid),
            'resource_failures_propagated': resources,
            'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in [directory / 'epsc2_original.py',
                                        directory / 'epsc2_default_indices.py']},
            'scope': 'Independent targeted checks plus source/proof review; no kernel or binary proof.'}


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Assertions must be enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker-directory', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'theory_scope')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('independent_scope_results.json'))
    args = parser.parse_args()
    result = audit(args.checker_directory)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

#!/usr/bin/env python3
"""Reproduce the independent review's 54 coefficient/ledger cases.

This checker is separate from exact_checks.py. It reads the base compiler's
summand affine forms but expands them with its own sparse multiplication,
without Summand.records. It performs no LP, root search, or public-source work.
Run with python -B; this script also disables bytecode writes before imports.
All checks are explicit exceptions, and therefore remain active under -O.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import importlib.util
import itertools
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE_PATH = HERE / 'approved_base' / 'prism_certificate.py'
BASE_SHA256 = 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2'


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_real_compiler():
    require(sha256(BASE_PATH) == BASE_SHA256, 'Frozen base compiler hash mismatch')
    spec = importlib.util.spec_from_file_location('_independent_review_real', HERE / 'real_certificate.py')
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def multiply(left, right):
    result = Counter()
    for m, c in left.items():
        for n, d in right.items():
            result[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in result.items() if c}


def linear(form):
    return {(() if i < 0 else (i,)): c for i,c in form.items()}


def independently_expand_summands(compiler):
    """Independent sparse expansion of the supplied summand affine forms."""
    result = Counter()
    for term in compiler.summands():
        residual = linear(term.residual)
        if term.kind == 'square':
            value = multiply(residual, residual)
        elif term.kind == 'product':
            value = residual
        else:
            raise AssertionError('Unknown summand kind: ' + term.kind)
        if term.weight is not None:
            value = multiply(value, linear(term.weight))
        result.update(value)
    return {m:c for m,c in result.items() if c}


def run_checks():
    module = load_real_compiler()
    RealCompiler, Prism, PeriodicInput, base = module.RealCompiler, module.Prism, module.PeriodicInput, module.base
    cases = []
    coefficient_histogram = Counter()
    vertex_pairs = edge_pairs = 0
    ledger_keys = (
        'summands', 'product_summands', 'records', 'evaluation_mults',
        'evaluation_adds', 'expansion_coefficient_mults',
        'plain_square_residuals', 'weighted_square_residuals',
    )
    for dimensions in itertools.product((1,2,3), repeat=3):
        prism = Prism((-2,3,-4), dimensions)
        for background in (0,5):
            context = {'lengths': dimensions, 'background': background}
            additions = tuple((p, (i*7)%19) for i,p in enumerate(prism.points()))
            source = PeriodicInput((1,1,1), (background,), additions)
            old = base.Compiler(prism, source)
            original = independently_expand_summands(old)
            require(original == old.polynomial(), ('Independent base expansion mismatch', context))
            expected_flat = original.copy()
            expected_sharp = original.copy()
            for p in prism.points():
                for a,b,expected in (('f','k',2), ('f','c',2), ('k','c',86)):
                    monomial = tuple(sorted((old.v(p,a), old.v(p,b))))
                    require(original.get(monomial) == expected,
                            ('Vertex coefficient mismatch', context, p, a, b, original.get(monomial)))
                    coefficient_histogram[str(expected)] += 1
                    vertex_pairs += 1
                    expected_sharp[monomial] += 1
                    if a == 'f':
                        expected_flat[monomial] += 1
            for p,q in prism.edges():
                for a,b in itertools.combinations(base.EDGE_FIELDS[:5],2):
                    monomial = tuple(sorted((old.ev(p,q,a), old.ev(p,q,b))))
                    require(original.get(monomial) == 2,
                            ('Selector coefficient mismatch', context, p, q, a, b, original.get(monomial)))
                    coefficient_histogram['2'] += 1
                    edge_pairs += 1
                    expected_sharp[monomial] += 1
            require(set(expected_flat) == set(original) == set(expected_sharp),
                    ('Expected support preservation failed', context))

            merged = RealCompiler(prism, source)
            flat = RealCompiler(prism, source, 'flat')
            sharp = RealCompiler(prism, source, 'sharp')
            merged_poly = merged.polynomial()
            require(merged_poly == expected_flat, ('Merged coefficient changes mismatch', context))
            require(merged_poly == flat.polynomial(), ('Merged/flat polynomial mismatch', context))
            require(sharp.polynomial() == expected_sharp, ('Sharp coefficient changes mismatch', context))
            require(independently_expand_summands(merged) == merged_poly,
                    ('Independent merged expansion mismatch', context))
            require(set(merged_poly) == set(original), ('Merged support changed', context))
            require(max(map(len,merged_poly)) == 3, ('Merged degree is not exactly three', context))
            require(max(map(abs,merged_poly.values())) == max(map(abs,original.values())),
                    ('Merged coefficient height changed', context))
            require(dict(merged.collected_records()) == merged_poly,
                    ('Merged collected stream mismatch', context))

            old_ledger = old.ledger()
            merged_ledger = merged.ledger()
            expected_deltas = {key:2*prism.V for key in (
                'records', 'evaluation_mults', 'evaluation_adds', 'expansion_coefficient_mults')}
            for key in ledger_keys:
                require(merged_ledger[key] - old_ledger[key] == expected_deltas.get(key,0),
                        ('Merged ledger delta mismatch', context, key))
            for compiler in (merged,flat,sharp):
                enumerated, closed = compiler.ledger(), compiler.closed_ledger()
                for key in closed:
                    if key in enumerated:
                        require(enumerated[key] == closed[key],
                                ('Enumerated/closed ledger mismatch', context, compiler.variant, key))
            cases.append({
                'lengths': list(dimensions), 'background': background,
                'vertices': prism.V, 'edges': prism.E, 'halo_sites': prism.H,
                'base_collected_monomials': len(original),
                'merged_collected_monomials': len(merged_poly),
                'base_and_merged_coefficient_height': max(map(abs,original.values())),
                'status': 'passed',
            })
    require(len(cases) == 54, 'Incorrect case count')
    require(vertex_pairs == 1296 and edge_pairs == 6480, 'Incorrect pair count')
    require(dict(coefficient_histogram) == {'2':7344, '86':432}, 'Incorrect coefficient histogram')
    require(sha256(BASE_PATH) == BASE_SHA256, 'Frozen base compiler changed during checks')
    return {
        'status': 'passed',
        'checker': Path(__file__).name,
        'checker_sha256': sha256(Path(__file__)),
        'real_compiler_sha256': sha256(HERE / 'real_certificate.py'),
        'frozen_base_compiler_sha256': BASE_SHA256,
        'scope': 'Independent 54-case coefficient/ledger review; distinct from exact_checks.py; no LP branches',
        'expansion_method': 'Independent sparse multiplication of compiler-provided summand affine forms, without Summand.records',
        'geometries': 27, 'cases': 54,
        'vertex_penalty_pairs_checked': vertex_pairs,
        'edge_selector_pairs_checked': edge_pairs,
        'base_coefficient_histogram': dict(coefficient_histogram),
        'checks': [
            'Independent affine expansion equals base and merged compiler polynomials',
            'Exact fk=fc=2, kc=86, and same-edge selector pair=2 base coefficients',
            'Merged and flat polynomials are identical and have exactly the expected coefficient changes',
            'Sharp polynomial has exactly the expected full-pair coefficient changes',
            'Merged, flat, and sharp collected support equals base support',
            'Merged degree is exactly three and coefficient height equals base height',
            'Merged collected stream equals global polynomial collection',
            'Merged record/arithmetic deltas and unchanged summand/residual/product counts are exact',
            'Merged/flat/sharp enumerated and closed ledger shared entries agree',
            'Frozen source hash unchanged',
        ],
        'case_results': cases,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Also save the exact JSON receipt at this path')
    args = parser.parse_args()
    receipt = json.dumps(run_checks(), indent=2, sort_keys=True) + '\n'
    if args.output is not None:
        args.output.write_text(receipt)
    print(receipt, end='')

"""Reproduce finite independent replay, normalization and scope audits."""
import argparse
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import subprocess
import sys

import independent_named_replay as named


def functions_only(path):
    tree = ast.parse(path.read_text())
    tree.body = [node for node in tree.body if isinstance(node, (ast.FunctionDef, ast.Import, ast.ImportFrom))]
    namespace = {}
    exec(compile(tree, str(path), 'exec'), namespace)
    return namespace


def random_term(rng, size, bound=0, scope=2):
    atoms = [0] + list(range(-scope, 0)) + list(range(1, bound + 1))
    if not size or rng.random() < .45:
        return rng.choice(atoms)
    if rng.random() < .5:
        return [0, random_term(rng, size - 1, bound, scope)]
    return [random_term(rng, size - 1, bound, scope),
            random_term(rng, size - 1, bound, scope),
            random_term(rng, size - 1, bound + 1, scope)]


def random_formula(rng, depth, bound=0, scope=3):
    if depth and rng.random() < .6:
        return [random_formula(rng, depth - 1, bound + 2, scope)]
    return [random_term(rng, 3, bound, scope), random_term(rng, 3, bound, scope)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('checker', type=Path)
    parser.add_argument('positive_directory', type=Path)
    parser.add_argument('--adversaries', type=Path, default=Path(__file__).parent / 'independent_adversaries')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    candidate = functions_only(args.checker)
    rng = random.Random(2026111206)
    result = {
        'checker_sha256': hashlib.sha256(args.checker.read_bytes()).hexdigest(),
        'replayer_sha256': hashlib.sha256(Path(named.__file__).read_bytes()).hexdigest(),
        'normalization_comparisons': 0,
        'bound_substitution_comparisons': 0,
        'formula_parameter_substitution_comparisons': 0,
        'positive_replays': [],
        'adversarial_rejections': [],
        'public_cli_checks': 0,
        'resource_skips': 0,
        'failures': 0,
        'limits': 'Finite implementation evidence; no proof-assistant verification or universal soundness claim.'
    }
    for _ in range(400):
        raw = random_term(rng, 3)
        expected = named.encode(named.normal(named.term(raw, 2)))
        actual = candidate['walk'](raw, lambda i, d: i, form=False)
        named.require(actual == expected)
        result['normalization_comparisons'] += 1
    for depth in (0, 1):
        for _ in range(100):
            protected = (named.fresh_bound(),) if depth else ()
            source = named.fresh_bound()
            outer = (named.fresh_bound(), named.fresh_bound())
            old_environment = protected + (source,) + outer
            new_environment = protected + outer
            raw = random_term(rng, 3, len(old_environment))
            value = random_term(rng, 3, len(outer))
            left = named.term(raw, 2, old_environment)
            target = named.term(value, 2, outer)
            expected = named.encode(named.normal(named.replace(left, source, target)), new_environment)
            actual = candidate['sub'](raw, value, depth)
            named.require(actual == expected)
            result['bound_substitution_comparisons'] += 1
    for _ in range(200):
        left = named.normal(named.formula(random_formula(rng, 3), 3))
        target = named.normal(named.term(random_term(rng, 3, scope=3), 3))
        raw, raw_target = named.encode(left), named.encode(target)
        expected = named.encode(named.normal(named.replace(left, ('free', -3), target)))
        actual = candidate['walk'](raw, lambda i, d: raw_target if i == -3 else i)
        named.require(actual == expected)
        result['formula_parameter_substitution_comparisons'] += 1
    for path in sorted(args.positive_directory.glob('*.json')):
        data = json.loads(path.read_text())
        counts = named.check(data)
        result['positive_replays'].append({'file': path.name, 'counts': counts})
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(args.checker)]
            process = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=30)
            named.require(process.returncode == 0 and process.stdout == b'ACCEPT\n')
            result['public_cli_checks'] += 1
    for path in sorted(args.adversaries.glob('*.json')):
        data = json.loads(path.read_text())
        try:
            named.check(data)
        except (named.Invalid, IndexError, ValueError):
            pass
        else:
            raise RuntimeError('Independent replayer accepted ' + path.name)
        for optimized in (False, True):
            command = [sys.executable] + (['-O'] if optimized else []) + [str(args.checker)]
            process = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=30)
            named.require(process.returncode != 0)
            result['public_cli_checks'] += 1
        result['adversarial_rejections'].append(path.name)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()

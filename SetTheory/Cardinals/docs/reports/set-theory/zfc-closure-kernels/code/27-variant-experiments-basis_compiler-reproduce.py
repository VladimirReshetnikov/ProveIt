#!/usr/bin/env python3
"""Recompile all three frozen recipes and verify their finite RM certificates.

No network, search, Coq installation or third-party Python package is required.
The output is a new directory; existing files there are not overwritten.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, 'run without -O: verification uses assertions'
    out = args.output.resolve()
    assert out != HERE and HERE not in out.parents, 'write outside the input package'
    assert not out.exists() or not any(out.iterdir()), 'output must be new or empty'
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((HERE / 'input_manifest.json').read_text())
    for name, expected in manifest['sha256'].items():
        actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        assert actual == expected, (name, actual, expected)
    import basis_search as s
    nodes, names, rows, bundle, perms, bases, _ = s.setup()
    recipes = json.loads((HERE / 'recipes.json').read_text())
    results = {}
    for basis in ('L', 'KSP', 'KBP'):
        data = s.save_winner(out, basis, recipes[basis], nodes, names, rows, bundle, perms, bases)
        expected = recipes[basis].get('expected_numeric_sha256')
        if expected:
            assert data['numeric_sha256'] == expected
        results[basis] = {'working_states': data['cost']['working_states'],
                          'decision_states': data['cost']['decision_states'],
                          'framework_states': data['cost']['framework_states'],
                          'numeric_sha256': data['numeric_sha256'],
                          'rm_check': data['independent_rm_certificate_check']}
        print(json.dumps({basis: results[basis]}), flush=True)
    s.write_json(out / 'verification.json', results)


if __name__ == '__main__':
    main()

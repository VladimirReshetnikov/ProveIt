#!/usr/bin/env python3
"""Regenerate all four circuits from the retained ./upstream component.

Run without arguments to regenerate graphs and receipts. Run --check for a
read-only audit. Both modes require only the Python standard library.
"""
from pathlib import Path
import argparse
import hashlib
import json
import types

ROOT = Path(__file__).resolve().parent
VARIANTS = ('predecessor', 'linear', 'cubic', 'sixterm')
DEGREES = dict(zip(VARIANTS, (1245324, 1179788, 1114252, 1081125)))


def load_module(name, path):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def parent_path(variant):
    return ROOT/'upstream'/('upstream/integer10.json' if variant == 'predecessor'
                            else 'integer10_'+variant+'.json')


def serialize(body):
    return (json.dumps(body, separators=(',', ':'))+'\n').encode()


def build_variant(variant, parent):
    optimizer = load_module('ten_integer_optimizer_for_builder', ROOT/'optimize.py')
    new = optimizer.transform(parent, rewrite_delta=True)
    # Only path/provenance metadata is adjusted for this standalone package.
    new.update(exact_degree=DEGREES[variant],
               fixed_coefficients='upstream/FIXED_COEFFICIENTS.json',
               predecessor='upstream/upstream/integer10.json',
               identical_polynomial_parent=str(parent_path(variant).relative_to(ROOT)),
               rewrite_identity='P_optimized(v) = P_parent(v) for all ten integer inputs')
    return new


def build_all():
    optimizer = load_module('ten_integer_optimizer_for_build', ROOT/'optimize.py')
    audit = load_module('ten_integer_exact_audit_for_build', ROOT/'verify.py')
    summary = {}
    for variant in VARIANTS:
        parent_raw = parent_path(variant).read_bytes()
        parent = json.loads(parent_raw)
        new = build_variant(variant, parent)
        receipt = optimizer.verify(parent, new, saving=3)
        audit.graph_check(new)
        receipt['exact_polynomial_check'] = audit.exact_rewrite_check(parent, new)
        new_raw = serialize(new)
        receipt['parent_sha256'] = hashlib.sha256(parent_raw).hexdigest()
        receipt['new_sha256'] = hashlib.sha256(new_raw).hexdigest()
        (ROOT/('integer10_'+variant+'.json')).write_bytes(new_raw)
        (ROOT/('CHECKS_'+variant+'.json')).write_text(json.dumps(receipt, indent=2)+'\n')
        summary[variant] = receipt
    (ROOT/'SUMMARY.json').write_text(json.dumps(summary, indent=2)+'\n')
    return summary


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='verify without modifying files')
    args = parser.parse_args()
    if args.check:
        audit = load_module('ten_integer_standalone_audit', ROOT/'verify.py')
        result = audit.verify_all()
    else:
        result = build_all()
    print(json.dumps(result, indent=2))

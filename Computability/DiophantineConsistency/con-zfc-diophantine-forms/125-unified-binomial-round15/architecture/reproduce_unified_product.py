#!/usr/bin/env python3
"""Byte-exact reconstruction in temporary output trees, never in intake."""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import hashlib
import json
import sys
from types import ModuleType
import build_unified_product as builder

HERE = Path(__file__).resolve().parent
OPTIONS = {
    'unified_derived_cantor': ('cantor', 'derived', False),
    'unified_slack_shell': ('xx0', 'slack', False),
    'unified_derived_shell': ('xx0', 'derived', False),
    'unified_slack_cantor': ('cantor', 'slack', False),
    'unified_square_derived_cantor': ('cantor', 'derived', True),
    'unified_square_slack_shell': ('xx0', 'slack', True),
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-binding', type=Path)
    args = parser.parse_args()
    receipt = {'verified': True, 'optimized': not __debug__, 'variants': {}}
    for name, (syntax, labels, squared) in OPTIONS.items():
        with TemporaryDirectory(prefix='unified-product-replay-') as tmp:
            target = Path(tmp)/name
            builder.generate(target, syntax=syntax, labels=labels,
                             squared_radix_base=squared)
            files = sorted(p.relative_to(target) for p in target.rglob('*') if p.is_file())
            original = HERE/name
            expected = sorted(p.relative_to(original) for p in original.rglob('*') if p.is_file())
            if files != expected:
                raise ValueError(name + ': reconstructed file inventory differs')
            for rel in files:
                if (target/rel).read_bytes() != (original/rel).read_bytes():
                    raise ValueError(name + ': byte mismatch in ' + str(rel))
            receipt['variants'][name] = {'files_identical': len(files),
                'equation_sha256': digest(target/'natural/equation.json'),
                'polynomial_sha256': digest(target/'natural/expanded_polynomial.json')}
    closure = {}
    pending = list(sys.modules.values())
    seen = set()
    while pending:
        mod = pending.pop()
        if not isinstance(mod, ModuleType) or id(mod) in seen:
            continue
        seen.add(id(mod))
        # The reviewed engine also uses module_from_spec without registering
        # every loaded module in sys.modules. Follow module-valued globals.
        pending.extend(value for value in vars(mod).values()
                       if isinstance(value, ModuleType) and id(value) not in seen)
        file = getattr(mod, '__file__', None)
        if not file:
            continue
        p = Path(file).resolve()
        if p.is_relative_to(builder.BASE) and p.is_file():
            closure[str(p.relative_to(builder.BASE))] = digest(p)
    source = {'reviewed_release': builder.BASE.name,
        'imported_executable_closure': dict(sorted(closure.items())),
        'new_generator_sha256': digest(HERE/'build_unified_product.py'),
        'unchanged_source_binding': json.loads((builder.BASE/'architecture/SOURCE_BINDING.json').read_text()),
        'ordinary_new_proof': 'UNIFIED_PRODUCT_PROOF.md',
        'inherited_square_fixed_point_and_uniform_coefficient_proof':
            '../intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/proofs/shared_square_and_latent_index.md'}
    if args.source_binding:
        args.source_binding.write_text(json.dumps(source, sort_keys=True, indent=2)+'\n')
    receipt['imported_executable_files'] = len(closure)
    args.output.write_text(json.dumps(receipt, sort_keys=True, indent=2)+'\n')
    print(json.dumps(receipt, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()

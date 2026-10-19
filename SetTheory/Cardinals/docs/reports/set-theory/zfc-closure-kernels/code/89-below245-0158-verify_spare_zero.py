#!/usr/bin/env python3
"""Replay local or whole-frame spare-zero proofs against a recovered baseline.

The baseline package is the incoming zfc245-proof-20261018 archive. This adapter
changes only the stated output spare value in its two proof drivers. It does
not alter the transition-table execution rules or guard any additional case.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import types

ROOT = Path(__file__).resolve().parents[1]


def module_from_text(name, path, text):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(text, str(path), 'exec'), module.__dict__)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--whole-frame', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    package = args.package.resolve()
    sys.path.insert(0, str(package/'reference/context246/code'))
    sys.path.insert(0, str(package/'code'))
    import rebuild_machines as rebuild
    assert __debug__, 'Assertions must remain enabled.'
    original, start = rebuild.read_table(ROOT/'inputs/routing245_old.tm')
    table, changed_start = rebuild.read_table(ROOT/'inputs/spare0_245_old.tm')
    assert start == changed_start == 95
    assert [(key, original[key], table[key]) for key in original
            if original[key] != table[key]] == [((255, 0), (1, 'L', 255), (0, 'L', 255))]
    if args.whole_frame:
        path = package/'code/full_symbolic_parametric.py'
        source = path.read_text()
        before = 'out_file=out_file[:-1]+m.B(E(1))+[Blank()]'
        after = 'out_file=out_file[:-1]+m.B(E())+[Blank()]'
        assert source.count(before) == 1
        module = module_from_text('spare_zero_full_frame', path, source.replace(before, after))
        destination = (args.output or ROOT/'results/spare0_full_symbolic_result.json').resolve()
        sys.argv = [str(path), '--table', str(ROOT/'inputs/spare0_245_old.tm'),
                    '--all-values', '--sites', str(package/'certificate/sites_physical.json'),
                    '--output', str(destination)]
        module.main()
        return
    path = package/'reference/context246/code/check_macro_inductions.py'
    source = path.read_text()
    before, after = '[b] + B(E(1)) + [z]', '[b] + B(E()) + [z]'
    assert source.count(before) == 1
    module = module_from_text('spare_zero_local_inductions', path, source.replace(before, after))
    module.TABLE = table
    module.prove_blocks()
    identity = module.prove_word_identity()
    macros = module.prove_macros()
    marks = module.prove_marks()
    result = dict(status='PASS_LOCAL_MACROS',
                  source_driver_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  exact_adapter=dict(before=before, after=after, occurrences=1),
                  table_sha256=hashlib.sha256((ROOT/'inputs/spare0_245_old.tm').read_bytes()).hexdigest(),
                  block_proofs=module.BLOCK_PROOFS, word_identity=identity,
                  macros=macros, marking=marks,
                  scope='Universal finite-word and finite-list induction checks for local macros. '
                        'No correct blank bootstrap is asserted; the separate certificate disproves it.')
    destination = args.output or ROOT/'results/spare0_local_proofs.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      ('block_proofs', 'word_identity', 'macros', 'marking')}, indent=2))


if __name__ == '__main__':
    main()

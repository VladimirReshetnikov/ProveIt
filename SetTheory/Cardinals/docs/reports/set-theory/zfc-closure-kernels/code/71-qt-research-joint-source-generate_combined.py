#!/usr/bin/env python3
"""Compose native equality orientations with exact bundle DNE rewrites.

This generates and checks source expressions. It does not certify a binary
machine or use an estimated dictionary cost as a working-state count.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--equality-source', type=Path, required=True)
    ap.add_argument('--dne-checker', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__, 'Assertions must be enabled.'
    d = load(args.dne_checker, 'combined_dne_checker')
    data = json.loads(args.equality_source.read_text())
    fine = json.loads(args.dne_checker.with_name('macro_to_fine.json').read_text())
    spec = d.load_spec()
    original = spec['bundle']('a', 'b', 'c')
    original_paths = d.redexes(original)
    assert len(original_paths) == 6
    original_rows = spec['ax_rows']('a', 'old_cache', 'b', 'c', 'u')
    prefix = [166, 121, 180, 176]
    variants = []
    for name, eqv in sorted(data['anchored_variants'].items()):
        if eqv['C_G_membership_converse']:
            continue
        rows = [d.freeze(x) for x in eqv['logical_row_asts']]
        bundle0 = d.freeze(eqv['bundle_ast'])
        paths = d.redexes(bundle0)
        assert paths == original_paths
        assert rows[0] == original_rows[1]
        assert rows[2] == original_rows[3]
        assert rows[4] == original_rows[5]
        assert rows[6] == original_rows[7]
        front = prefix + [m for row in rows for m in d.emit(row)]
        for mask in range(64):
            bundle = d.normalize(bundle0, {p for i, p in enumerate(paths) if mask >> i & 1})
            assert bundle[0] == 'imp'
            macros = front + d.emit(bundle) + d.TAIL
            stack, events = d.execute_macros(macros[:-len(d.TAIL)])
            assert stack == ['old_top', original_rows[0], *rows, bundle]
            assert events == [(176, 2), (158, 4)]
            assert macros.count(158) == macros.count(208) == 1
            fine_word = ''.join(fine[str(m)] for m in macros)
            assert len(fine_word) == 1270 - 18 * mask.bit_count()
            variants.append(dict(
                mask=len(variants), name=f'{name}_dne{mask:02d}',
                equality_orientation=name, dne_mask=mask,
                fine_AX=fine_word, fine_length=len(fine_word),
                word=macros, logical_rows=rows, bundle=bundle,
                fine_sha256=hashlib.sha256(fine_word.encode()).hexdigest(),
                proof_scope='Composition of native numerical-axiom interderivability and common-core contextual DNE; binary compilation still required.',
            ))
    assert len(variants) == 32 * 64
    assert len({v['name'] for v in variants}) == len(variants)
    out = dict(status='PASS_EXACT_COMBINED_SOURCE_FAMILY',
               scope='Source-emission and symbolic stack certificates, not a machine count.',
               variants=variants, count=len(variants),
               hashes={'equality_source':hashlib.sha256(args.equality_source.read_bytes()).hexdigest(),
                       'dne_checker':hashlib.sha256(args.dne_checker.read_bytes()).hexdigest()},
               numerical_reads_preserved=True, gate_and_tail_preserved=True,
               all_32_times_64_records_symbolically_checked=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k:v for k,v in out.items() if k!='variants'}, indent=2))


if __name__ == '__main__':
    main()

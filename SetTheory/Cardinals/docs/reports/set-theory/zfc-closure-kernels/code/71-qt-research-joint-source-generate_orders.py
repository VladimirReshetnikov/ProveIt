#!/usr/bin/env python3
"""Compose complete-row permutation with the proved mask32 DNE rewrite.

This checks exact symbolic emission and the protected stack interface. The
ordinary derivation-selector transfer is attributed to the incoming
axiom-symmetry packet. No binary-machine state count follows from this check.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--dne-checker', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    module_spec = importlib.util.spec_from_file_location('order_dne', args.dne_checker)
    d = importlib.util.module_from_spec(module_spec)
    sys.modules[module_spec.name] = d
    module_spec.loader.exec_module(d)
    spec = d.load_spec()
    fine = json.loads(args.dne_checker.with_name('macro_to_fine.json').read_text())
    logical = spec['ax_rows']('a', 'old_cache', 'b', 'c', 'u')
    rows = logical[1:]
    old_bundle = spec['bundle']('a', 'b', 'c')
    bundle = d.normalize(old_bundle, {d.redexes(old_bundle)[5]})
    identity = tuple(range(8))
    orders = {identity, tuple(reversed(identity))}
    # Every transposition, every single-row insertion, and each rotation of
    # each consecutive block. Deduplicate before assigning stable indices.
    for i in range(8):
        for j in range(8):
            order = list(identity)
            order[i], order[j] = order[j], order[i]
            orders.add(tuple(order))
            order = list(identity)
            row = order.pop(i)
            order.insert(j, row)
            orders.add(tuple(order))
        for j in range(i + 2, 9):
            part = identity[i:j]
            for k in range(1, len(part)):
                orders.add(identity[:i] + part[k:] + part[:k] + identity[j:])
    variants = []
    for order in sorted(orders):
        emitted = [rows[k] for k in order]
        macros = [166, 121, 180, 176] + [m for row in emitted for m in d.emit(row)] + d.emit(bundle) + d.TAIL
        stack, events = d.execute_macros(macros[:-len(d.TAIL)])
        assert stack == ['old_top', logical[0], *emitted, bundle]
        assert events[0] == (176, 2)
        assert len(events) == 2 and events[1][0] == 158
        assert macros.count(158) == macros.count(208) == 1
        word = ''.join(fine[str(m)] for m in macros)
        assert len(word) == 1252
        variants.append(dict(mask=64*len(variants)+32,
            name='order_' + ''.join(str(k+1) for k in order) + '_dne32',
            order_zero_based=order, dne_mask=32, fine_AX=word,
            fine_length=len(word), word=macros, logical_rows=emitted,
            bundle=bundle, read_events=events,
            fine_sha256=hashlib.sha256(word.encode()).hexdigest()))
    assert len({v['fine_AX'] for v in variants}) == len(variants)
    result = dict(status='PASS_PERMUTED_DNE32_SOURCE_FAMILY',
        count=len(variants), variants=variants,
        scope='Exact complete-row emissions plus inherited permutation/DNE transfer; binary compilation required.',
        checker_sha256=hashlib.sha256(args.dne_checker.read_bytes()).hexdigest())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='variants'}, indent=2))


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Optional deterministic beam search for the selected K226 address repairs.

This is discovery code, not a runtime certificate. The small fixed recipe in
build226.py is sufficient to reproduce the selected machine without search.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
sys.path.insert(0, str(PACKAGE))
import build227 as b

g = b.g
PROTECTED = {150, 152, 173, 153, 172, 184, 182, 159, 166,
             118, 169, 99, 148, 155, 176, 98, 85}


def score(root):
    sites = g.sites(root)
    bad = [p for p, op, arg in sites if '0000000' in p]
    return len(bad), sum(map(len, bad)), max(len(p) for p, op, arg in sites)


def candidates(root, table):
    mapping, inverse = g.decoder_mapping(root, table)
    clean = {q for q in inverse if len(inverse[q]) == 1 and q not in PROTECTED
             and table[q, 0][:2] == (0, 1)
             and table[q, 1][:2] == (1, 1)}
    for outer in sorted(clean):
        for bit in (0, 1):
            inner = table[outer, bit][2]
            if inner not in clean:
                continue
            direction = 'left' if bit else 'right'
            try:
                new_root, new_table, cert = g.stage(root, table, outer, inner, direction)
            except ValueError:
                continue
            if cert['metrics']['maximum_depth'] <= 48:
                yield new_root, new_table, cert


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=Path,
                        default=PACKAGE / 'generated226/01_unrepaired226')
    parser.add_argument('--out', type=Path, default=HERE / 'replayed')
    args = parser.parse_args()
    root = g.tree(json.loads((args.seed / 'sites.json').read_text()))
    table = b.read_table(args.seed / 'table_k230labels.tm')
    reference = g.graph(g.sites(root))[1:]
    beam = [(root, table, [])]
    seen = {hashlib.sha256(b.encode(table).encode()).hexdigest()}
    started = time.monotonic()
    for depth in range(1, 11):
        pending = []
        for old_root, old_table, history in beam:
            for new_root, new_table, cert in candidates(old_root, old_table):
                key = hashlib.sha256(b.encode(new_table).encode()).hexdigest()
                if key in seen:
                    continue
                seen.add(key)
                candidate_score = score(new_root)
                candidate_history = history + [cert]
                if candidate_score[0] == 0:
                    assert g.graph(g.sites(new_root))[1:] == reference
                    receipt = {'status': 'SOURCE_GUARDS_PRESERVED_ZERO6',
                               'history': candidate_history,
                               'search_seen': len(seen), 'search_depth': depth,
                               'elapsed_seconds': time.monotonic() - started,
                               'scope': 'Discovery only; native runtime is a separate gate.'}
                    b.save_stage(args.out, key[:12], new_root, new_table, receipt)
                    assert key == '6f5a35c58961c77baf595ab743a185f4df6815aaaceb89a5b1494521b96f1d6c'
                    print('FOUND_SELECTED', key, flush=True)
                    return
                pending.append((candidate_score, key, new_root, new_table, candidate_history))
        pending.sort(key=lambda item: item[:2])
        beam = [(r, t, h) for s, key, r, t, h in pending[:16]]
        print('DEPTH', depth, 'SEEN', len(seen),
              'BEST', pending[0][:2] if pending else None, flush=True)
        if not beam:
            break
    raise SystemExit('No repaired source found within the fixed search bound')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    main()

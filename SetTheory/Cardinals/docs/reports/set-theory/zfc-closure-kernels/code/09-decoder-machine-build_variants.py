#!/usr/bin/env python3
"""Reconstruct all three variants, checking every accepted fold sequentially.

The emitter reuses exact old decoder subtrees as an optimization heuristic;
the exhaustive affine checks are the justification for every contextual reuse.
"""
import functools
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise SystemExit('Refusing optimized Python (-O/-OO): this builder requires enabled assertions.')

import verify

HERE = Path(__file__).resolve().parent


def write_table(path, table, start):
    lines = [f'#! start {start}']
    for q, b in sorted(table, key=lambda z: (int(z[0]), z[1])):
        w, d, n = table[q, b]
        lines.append(f'{q} {b} {w} {d} {n}')
    path.write_text('\n'.join(lines) + '\n')


def fold(table, substitutions):
    def target(q):
        seen = set()
        while q in substitutions:
            assert q not in seen
            seen.add(q)
            q = substitutions[q]
        return q
    return {(q, b): (w, d, target(n)) for (q, b), (w, d, n) in table.items()
            if q not in substitutions}


def emit_decoder():
    old = json.loads((HERE / 'data/decoder_entries.json').read_text())
    new = json.loads((HERE / 'data/candidate202.json').read_text())
    nodes = {int(k): tuple(tuple(e) for e in v) for k, v in new['nodes'].items()}
    @functools.lru_cache(None)
    def fingerprint(edge):
        if edge[0] == 'N':
            a, b = nodes[edge[1]]
            text = 'N(' + fingerprint(a) + ',' + fingerprint(b) + ')'
        else:
            text = ':'.join(map(str, edge))
        return hashlib.sha256(text.encode()).hexdigest()
    old_fp = {v: int(n) for n, v in old['fingerprints'].items()}
    table = verify.BASE.copy()
    entries = {}
    allocate = 255
    def modal_entry(counts):
        return max(counts, key=counts.get)
    for n in nodes:
        f = fingerprint(('N', n))
        if n == new['root']:
            entries[n] = '96'
        elif f in old_fp:
            entries[n] = modal_entry(old['state_entries'][str(old_fp[f])])
        else:
            entries[n] = str(allocate)
            allocate += 1
    def edge_transition(edge, bit):
        if edge[0] == 'N':
            return bit, 'R', entries[edge[1]]
        if edge[0] == 'B' and edge[1] == 1:
            return 0, 'L', '7' if bit == 0 else '33'
        tag = ':'.join(map(str, edge))
        return bit, 'R', modal_entry(old['leaf_entries'][tag])
    for n in nodes:
        if entries[n] == '96' or fingerprint(('N', n)) not in old_fp:
            for bit, edge in enumerate(nodes[n]):
                table[entries[n], bit] = edge_transition(edge, bit)
    return table


def audit_coverage(table, paths, gap, blank):
    stats, used = verify.affine_audit(table, paths, gap)
    boot = None
    if blank:
        boot, boot_used = verify.boot_audit(table)
        used |= boot_used
    covered = used | verify.BOX_PAIRS
    retained = {q for q, _ in covered} | {'96', '0'}
    return stats, boot, covered, retained


def prune_and_write(name, table, paths, gap, blank):
    stats, boot, covered, retained = audit_coverage(table, paths, gap, blank)
    changes = []
    pruned = {}
    for (q, bit), (write, move, target) in table.items():
        if q not in retained:
            continue
        if target not in retained and target != '254':
            assert (q, bit) not in covered
            changes.append({'state': q, 'read': bit, 'old_target': target,
                            'new_target': '0', 'absent_from_coverage': True})
            target = '0'
        pruned[q, bit] = write, move, target
    start = '0' if blank else '96'
    assert verify.check_total_closed(pruned, start) == len(retained)
    # Re-run against the actual transition-closed table, not its expanded source.
    after, after_boot, after_coverage, after_states = audit_coverage(pruned, paths, gap, blank)
    assert after == stats and after_boot == boot and after_coverage == covered
    assert after_states == retained
    write_table(HERE / 'machines' / name, pruned, start)
    result = {'expanded_working_rows': len(table) // 2, 'retained_working_rows': len(retained),
              'removed_states': sorted({q for q, _ in table} - retained, key=int),
              'rewired_unread_transitions': changes,
              'post_pruning_affine_cases': after['pass'],
              'post_pruning_exact_boot': after_boot,
              'total_and_target_closed': True}
    (HERE / 'results' / (name + '.pruning.json')).write_text(json.dumps(result, indent=2) + '\n')
    print('built', name, len(retained), 'states;', len(changes), 'unread targets rewired', flush=True)
    return pruned


def main():
    base_paths = verify.paths_from_dag('decoder_entries.json')
    new_paths = verify.paths_from_dag('candidate202.json')
    core = fold(verify.BASE, {'5': '48'})
    core = {(q, b): t for (q, b), t in core.items() if q != '8'}
    prune_and_write('prepared252.tm', core, base_paths, 40, False)
    emitted = emit_decoder()
    prune_and_write('decoder267.tm', emitted, new_paths, 41, True)
    folds = json.loads((HERE / 'data/folds11.json').read_text())
    log = []
    for dead, replacement in folds.items():
        emitted = fold(emitted, {dead: replacement})
        stats, boot, covered, retained = audit_coverage(emitted, new_paths, 41, True)
        log.append({'dead': dead, 'replacement': replacement,
                    'affine': stats, 'boot': boot, 'retained_states': len(retained)})
        print('accepted', dead, '->', replacement, ';', len(retained), 'retained states', flush=True)
    (HERE / 'results/sequential_folds.json').write_text(json.dumps(log, indent=2) + '\n')
    prune_and_write('decoder256.tm', emitted, new_paths, 41, True)
    verify.main()


if __name__ == '__main__':
    main()

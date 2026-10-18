#!/usr/bin/env python3
"""Reconstruct the 246-state table and independently replay its exact bootstrap.

The input is the frozen prefix250 original-label table. The two changes are
contextual state folds; the universally quantified domain proof is supplied
separately. Literal bootstrap replay is finite evidence, not a non-halting test.
"""
from pathlib import Path
import argparse
import hashlib
import json

BASE_SHA256 = 'fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43'
STEPS = 410735


def parse(raw):
    tab = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, t = line.split()
        key = (int(q), int(b))
        assert key not in tab
        tab[key] = (int(w), d, int(t))
    return tab


def encode(tab, start):
    return ('#! start ' + str(start) + '\n' + ''.join(
        f'{q} {b} {w} {d} {t}\n' for (q, b), (w, d, t) in sorted(tab.items())
    )).encode('ascii')


def generate(raw):
    assert hashlib.sha256(raw).hexdigest() == BASE_SHA256
    base = parse(raw)
    assert len(base) == 500
    removed = {0, 1, 3, 97}
    tab = {key: val for key, val in base.items() if key[0] not in removed}
    assert base[60, 0] == (0, 'R', 0)
    assert base[0, 1] == base[20, 1] == (0, 'L', 2)
    assert base[255, 0] == (1, 'L', 97)
    assert base[97, 1] == base[255, 1] == (1, 'L', 131)
    tab[60, 0] = (0, 'R', 20)
    tab[255, 0] = (1, 'L', 255)
    forbidden = {(0, 0), (1, 0), (1, 1), (3, 0), (3, 1), (97, 0)}
    fold = lambda q: {0: 20, 97: 255}.get(q, q)
    checked_pairs = 0
    for (q, b), (w, d, target) in base.items():
        if (q, b) in forbidden:
            continue
        assert tab[fold(q), b] == (w, d, fold(target))
        checked_pairs += 1
    assert checked_pairs == 494
    states = {q for q, _ in tab}
    assert len(states) == 246 and len(tab) == 492
    assert set(tab) == {(q, b) for q in states for b in (0, 1)}
    assert {t for w, d, t in tab.values()} - states == {254}
    order = [95] + sorted(states - {95})
    renumber = {q: i for i, q in enumerate(order)}
    canonical = {(renumber[q], b): (w, d, 246 if t == 254 else renumber[t])
                 for (q, b), (w, d, t) in tab.items()}
    return base, tab, canonical, renumber


def bootstrap(tab):
    one = set()
    q, h = 95, 0
    used = {}
    for tm in range(STEPS):
        assert q != 254, ('early halt', tm)
        key = q, int(h in one)
        used[key] = used.get(key, 0) + 1
        w, d, q = tab[key]
        if w:
            one.add(h)
        else:
            one.discard(h)
        h += 1 if d == 'R' else -1
    assert (q, h) == (96, -5)
    assert min(one) == h - 1 == -6
    header = min(x for x in one if x >= h)
    assert header == 176
    vals, pos, end = [], header + 1, max(one)
    while pos <= end:
        assert pos not in one and pos + 1 in one
        first = pos + 1
        pos = first
        while pos in one:
            pos += 1
        vals.append(pos - first - 1)
    assert vals[:9] == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    assert len(vals) == 176 and vals[9:] == [1] * 167
    expected = {h - 1, header}
    pos = header + 1
    for v in vals:
        expected.update(range(pos + 1, pos + v + 2))
        pos += v + 2
    assert expected == one
    assert len(one) == 351
    physical = vals[:9]
    logical = [physical[i] for i in (6, 2, 0, 4, 3, 7, 8, 5, 1)]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert header - h == 181 >= 40
    return dict(status='PASS', start=95, halt=254, steps=STEPS,
                final_state=q, head=h, marker=h - 1, header=header,
                head_to_header_distance=header - h,
                marker_to_header_distance=header - (h - 1), clean_pc='',
                physical_primary=physical, logical_primary=logical,
                logical_register_order=['N', 'T', 'W', 'A', 'D', 'H', 'X', 'Y', 'L'],
                spare_count=len(vals) - 9, spare_values=vals[9:],
                one_count=len(one), all_one_positions=sorted(one),
                all_other_cells_zero=True,
                used_transition_counts={f'{q}/{b}': count
                                        for (q, b), count in sorted(used.items())},
                proof_scope='Exact finite replay establishing a safe root frame; '
                            'recurrent simulation is proved separately.')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError('Assertions required; run without -O.')
    raw = args.baseline.read_bytes()
    base, tab, canonical, renumber = generate(raw)
    old, canon = encode(tab, 95), encode(canonical, 0)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / 'zfc_fold246_old.tm').write_bytes(old)
    (args.output / 'zfc_fold246.tm').write_bytes(canon)
    boot = bootstrap(tab)
    boot['old_table_sha256'] = hashlib.sha256(old).hexdigest()
    boot['canonical_table_sha256'] = hashlib.sha256(canon).hexdigest()
    seen, pending = set(), [0]
    while pending:
        q = pending.pop()
        if q == 246 or q in seen:
            continue
        seen.add(q)
        pending.extend(canonical[q, b][2] for b in (0, 1))
    audit = dict(status='PASS', working_states=246, rows=492,
                 start=0, halt=246, original_start=95, original_halt=254,
                 original_dispatch=96, canonical_dispatch=renumber[96],
                 graph_reachable_working_states=len(seen),
                 contextual_quotient_checked_pairs=494,
                 contextual_quotient_excluded_pairs=[[0, 0], [1, 0], [1, 1], [3, 0], [3, 1], [97, 0]],
                 removed_from_prefix250=[0, 1, 3, 97],
                 changed_rows=[dict(state=q, read=b, before=base[q, b], after=tab[q, b])
                               for q, b in ((60, 0), (255, 0))],
                 baseline_sha256=BASE_SHA256,
                 old_sha256=hashlib.sha256(old).hexdigest(),
                 canonical_sha256=hashlib.sha256(canon).hexdigest(),
                 old_to_canonical={str(q): v for q, v in renumber.items()},
                 canonical_to_old={str(v): q for q, v in renumber.items()},
                 halting_rows=[dict(state=q, read=b, transition=a)
                               for (q, b), a in sorted(canonical.items()) if a[2] == 246])
    (args.output / 'renumbering-and-table-audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    (args.output / 'independent-bootstrap-audit.json').write_text(json.dumps(boot, indent=2) + '\n')
    print(json.dumps({k: v for k, v in audit.items()
                      if k not in ('old_to_canonical', 'canonical_to_old')}, indent=2))
    print(json.dumps({k: v for k, v in boot.items()
                      if k not in ('spare_values', 'all_one_positions', 'used_transition_counts')}, indent=2))


if __name__ == '__main__':
    main()

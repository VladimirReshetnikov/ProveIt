#!/usr/bin/env python3
"""Offline exact graph comparison of PA194P5 with 82 pinned frontier classes.

Python 3 standard library only. Run from any directory:
  python3 comparison/verify_novelty.py

Canonical tuples, rather than digests alone, are compared. The equivalence
relation permits control renaming, arbitrary spanning-root choice, global
left/right reflection, global interchange of read/write symbols, and erasure
of the write/movement actions on edges entering the terminal halt. This is
deliberately broader than blank-zero, specified-start machine equivalence.
The result certifies graph novelty within the supplied corpus, not global
priority or the PA consistency theorem.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
from table_tools import parse_table, canonical

HERE = Path(__file__).resolve().parent
DELIVERED_SHA256 = 'cf3a2c2d3ba8e95d5c0ea825c3f279ae529b6591cc1280264b0ba3793e77d026'

def sha256(raw):
    return hashlib.sha256(raw).hexdigest()

def forms(data, broad=False):
    """Return the least BFS encoding over every spanning root and symmetry."""
    rows, states, halt = data
    best = None
    transforms = ((False, False), (False, True), (True, False), (True, True)) if broad else ((False, False),)
    for reflect, complement in transforms:
        if broad:
            changed = {}
            for q in states:
                for bit in (0, 1):
                    w, d, t = rows[q, bit ^ complement]
                    if t == halt:
                        changed[q, bit] = (0, 'R', halt)
                    else:
                        changed[q, bit] = (w ^ complement, ('L' if d == 'R' else 'R') if reflect else d, t)
            transformed = (changed, states, halt)
        else:
            transformed = data
        for root in sorted(states):
            value = canonical(transformed, root)
            if value is not None and (best is None or value < best):
                best = value
    return best

def maximum_reachable(data):
    rows, states, halt = data
    best = 0
    for root in states:
        reached = {root}
        todo = [root]
        for q in todo:
            for bit in (0, 1):
                target = rows[q, bit][2]
                if target != halt and target not in reached:
                    reached.add(target)
                    todo.append(target)
        best = max(best, len(reached))
    return best

def nonhalting_action_histogram(data, reflect=False, complement=False):
    rows, states, halt = data
    counts = collections.Counter(
        (bit ^ complement, w ^ complement,
         ('L' if d == 'R' else 'R') if reflect else d)
        for (q, bit), (w, d, t) in rows.items() if t != halt)
    return tuple(sorted(counts.items()))

def check_table(path, expected_sha=None):
    raw = path.read_bytes()
    got = sha256(raw)
    if expected_sha is not None and got != expected_sha:
        raise ValueError('Table SHA256 mismatch: ' + str(path))
    data = parse_table(raw)
    if data is None:
        raise ValueError('Not a complete numeric binary table with one terminal halt: ' + str(path))
    return data, got

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, default=HERE.parent/'machine/pa194p5.tm')
    ap.add_argument('--start', type=int, default=0)
    ap.add_argument('--output', type=Path, default=HERE/'candidate_novelty.json')
    args = ap.parse_args()
    candidate, raw_hash = check_table(args.candidate)
    rows, states, halt = candidate
    if len(states) != 194 or len(rows) != 388 or args.start not in states:
        raise ValueError('Expected a 194-control, 388-row candidate and valid start.')
    if canonical(candidate, args.start) is None:
        raise ValueError('Candidate does not graph-reach every control from its stated start.')
    exact = forms(candidate)
    broad = forms(candidate, broad=True)
    frontier = json.loads((HERE/'frontier194.json').read_text())
    if len(frontier) != 82:
        raise ValueError('Pinned frontier must contain exactly 82 representatives.')
    matches = []
    seen_exact = set()
    seen_broad = set()
    records = []
    for entry in frontier:
        data, got = check_table(HERE/entry['table'], entry['sha256'])
        if len(data[1]) != 194:
            raise ValueError('Wrong representative state count.')
        normal = forms(data)
        if normal is None or sha256(repr(normal).encode()) != entry['graph_hash']:
            raise ValueError('Spanning graph identity mismatch: ' + entry['table'])
        if normal in seen_exact:
            raise ValueError('Duplicate graph in frontier representatives.')
        seen_exact.add(normal)
        relaxed = forms(data, broad=True)
        seen_broad.add(relaxed)
        matched = relaxed == broad
        if matched:
            matches.append(entry['name'])
        records.append({'name': entry['name'], 'table': entry['table'], 'sha256': got,
                        'graph_hash': entry['graph_hash'],
                        'broad_graph_hash': sha256(repr(relaxed).encode()), 'match': matched})
    diagnostics = []
    diagnostics194 = []
    for path in sorted((HERE/'diagnostics').glob('*.tm')):
        data, got = check_table(path, path.stem)
        reach = maximum_reachable(data)
        if reach == len(data[1]):
            raise ValueError('A purported nonspanning diagnostic has a spanning root.')
        if len(data[1]) == 194:
            diagnostics194.append((path.name, data))
        diagnostics.append({'table': 'diagnostics/'+path.name, 'sha256': got,
                            'states': len(data[1]), 'maximum_reachable_controls': reach,
                            'match': False,
                            'reason': 'Control count differs or no root reaches every control; candidate has a spanning root.'})
    if len(diagnostics194) != 2:
        raise ValueError('Expected exactly two nonspanning194 literal identities.')
    first_histogram = nonhalting_action_histogram(diagnostics194[0][1])
    second_histograms = [nonhalting_action_histogram(diagnostics194[1][1], r, c)
                         for r in (False, True) for c in (False, True)]
    if first_histogram in second_histograms:
        raise ValueError('Simple invariant does not distinguish the two nonspanning194 fixtures.')
    result = {
        'status': 'PASS' if not matches else 'MATCH_FOUND',
        'snapshot': '4be5c6e3a10292a7466f5d3687e3b39615ff049b',
        'candidate': {'path': args.candidate.name, 'sha256': raw_hash,
                      'matches_delivered_table_hash': raw_hash == DELIVERED_SHA256,
                      'working_states': len(states), 'rows': len(rows), 'start': args.start,
                      'halt': halt, 'all_controls_graph_reachable': True,
                      'graph_hash': sha256(repr(exact).encode()),
                      'broad_graph_hash': sha256(repr(broad).encode())},
        'comparison': {'spanning_194_graph_classes': len(frontier),
                       'broad_equivalence_classes': len(seen_broad),
                       'additional_nonspanning194_broad_classes': len(diagnostics194),
                       'all_recognized194_broad_classes_in_literal_scope': len(seen_broad)+len(diagnostics194),
                       'nonspanning_literal_identities_checked': len(diagnostics),
                       'equality_method': 'Exact canonical tuples; SHA256 values are supplementary identifiers.',
                       'allowed_symmetries': ['arbitrary control relabeling', 'arbitrary spanning-root choice',
                                             'global tape reflection', 'global read/write bit interchange',
                                             'erasure of terminal-edge write and movement actions'],
                       'matches': matches},
        'frontier_results': records,
        'nonspanning_diagnostics': diagnostics,
        'nonspanning194_distinction': {
            'tables': [x[0] for x in diagnostics194],
            'first_nonhalting_edge_action_histogram': first_histogram,
            'second_histograms_under_four_symmetries': second_histograms,
            'same_graph': False,
            'method': 'Different read/write/move histograms on nonterminal edges, even under all four global transformations.'},
        'limits': ['Corpus-relative graph distinction is not a global priority claim.',
                   'This script does not establish any consistency equivalence.',
                   'Census scope and excluded source encodings are documented in README.txt.']}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status', 'candidate', 'comparison')}, indent=2))
    if matches:
        raise SystemExit(1)

if __name__ == '__main__':
    main()

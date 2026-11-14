#!/usr/bin/env python3
"""Replay the independent graph comparison from the bundled historical tables.

The original check_all_prior_graphs.py additionally authenticates table
membership directly against the full pinned incoming ZIPs. This wrapper uses
its unchanged parsing and graph algorithms on the compact exact-byte corpus.
"""
from pathlib import Path
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check_all_prior_graphs as c

def main():
    directory = HERE.parent / 'comparison/prior196'
    index = json.loads((directory / 'index.json').read_text())
    prior = json.loads((HERE / 'all_prior_graph_review.json').read_text())
    v = c.v
    targets = []
    for label in ('candidate_0', 'candidate_1', 'zerojump_0', 'zerojump_1'):
        rows = v.read_machine(v.INP / (label + '_machine.tm'))
        targets.append((label, v.canonical(rows, 0)[0], c.outputs(rows)))
    expected = {r['parsed_sha256']: r for r in prior['prior_tables']}
    v.require(len(index['tables']) == len(expected) == 127, 'Corpus size')
    seen = set()
    trials = 0
    for entry in index['tables']:
        key = entry['parsed_sha256']
        v.require(key in expected and key not in seen, 'Corpus identity')
        seen.add(key)
        record = expected[key]
        for field in ('archive', 'member', 'sha256'):
            v.require(entry[field] == record[field], 'Historical binding')
        data = (directory / entry['file']).read_bytes()
        v.require(hashlib.sha256(data).hexdigest() == entry['sha256'], 'Table digest')
        rows = c.parse(data.decode('utf-8-sig'))
        signature = c.outputs(rows)
        possible = {h for _, h, s in targets if s == signature}
        count = 0
        if possible:
            for q in sorted({q for q, b in rows}):
                count += 1
                h, reached = v.canonical(rows, q)
                v.require(h not in possible, 'Prior graph matches a graft')
        v.require(count == record['roots_tried'], 'Root-count receipt')
        trials += count
    v.require(trials == prior['arbitrary_root_canonicalizations'] == 23324,
              'Total root-count receipt')
    print(json.dumps({'status': 'PASS', 'prior_parsed_distinct_tables': len(seen),
                      'rooted_canonicalizations': trials, 'new_graphs': 4,
                      'matches': 0}, indent=2))

if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Rooted graph novelty against 84 frozen 215-state graphs, including reflection."""
from pathlib import Path
import json
from common import cli, parse_table, require, sha, write_json

MANIFEST_SHA = 'b2ef3bedad5e4a0f744080ae7c8382fbe858b1c3c7746c164d47a1f7f3529b10'


def canonical(table, start, reflect=False):
    states = {q for q, b in table}
    outside = {z for w, d, z in table.values()} - states
    require(len(states) == 215 and len(table) == 430 and len(outside) == 1,
            'Comparison table census')
    order, mapping = [start], {start: 0}
    for q in order:
        for bit in (0, 1):
            z = table[q, bit][2]
            if z in states and z not in mapping:
                mapping[z] = len(mapping)
                order.append(z)
    require(set(mapping) == states, 'Comparison graph has unreachable state')
    mapping[next(iter(outside))] = len(states)
    return tuple((mapping[q], b, w, -d if reflect else d, mapping[z])
                 for q in order for b in (0, 1) for w, d, z in [table[q, b]])


def run(root, work):
    """Recompute every canonical form; hashes alone are not the comparison."""
    root, work = Path(root), Path(work)
    raw = (root / 'comparison/manifest.json').read_bytes()
    require(sha(raw) == MANIFEST_SHA, 'Frozen corpus manifest')
    manifest = json.loads(raw)
    require(manifest['commit'] == 'b6fb232916d008383e7cf2990d68ddb30fded7db', 'Corpus pin')
    current_raw = (root / 'machine/dr215.native.tm').read_bytes()
    table, start = parse_table(current_raw)
    key, mirror = canonical(table, start), canonical(table, start, True)
    keys, matches, details = set(), [], []
    for record in manifest['representatives']:
        data = (root / 'comparison' / record['file']).read_bytes()
        require(sha(data) == record['sha256'], 'Frozen table hash')
        old, oldstart = parse_table(data)
        other = canonical(old, oldstart)
        require(sha(repr(other).encode()) == record['graph_sha256'], 'Frozen graph hash')
        require(other not in keys, 'Duplicate graph representative')
        keys.add(other)
        equal, reflected = key == other, mirror == other
        if equal or reflected:
            matches.append({'file': record['file'], 'equal': equal, 'reflected': reflected})
        details.append({'file': record['file'], 'equal': equal, 'reflected': reflected})
    require(len(keys) == 84 and len(manifest['all_occurrences']) == 321, 'Corpus census')
    require(not matches, 'Candidate matches a frozen graph')
    result = {
        'status': 'NO_ROOTED_OR_REFLECTED_GRAPH_MATCH',
        'candidate_sha256': sha(current_raw), 'corpus_manifest_sha256': sha(raw),
        'repository_commit': manifest['commit'], 'unique_graphs': len(keys),
        'table_occurrences': len(manifest['all_occurrences']), 'comparisons': details,
        'scope': 'Rooted action-labelled transition graphs; this does not assert behavioral inequivalence.',
    }
    write_json(work / 'comparison.json', result)
    return result


if __name__ == '__main__':
    cli(run)

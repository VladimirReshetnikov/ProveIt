#!/usr/bin/env python3
"""Recompute the three-candidate comparison and bind snapshots to original ZIPs."""
from pathlib import Path
import hashlib
import itertools
import json
import zipfile
import source_language as L
from build import parse, census, need, ROOT

PACKETS = {
    'Contextual': ('U211_ConPA_Contextual_2026-10-28.zip', 'u211_contextual_2026-10-28',
                   'machine/sites.json'),
    'Research': ('U211_ConPA_Research_2026-10-28.zip',
                 'U211_ConPA_Decoder_Reassociation_2026-10-28', 'machine/sites.json'),
    'Rotated': ('U211_ConPA_Rotated_2026-10-28.zip', 'U211_ConPA_Rotated_2026-10-28',
                'source/sites.json'),
}

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def canonical(table):
    # Deterministic BFS in read-symbol order gives the unique rooted labeling.
    queue, numbering, rows = [0], {0: 0, 254: -1}, []
    for q in queue:
        for bit in (0, 1):
            w, d, target = table[q, bit]
            if target not in numbering:
                numbering[target] = len(queue)
                queue.append(target)
            rows.append((numbering[q], bit, w, d, numbering[target]))
    need(len(queue) * 2 == len(table), 'Canonicalization misses a state')
    return rows

def compare():
    tables, sources, graphs, result = {}, {}, {}, {}
    for label, (archive, prefix, source_member) in PACKETS.items():
        folder = ROOT / 'comparison' / label
        with zipfile.ZipFile(ROOT / 'inputs' / archive) as z:
            for local, member in [('u211.native.tm', 'machine/u211.native.tm'),
                                   ('u211.tm', 'machine/u211.tm'), ('sites.json', source_member)]:
                need((folder / local).read_bytes() == z.read(prefix + '/' + member),
                     'Snapshot is not bound to the original archive: ' + label + '/' + local)
        table, rows = parse(folder / 'u211.native.tm'), json.loads((folder / 'sites.json').read_text())
        census(table, 211)
        dense = parse(folder / 'u211.tm')
        census(dense, 211, 211)
        mapping = {q: i for i, q in enumerate(sorted({q for q, b in table}))}
        mapping[254] = 211
        need(dense == {(mapping[q], b): (w, d, mapping[t])
                       for (q, b), (w, d, t) in table.items()}, 'Input dense isomorphism')
        graph = L.graph_intervals(rows)
        need(L.graph_arithmetic(rows)[0] == graph, 'Input graph resolvers disagree')
        tables[label], sources[label], graphs[label] = table, rows, graph
        result[label] = {'working_states': 211, 'rows': 422, 'metrics': L.metrics(L.tree(rows)),
                         'source_edges': sum(len(x[1]) for x in graph),
                         'native_sha256': sha((folder / 'u211.native.tm').read_bytes()),
                         'dense_sha256': sha((folder / 'u211.tm').read_bytes()),
                         'source_sha256': sha((folder / 'sites.json').read_bytes()),
                         'archive_sha256': sha((ROOT / 'inputs' / archive).read_bytes())}
    pairs = []
    for a, b in itertools.combinations(PACKETS, 2):
        x, y = tables[a], tables[b]
        pairs.append({'a': a, 'b': b,
                      'changed_common_rows': sum(x[k] != y[k] for k in x.keys() & y.keys()),
                      'rows_only_a': sorted(x.keys() - y.keys()),
                      'rows_only_b': sorted(y.keys() - x.keys()),
                      'source_addresses_differ': sum(u[0] != v[0] for u, v in zip(sources[a], sources[b])),
                      'same_primitive_word': [r[1:] for r in sources[a]] == [r[1:] for r in sources[b]],
                      'same_complete_cfg': graphs[a] == graphs[b],
                      'isomorphic_rooted_labeled_transition_graph': canonical(x) == canonical(y)})
    need(all(p['same_primitive_word'] and p['same_complete_cfg'] and
             not p['isomorphic_rooted_labeled_transition_graph'] for p in pairs),
         'Unexpected relationship among input proposals')
    return {'status': 'INPUT_COMPARISON_PASS', 'candidates': result, 'comparisons': pairs,
            'scope': 'Fresh literal/source comparison; original finite replay logs are separate.'}

if __name__ == '__main__':
    result = compare()
    (ROOT / 'build').mkdir(exist_ok=True)
    (ROOT / 'build/comparison.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

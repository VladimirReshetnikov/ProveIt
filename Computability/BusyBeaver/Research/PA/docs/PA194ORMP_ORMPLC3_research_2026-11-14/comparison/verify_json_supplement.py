#!/usr/bin/env python3
"""Check the two supplemental Boolean-direction tables against exact old graphs.

Only the standard library is required. The original pinned JSON is included
compressed, with its uncompressed SHA256 and Git source path in the receipts.
No interpretation of the program, or consistency theorem, is inferred.
"""
from pathlib import Path
import argparse, gzip, hashlib, json
from check_novelty import form, require

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    receipts = json.loads((here/'json_coverage/occurrences.json').read_text())
    identities = json.loads((here/'json_coverage/identities.json').read_text())
    raw = gzip.decompress((here/'json_coverage/source_data.json.gz').read_bytes())
    source = json.loads(raw)
    source_hash = hashlib.sha256(raw).hexdigest()
    index = json.loads(gzip.decompress((here/'frontier194_index.json.gz').read_bytes()))
    classes = {c['action_graph_sha256']: c for c in index['classes']}
    cases = []
    for receipt in receipts:
        require(receipt['raw_sha256'] == source_hash, 'source digest differs')
        pointer = receipt['json_pointer']
        require(pointer in ('$/primary', '$/permuted'), 'unexpected JSON pointer')
        rows = {}
        for action in source[pointer[2:]]:
            require(isinstance(action, list) and len(action) == 5, 'invalid action')
            q, b, w, direction, target = action
            require(type(q) is int and q >= 0 and type(target) is int and target >= 0,
                    'invalid state label')
            require(type(b) is int and b in (0, 1) and type(w) is int and w in (0, 1),
                    'invalid binary symbol')
            require(type(direction) is bool and (q, b) not in rows,
                    'expected distinct Boolean-direction rows')
            rows[q, b] = (w, 'R' if direction else 'L', target)
        states = {q for q, b in rows}
        terminals = {t for w, d, t in rows.values()} - states
        require(len(states) == 194 and len(rows) == 388
                and all((q, b) in rows for q in states for b in (0, 1))
                and len(terminals) == 1, 'incomplete 194-control matrix')
        normalized = ''.join(f'{q} {b} {w} {d} {t}\n'
                             for (q, b), (w, d, t) in sorted(rows.items())).encode()
        normalized_hash = hashlib.sha256(normalized).hexdigest()
        require(normalized_hash == receipt['normalized_sha256'], 'normalization differs')
        data = rows, states, next(iter(terminals))
        candidates = [form(data, root, loose=False) for root in sorted(states)]
        spanning = [value for value, reached in candidates if reached == 194]
        require(bool(spanning), 'no spanning root')
        canonical = min(spanning)
        graph_hash = identities[normalized_hash]['action_graph_sha256']
        expected = tuple(tuple(action) for action in classes[graph_hash]['rows'])
        require(canonical == expected, 'supplement adds a different exact graph')
        cases.append({'json_pointer': pointer, 'normalized_sha256': normalized_hash,
                      'action_graph_sha256': graph_hash, 'working_states': 194,
                      'exact_full_transition_tuple_match': True})
    result = {'source': receipts[0]['path'], 'source_sha256': source_hash,
              'tables_checked': len(cases), 'new_graph_classes': 0, 'cases': cases,
              'comparison': 'Exact full canonical tuples, preserving terminal actions; no hash-based isomorphism decision.'}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()

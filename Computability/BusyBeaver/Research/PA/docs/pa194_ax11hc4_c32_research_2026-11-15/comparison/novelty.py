#!/usr/bin/env python3
"""Offline exact novelty and pairwise comparison of 194-state machines.

Usage: python3 -B novelty.py TABLE.tm [OTHER.tm ...] --output replay.json
The default corpus and its SHA-256 index are beside this script.
"""
import argparse, hashlib, json
from pathlib import Path
from tm_tables import parse, canonical, compare_root, has_spanning_root

HERE = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def candidate(path):
    data = path.read_bytes()
    rows, states, start, _ = parse(data)
    if start is None or len(states) != 194:
        raise ValueError('candidate requires 194 controls and a specified start')
    forms = []
    for mirror in (False, True):
        for flip in (False, True):
            form, n = canonical(rows, states, start, mirror, flip)
            if n != 194:
                raise ValueError('candidate start does not reach all controls')
            transformed = {}
            for q in states:
                for b in (0, 1):
                    w, d, target = rows[q, b ^ int(flip)]
                    transformed[q, b] = (w ^ int(flip), ('L' if d == 'R' else 'R') if mirror else d, target)
            assert compare_root(transformed, states, start, form)[0]
            forms.append((mirror, flip, form))
    return dict(path=str(path), sha256=sha(data), rows=rows, states=states, start=start, forms=forms)

def against(rows, states, forms):
    matches, prefix, count = [], 0, 0
    for root in sorted(states):
        for mirror, flip, expected in forms:
            equal, k = compare_root(rows, states, root, expected)
            prefix = max(prefix, k)
            count += 1
            if equal:
                matches.append(dict(root=root, mirror=mirror, bit_exchange=flip))
    return matches, prefix, count

def run(args):
    candidates = [candidate(Path(p)) for p in args.tables]
    index = json.loads(Path(args.index).read_text())
    corpus = []
    excluded = []
    for key, info in sorted(index.items()):
        path = Path(args.corpus) / (key + '.tm')
        data = path.read_bytes()
        assert sha(data) == info['sha256'], str(path)
        rows, states, _, _ = parse(data)
        assert len(states) == 194
        spanning = has_spanning_root(rows, states)
        assert spanning == info['exact_unrooted'], key
        if spanning:
            corpus.append((key, info, rows, states))
        else:
            excluded.append(key)
    results = []
    for c in candidates:
        checks, matches, count = [], [], 0
        for key, info, rows, states in corpus:
            hit, prefix, n = against(rows, states, c['forms'])
            count += n
            matches.extend(dict(class_key=key, **h) for h in hit)
            checks.append(dict(class_key=key, source=info['path'], maximum_matching_prefix=prefix))
        results.append(dict(candidate=c['path'], sha256=c['sha256'], start=c['start'],
                            positive_orientation_controls=4, spanning_classes=len(corpus),
                            root_orientation_comparisons=count, matches=matches,
                            novel_in_recognized_corpus=not matches, checks=checks))
    pairs = []
    for i, a in enumerate(candidates):
        for b in candidates[:i]:
            hits, prefix, count = against(b['rows'], b['states'], a['forms'])
            pairs.append(dict(first=b['path'], second=a['path'], first_sha256=b['sha256'],
                              second_sha256=a['sha256'], root_orientation_comparisons=count,
                              maximum_matching_prefix=prefix, matches=hits, distinct=not hits))
    result = dict(comparison='Exact transition tuples; arbitrary state names and roots, global reflection and bit exchange; terminal write/move ignored.',
                  scope='Literal tables in all six pinned incoming archives recursively; all139 historical194 table keys independently recovered. Roles are attributed, and JSON/generator-only encodings were not freshly censused.',
                  nonspanning_representatives_excluded=excluded, candidates=results, pairwise=pairs)
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(candidates=[{k:v for k,v in c.items() if k!='checks'} for c in results], pairwise=pairs,
                          nonspanning_representatives_excluded=len(excluded)), indent=2))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('tables', nargs='+')
    p.add_argument('--corpus', default=str(HERE / 'representatives194'))
    p.add_argument('--index', default=str(HERE / 'representatives194.json'))
    p.add_argument('--output', default='novelty_replay.json')
    run(p.parse_args())

#!/usr/bin/env python3
"""Exact cosmetic comparison with a frozen numeric-table corpus.

Uses complete serialized canonical graphs, not just digests, for equality.
The corpus must contain a census.json and tables/<file-SHA256>.tm.
Changing the root here is allowed only for a spanning root; the tool says
nothing about semantic equivalence or the correctness of either machine.
"""
import argparse, json
from pathlib import Path
from census import parse, rootfree, sha

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('candidate', type=Path)
    ap.add_argument('--corpus', type=Path, default=Path(__file__).resolve().parent / 'current_census')
    ap.add_argument('--out', type=Path)
    a = ap.parse_args()
    data = a.candidate.read_bytes(); table = parse(data)
    assert table is not None, 'Not a complete numeric binary table with exactly one halt target'
    mine = [rootfree(table, m, c)[0] for m in (False, True) for c in (False, True)]
    assert all(x is not None for x in mine), 'No spanning control root'
    key = min(mine)
    census = json.loads((a.corpus / 'census.json').read_text())
    matches, compared = [], 0
    for group in census['classes']:
        if group['states'] != len(table[1]): continue
        prior = parse((a.corpus/'tables'/(group['raw_sha256s'][0]+'.tm')).read_bytes())
        # All transformations act invertibly, so transforming only the candidate
        # and comparing against an untransformed prior covers the same relation.
        prior_key = rootfree(prior)[0]
        compared += 1
        if any(x == prior_key for x in mine):
            matches.append({'rootfree_sha256':group['rootfree_sha256'], 'paths':group['paths']})
    result = dict(candidate_sha256=sha(data), states=len(table[1]),
                  canonical_cosmetic_sha256=sha(key),
                  corpus_commit=census['summary']['commit'],
                  compared_same_size_classes=compared, exact_string_comparisons=True,
                  transformations=['arbitrary working-state relabeling','spanning-root change','L/R reflection','global bit interchange'],
                  absent_from_corpus=not matches, matches=matches)
    text = json.dumps(result,indent=2)+'\n'
    if a.out: a.out.write_text(text)
    print(text)

if __name__ == '__main__': main()

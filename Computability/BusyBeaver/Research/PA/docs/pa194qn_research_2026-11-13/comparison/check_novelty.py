#!/usr/bin/env python3
"""Exact finite graph novelty check for a proposed 194-state table.

Compares full canonical transition tuples, allowing state renaming, any
graph-spanning start, reflection, and bit complement. Blank-tape behavior is
not inferred by this graph check. Corpus coverage is recorded separately.
The canonical traversal and numeric parser derive from inventory_census.py
in the supplied PA194N6 packet and retain that attribution.
"""
import argparse, hashlib, json
from pathlib import Path
from inventory_census import parse_table, canonical

def forms(data):
    return {c for reflect in (False,True) for complement in (False,True)
            for q in sorted(data[1])
            if (c:=canonical(data,q,reflect,complement)) is not None}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path)
    ap.add_argument('--corpus',type=Path,default=Path(__file__).resolve().parent)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args();raw=a.table.read_bytes();data=parse_table(raw)
    assert data is not None and len(data[1])==194
    cand=forms(data);assert cand,'Candidate has no graph-spanning start.'
    ledger=json.loads((a.corpus/'frontier194.json').read_text());matches=[]
    for r in ledger:
        old=(a.corpus/r['representative_file']).read_bytes()
        assert hashlib.sha256(old).hexdigest()==r['representative_sha256']
        p=parse_table(old);assert p is not None
        # The candidate set already includes all four global transformations.
        old_forms={c for q in sorted(p[1]) if (c:=canonical(p,q)) is not None}
        if cand & old_forms:matches.append(r['name'])
    receipt=dict(candidate_sha256=hashlib.sha256(raw).hexdigest(),states=194,
        exact_tuple_comparison=True,corpus_graph_classes=len(ledger),
        equivalences_allowed=['state renaming','spanning root choice','L/R reflection','symbol complement'],
        matches=matches,novel=not matches,
        scope='All recognized 194-state literal graph classes in the pinned PA/incoming corpus; not arbitrary source-only encodings.')
    if a.output:a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

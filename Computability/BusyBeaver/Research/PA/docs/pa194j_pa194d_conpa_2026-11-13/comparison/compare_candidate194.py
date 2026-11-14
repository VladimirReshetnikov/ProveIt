#!/usr/bin/env python3
"""Compare a candidate with frozen194 frontier, ignoring root and names;
allow global L/R reflection and bit complementation as additional tests.
This is only a graph comparison, not a halting or consistency verifier.
"""
import argparse,json
from pathlib import Path
from census_current_snapshot import parse,rootfree
ap=argparse.ArgumentParser();ap.add_argument('candidate',type=Path);ap.add_argument('--corpus',type=Path,default=Path(__file__).with_name('frontier194.json'));a=ap.parse_args()
t=parse(a.candidate.read_bytes());assert t is not None
assert len(t[1])==194
hashes=[rootfree(t,m,c)[0] for m in(False,True)for c in(False,True)]
assert all(x is not None for x in hashes)
k=min(hashes);d=json.loads(a.corpus.read_text());matches=[r['name']for r in d['classes']if r['cosmetic_class_sha256']==k]
print(json.dumps({'candidate':str(a.candidate),'states':194,'matches':matches,'cosmetic_class_sha256':k,'different_from_all_eight':not matches},indent=2))

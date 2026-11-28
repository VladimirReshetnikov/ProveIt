#!/usr/bin/env python3
"""Verify pinned Git object IDs and reproduce the proposal TeX keyword scan."""
import csv, re, subprocess, sys
from pathlib import Path
if len(sys.argv)!=2:
    raise SystemExit('usage: python3 verify_sources.py /path/to/ProveIt')
repo=Path(sys.argv[1]).resolve()
base=Path(__file__).resolve().parent
rev='9050b04000647d588d0c78d945180abcd3b0bcf7'
root='Analysis/GeneralizedRiemannHypothesis/'
pattern=re.compile(r'Fitting|Ribet|Morita|Noetherian induction|formsMod|BlockFittingBound|annihilator.*length|length.*annihilator', re.I)
def git(*args):
    return subprocess.check_output(['git','-C',str(repo),*args],text=True)
def rows(name):
    with (base/name).open(encoding='utf8') as f:
        yield from csv.DictReader(f,delimiter='\t')
def verify(path, expected):
    actual=git('rev-parse',rev+':'+root+path).strip()
    if actual!=expected: raise ValueError(f'{path}: expected {expected}, got {actual}')
for row in rows('source_anchors.tsv'):
    verify(row['path'],row['blob_sha'])
for row in rows('proposal_audit.tsv'):
    verify('docs/proposals/'+row['directory'],row['tree_sha'])
seen=set()
for row in rows('proposal_tex_scan.tsv'):
    path='docs/proposals/'+row['path']; seen.add(root+path)
    verify(path,row['blob_sha'])
    hits=[(i,s) for i,s in enumerate(git('show',rev+':'+root+path).splitlines(),1) if pattern.search(s)]
    expected=int(row['keyword_hits'].split()[0]); assert len(hits)==expected,(path,hits)
    for i,s in hits: print(f'{path}:{i}: {s}')
all_tex={p for p in git('ls-tree','-r','--name-only',rev,'--',root+'docs/proposals').splitlines() if p.endswith('.tex')}
assert seen==all_tex, (seen-all_tex,all_tex-seen)
print(f'All source blobs, proposal trees and {len(seen)} TeX files match; keyword scan reproduced.')

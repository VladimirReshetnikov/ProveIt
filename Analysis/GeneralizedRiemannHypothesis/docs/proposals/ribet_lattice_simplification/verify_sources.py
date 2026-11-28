#!/usr/bin/env python3
"""Verify Git object IDs and proposal scope against a local clone of the pinned revision."""
import csv, subprocess, sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
REV='835c3695d07c0f77060c5cc63f92eeb52a7d21c2'
ROOT='Analysis/GeneralizedRiemannHypothesis/'
PROP=ROOT+'docs/proposals/'
if len(sys.argv)!=2: raise SystemExit('usage: python verify_sources.py /path/to/ProveIt')
REPO=sys.argv[1]
def git(*args):
    return subprocess.check_output(['git','-C',REPO,*args],text=True).strip()
def rows(name):
    with (BASE/name).open() as f: return list(csv.reader(f,delimiter='\t'))[1:]
def verify(path,expected):
    actual=git('rev-parse',f'{REV}:{path}')
    if actual!=expected: raise SystemExit(f'mismatch: {path}: {actual} != {expected}')
for path,sha,*_ in rows('source_audit.tsv'): verify(ROOT+path,sha)
proposals=rows('proposal_audit.tsv')
for path,sha,*_ in proposals: verify(PROP+path,sha)
tex=rows('proposal_tex_inventory.tsv')
for path,sha,*_ in tex: verify(PROP+path,sha)
actual_dirs=set(git('ls-tree','--name-only',f'{REV}:{PROP.rstrip("/")}').splitlines())
assert actual_dirs=={r[0] for r in proposals}, (actual_dirs,{r[0] for r in proposals})
actual_tex={s for s in git('ls-tree','-r','--name-only',f'{REV}:{PROP.rstrip("/")}').splitlines() if s.endswith('.tex')}
assert actual_tex=={r[0] for r in tex}, (actual_tex,{r[0] for r in tex})
print(f'Pinned object IDs verified: {len(rows("source_audit.tsv"))} source files, {len(proposals)} proposal trees, {len(tex)} TeX files.')

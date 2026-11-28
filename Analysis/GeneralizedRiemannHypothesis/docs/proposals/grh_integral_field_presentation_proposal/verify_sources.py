#!/usr/bin/env python3
"""Verify recorded Git objects and repeat the keyword screen in a local clone."""
import csv, re, subprocess, sys
from pathlib import Path
root = Path(__file__).resolve().parent
repo = sys.argv[1] if len(sys.argv)>1 else '.'
rev = 'fd695fd462aa31b25af3335e2a9c3b6e014b055f'
prefix = 'Analysis/GeneralizedRiemannHypothesis/'
pattern = re.compile(r'PrimeDecomposition|relDifferentGen|differentGenPhase|codifferent|coprime discriminant|trace.dual|reciprocal polynomial|residue.orbit|two.generator|smul_eq_iff_exists_frobElem_pow', re.I)
def git(*a):
    return subprocess.check_output(['git','-C',repo,*a])
def rows(name):
    with (root/name).open() as f: return list(csv.reader(f,delimiter='\t'))[1:]
def verify(path,sha):
    actual = git('rev-parse',f'{rev}:{path}').decode().strip()
    assert actual == sha, (path,actual,sha)
for path,sha,*_ in rows('source_anchors.tsv'): verify(prefix+path,sha)
assert git('rev-parse',rev+':'+prefix+'docs/proposals').decode().strip()=='7fd24ac9ab5506bf6d0d21fd52034010a4f72243'
tex = rows('proposal_tex_inventory.tsv')
actual_tex = set(p.removeprefix(prefix+'docs/proposals/') for p in git('ls-tree','-r','--name-only',rev,'--',prefix+'docs/proposals').decode().splitlines() if p.endswith('.tex'))
assert actual_tex == {p for p,_ in tex}
hits=[]
for path,sha in tex:
    p=prefix+'docs/proposals/'+path
    verify(p,sha)
    for j,line in enumerate(git('show',rev+':'+p).decode().splitlines(),1):
        if pattern.search(line): hits.append((path,j,line))
print(f'All {len(rows("source_anchors.tsv"))} source anchors and {len(tex)} TeX blobs verified.')
print('Keyword hits:',len(hits))
for h in hits: print(*h,sep=': ')

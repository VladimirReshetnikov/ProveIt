#!/usr/bin/env python3
"""Reproduce source-only dependency, producer and hash checks for this patch."""
from pathlib import Path
import argparse, json, hashlib, re, subprocess
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);a=ap.parse_args()
here=Path(__file__).resolve().parent
root=Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
prod=root/'rocq/rocq-extension/coq/215'
def h(b):return hashlib.sha256(b).hexdigest()
for n in ['L1_CompPerm','SeedPerm']:
    template=(here/'overlay'/root/'rocqperm'/(n+'.v')).read_bytes()
    expected=(f'(** k225-formal/rocqperm/{n}.v (SHA256 {h(template)}) under namespace K215F. *)\n'
      +template.decode().replace('From NS Require','From K215F Require')).encode()
    assert expected==(here/'overlay'/prod/(n+'.v')).read_bytes()
manifest=json.loads((here/'overlay'/root/'rocq/rocq-extension/manifest.json').read_text())
for n in ['L1_CompPerm','SeedPerm']:
    assert manifest['files'][f'coq/215/{n}.v']==h((here/'overlay'/prod/(n+'.v')).read_bytes())
def graph(patched):
    g={}; files={}
    for p in (a.repo/prod).glob('*.v'):
        q=here/'overlay'/prod/p.name
        if not patched or not q.exists():q=p
        s=re.sub(r'\(\*.*?\*\)','',q.read_text(),flags=re.S)
        deps=[]
        for m in re.finditer(r'From\s+K215F\s+Require\s+(?:(?:Import|Export)\s+)?([\w.\s]+?)\.(?=\s|$)',s):
            deps+=m.group(1).split()
        g[p.stem]=deps;files[p.stem]=q
    seen=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        for d in g[n]:visit(d)
    visit('CorrectDense215')
    return seen,{'modules':len(seen),'lines':sum(len(files[n].read_bytes().splitlines()) for n in seen),'bytes':sum(len(files[n].read_bytes()) for n in seen)}
b,bm=graph(False);c,cm=graph(True)
assert b-c=={'ThmDom'} and not c-b
assert bm['lines']-cm['lines']==59 and bm['bytes']-cm['bytes']==1565
subprocess.run(['git','apply','--check',str(here/'compiler-fusion.patch')],cwd=a.repo,check=True)
print(json.dumps({'source_only':True,'producer_bindings':'PASS','manifest_bindings':'PASS','patch_application':'PASS','before_family_closure':bm,'after_family_closure':cm,'removed':sorted(b-c)},indent=2))

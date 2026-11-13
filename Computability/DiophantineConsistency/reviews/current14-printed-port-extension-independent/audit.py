#!/usr/bin/env python3
"""Independently rederive and compare the current14 port extension source DAG."""
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
BASE=ROOT/'Computability/DiophantineConsistency'
PLAN=BASE/'research/current14-printed-port-extension-plan'
PINS={
    BASE/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
    PLAN/'kernel-manifest.json':'4809f9cb3572bb0bdc47b22fd6a0c0e277c215d7aa322fd1847e8e63152fd6b2',
    PLAN/'masks-manifest.json':'7e6d83edfa707b63e1ad1f6070cad00d01859929dca4a9459063af5e0932a8ff',
    PLAN/'result.json':'cb1817489d0ea7ca5cb3f805acd857a7e22e68659fc664e03b8360d70f4f231c',
    Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json'):'7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in PINS.items():
    if sha(p)!=h:raise RuntimeError('pin mismatch '+str(p))
base,kern,masks,result,provider=[json.loads(p.read_text()) for p in PINS]
cfg=tomllib.loads((ROOT/'lakefile.toml').read_text())
libs={x['name']:ROOT/x.get('srcDir','.') for x in cfg['lean_lib'] if x['name']!='Foundation'}
def remove_comments_and_strings(s):
    out=[];i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1;i+=2
            elif s.startswith('-/',i): depth-=1;i+=2
            else:
                out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif string:
            if s[i]=='\\': out.extend('  ');i+=2
            elif s[i]=='"':out.append(' ');i+=1;string=False
            else:out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('/-',i):depth=1;i+=2
        elif s.startswith('--',i):
            while i<len(s) and s[i]!='\n':i+=1
        elif s[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(s[i]);i+=1
    if depth or string:raise RuntimeError('unterminated comment or string')
    return ''.join(out)
def declared(path):
    out=[]
    for line in remove_comments_and_strings(path.read_text()).splitlines():
        m=re.fullmatch(r'\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*',line)
        if m:
            names=m.group(1).split()
            if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",n) for n in names):
                raise RuntimeError('unsupported import syntax '+str(path))
            out.extend(names)
    return out
rows={};external=set();stack=[];order=[]
def visit(n):
    if n in rows or n in external:return
    if n in stack:raise RuntimeError('cycle '+n)
    top=n.split('.')[0]
    if top not in libs:external.add(n);return
    p=libs[top]/(n.replace('.','/')+'.lean')
    if not p.is_file():raise RuntimeError('missing '+str(p))
    imports=declared(p);stack.append(n)
    for d in imports:visit(d)
    stack.pop();rows[n]={'sha256':sha(p),'imports':imports};order.append(n)
for target in ('DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011'):
    visit(target)
assert len(rows)==84
for manifest in (kern,masks):
    assert manifest['order'][-1]==manifest['target']
    for name,row in manifest['sources'].items():
        assert name in rows and rows[name]['sha256']==row['sha256'] and rows[name]['imports']==row['imports']
assert set(rows)==set(kern['sources'])|set(masks['sources'])
shared=set(rows)&set(base['sources'])
assert len(shared)==23 and all(rows[n]['sha256']==base['sources'][n]['sha256'] and rows[n]['imports']==base['sources'][n]['imports'] for n in shared)
additions=result['extra_project_build_order'];assert len(additions)==len(set(additions))==61 and set(additions)==set(rows)-shared
seen=set(base['sources'])
for n in additions:
    assert all(d not in rows or d in seen for d in rows[n]['imports'])
    seen.add(n)
new=sorted(external-set(base['external_modules']))
assert new==result['new_declared_external_modules']==['Mathlib.Analysis.SpecialFunctions.Pow.Real','Mathlib.NumberTheory.Wilson','Mathlib.Tactic']
assembly=BASE/'research/current14-literal-port-assembly/Current14LiteralPorts.lean'
assert sha(assembly)==result['assembly_source_sha256']
assert declared(assembly)==['DiophantineConsistency.CurrentKernel2011','DiophantineConsistency.CurrentMaskRecipes2011']
pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
objects={}
for name in new:
    p=pkg.joinpath(*name.split('.')).with_suffix('.olean')
    assert p.is_file()
    suffix='/'+name.replace('.','/')+'.olean'
    guard_matches=[key for key in provider['declared_external_guard'] if key.endswith(suffix)]
    assert not guard_matches
    objects[name]={'path':str(p),'realpath':str(p.resolve()),'sha256':sha(p),
                   'foundation_declared_guard_matching_paths':guard_matches}
print(json.dumps({'status':'PASS_SOURCE_ONLY','project_count':len(rows),'shared_count':len(shared),
                  'extra_count':len(additions),'new_direct_external':new,'observed_external_objects':objects,
                  'scope':'Independent source-declared closure and point-in-time object presence, not Lean --deps, rebuild, or package-transitive/dynamic ancestry.'},indent=2,sort_keys=True))

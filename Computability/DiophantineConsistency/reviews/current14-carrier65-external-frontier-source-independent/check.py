#!/usr/bin/env python3
"""Independently reconstruct bounded source/header and seed observations, no Lean."""
from collections import Counter, deque
from pathlib import Path
import hashlib, json, os, re, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D = Path(__file__).resolve().parents[2]
A = D / 'research/current14-carrier65-external-frontier-source-audit'
P = D / 'research/current14-coherent-extension-refactor-retry05-runner'
base_dir = Path('/tmp/current14-standard-fresh-build-20261104')
foundation_dir = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun')
package = foundation_dir / 'package-lib'
toolchain = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
cache = {}
def sha(path):
    p=Path(path).resolve(strict=True)
    if p not in cache:
        with p.open('rb') as f: cache[p]=hashlib.file_digest(f,'sha256').hexdigest()
    return cache[p]
def read(path, digest=None):
    if digest: assert sha(path)==digest, path
    return json.loads(Path(path).read_bytes())
obs=read(A/'observation.json','c64132b0de015ab2b7f7f0682892a8dba8a01edaf7ffad662aaabb42bd4bbdbc')
assert sha(A/'inspect.py')=='10c4ed8530636d40cdfee142950b64300be3e7228d3c40c5bede454230f8083f'
plan=read(P/'plan.json','b0006cd71994ebafccbd65a30d41e11cb8d953f52751b2c98f3884df3e63744c')
state=read(P/'attempt01/state.json','8b7d9a84b2bae01871a6417cb1529f85d5e0a35a1ec21a0cac1007dd159dcc82')
base=read(base_dir/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014')
foundation=read(foundation_dir/'build-all-receipt.json','7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6')
assert len(state['rows'])==240 and state['status']=='FAILED' and base['status']=='PASS'
records={r['module']:r for r in base['records']}; assert len(records)==1000
base_seed={n for r in state['rows'][:239] for n in r['dependencies'] if n in records}
reach=set(); queue=deque(base_seed)
while queue:
    n=queue.popleft()
    if n in reach: continue
    reach.add(n)
    queue.extend(k for k in records[n]['direct_inputs'] if k in records and k not in reach)
base_external={k for r in records.values() for k in r['direct_inputs'] if k not in records}
base_reachable_external={k for n in reach for k in records[n]['direct_inputs'] if k not in records}
prefix_external={n for r in state['rows'][:239] for n in r['dependencies'] if n in plan['external_direct']}
seeds=set(plan['external_direct'])|base_external
assert (len(plan['external_direct']),len(base_external),len(seeds),len(base_seed),len(reach),len(base_reachable_external),len(prefix_external))==(99,106,138,39,172,23,55)
assert set(obs['seed_rows'])==seeds
assert Counter(n.split('.')[0] for n in seeds)=={'Mathlib':99,'Foundation':37,'Init':1,'Lean':1}
# The parser below independently strips comments, then tokenizes each initial
# header line.  It supports only the simple observed forms, not all Lean.
def header(text):
    depth=0; imports=[]; markers=[]
    for line_no,line in enumerate(text.splitlines(),1):
        clean=[]; pos=0
        while pos<len(line):
            pair=line[pos:pos+2]
            if depth:
                if pair=='/-': depth+=1; pos+=2
                elif pair=='-/': depth-=1; pos+=2
                else: pos+=1
            elif pair=='--': break
            elif pair=='/-': depth=1; pos+=2
            else: clean.append(line[pos]); pos+=1
        line=''.join(clean).strip()
        if not line: continue
        if line in ('module','prelude'):
            markers.append(line); continue
        words=line.split()
        public=bool(words and words[0]=='public')
        if public: words=words[1:]
        meta=bool(words and words[0]=='meta')
        if meta: words=words[1:]
        if words and words[0]=='import':
            words=words[1:]; all_=bool(words and words[0]=='all')
            if all_: words=words[1:]
            assert len(words)==1 and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', words[0]),(line_no,line)
            imports.append({'module':words[0], 'public':public,'meta':meta,'all':all_,'line':line_no})
            continue
        assert 'import' not in line.split()[:3], (line_no,line)
        break
    assert depth==0
    return markers,imports
headers=obs['source_headers']; assert len(headers)==777 and not obs['missing_source']
assert {n for n,row in headers.items() if row['depth']==0}==seeds
first_gen={e['module'] for n in seeds for e in headers[n]['imports']} - seeds
assert {n for n,row in headers.items() if row['depth']==1}==first_gen and len(first_gen)==639
edges=[]
for n,row in headers.items():
    p=Path(row['source']); assert sha(p)==row['source_sha256']
    markers, imports=header(p.read_text())
    assert markers==row['markers'] and imports==row['imports'],n
    edges += [{'from':n,**e} for e in imports]
boundary=sorted({e['module'] for e in edges}-set(headers))
assert boundary==obs['boundary_names'] and len(boundary)==764
assert len(edges)==3157
all_edges=[e for e in edges if e['all']]
assert len(all_edges)==13 and len({e['module'] for e in all_edges})==12
assert {json.dumps(x,sort_keys=True) for x in all_edges}=={json.dumps(x,sort_keys=True) for x in obs['import_all_edges']}
assert sum(e['meta'] for e in edges)==464
for n,row in obs['seed_rows'].items():
    assert row['in_plan_external']==(n in plan['external_direct'])
    assert row['in_prefix_external']==(n in prefix_external)
    assert row['in_base_all_external']==(n in base_external)
    assert row['in_base_reachable_external']==(n in base_reachable_external)
    expected_candidates=[root/(n.replace('.','/')+'.olean') for root in (package,toolchain)]
    expected_candidates=[p for p in expected_candidates if p.is_file()]
    assert [str(p) for p in expected_candidates]==[v['path'] for v in row['object_candidates']]
    for v in row['object_candidates']:
        p=Path(v['path']); assert str(p.resolve(strict=True))==v['realpath'] and sha(p)==v['sha256']
    assert sha(expected_candidates[0])==row['recorded_object_sha256']
    saved=set()
    if n in plan['external_direct']:
        saved.add(plan['external_direct'][n]['sha256'])
        assert str(expected_candidates[0].resolve(strict=True))==plan['external_direct'][n]['realpath']
    for r in records.values():
        if n in r['direct_inputs'] and n not in records:
            v=r['direct_inputs'][n]
            assert v['kind']=='package' and sha(v['path'])==v['sha256']
            saved.add(v['sha256'])
    assert saved=={row['recorded_object_sha256']}, n
    assert sha(row['source'])==row['source_sha256']
    suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.trace',
        '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash',
        '.so','.dll','.dylib')
    for suffix in suffixes:
        candidate=package/(n.replace('.','/')+suffix)
        assert os.path.lexists(candidate)==(suffix in row['companions']), (n,suffix)
    for value in row['companions'].values():
        p=Path(value['path']); assert p.stat().st_size==value['bytes'] and str(p.resolve(strict=True))==value['realpath'] and sha(p)==value['sha256']
# Independently compare 11 recorded package suffixes per Foundation seed to
# the same pinned receipt; matching receipt bytes do not prove provenance.
required=('.olean','.olean.private','.olean.server','.ir','.ilean','.trace','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
f_count=0
for n in sorted(n for n in seeds if n.startswith('Foundation.')):
    row=obs['seed_rows'][n]
    assert foundation['objects'][n]==row['recorded_object_sha256']
    assert n in foundation['foundation_source_closure']
    rel=n[len('Foundation.'):].replace('.','/')
    for suffix in required:
        assert suffix in row['companions']
        assert foundation['foundation_artifacts'][rel+suffix]==row['companions'][suffix]['sha256']
        f_count+=1
assert f_count==407
for n, types in obs['import_all_targets'].items():
    assert types['.olean.private'], n
    for entries in types.values():
        for v in entries:
            p=Path(v['path']); assert p.stat().st_size==v['bytes'] and str(p.resolve(strict=True))==v['realpath'] and sha(p)==v['sha256']
print(json.dumps({'scope':'bounded independent reconstruction of recorded seeds, source headers and observed artifacts; no Lean resolution, source-object provenance or runtime closure','seed_count':len(seeds),'reachable_base_records':len(reach),'source_headers':len(headers),'explicit_edges':len(edges),'unexpanded_boundary':len(boundary),'import_all_edges':len(all_edges),'meta_import_edges':sum(e['meta'] for e in edges),'foundation_receipt_matched_artifacts':f_count},sort_keys=True,indent=2))

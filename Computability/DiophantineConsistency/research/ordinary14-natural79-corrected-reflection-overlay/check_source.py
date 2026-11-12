#!/usr/bin/env python3
"""Check the inert natural79 reflection overlay; no Lean or materialization."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=D.parents[1]
PREV=D/'research/ordinary14-natural79-combined-slim-overlay'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p,h):
    raw=p.read_bytes();assert sha(raw)==h,(str(p),sha(raw));return raw
previous=json.loads(pin(PREV/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
projection=json.loads(pin(D/'research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json','5e191072e4760cf91e97524e0d26f9805ef6a7c0b35b2b63e684222e40d5bff7'))
client_original=pin(D/'research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293')
client=pin(D/'research/ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896')
oldimp=b'import DiophantineConsistency.BFS943.Direct80NaturalProjection';newimp=b'import NaturalDvdReflectionSlim'
oldref=b'TenPositive80NaturalProjection.natural_dvd_of_signed';newref=b'NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert client_original.count(oldimp)==client_original.count(oldref)==1
assert client==client_original.replace(oldimp,newimp).replace(oldref,newref)
oldhelper=pin(D/'research/ordinary14-natural79-dvd-reflection-slim-draft/NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb')
helper=pin(D/'research/ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src','90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4')
assert helper==b'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'+oldhelper
old={r['module']:r for r in previous['drafts_topological']}
assert len(old)==195 and 'NaturalDvdReflectionSlim' not in old
files=list((P/'source').iterdir());assert len(files)==196
assert all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in files)
names=[p.name[:-9] for p in files]
assert len(set(names))==196 and set(names)==set(old)|{'NaturalDvdReflectionSlim'}
def imports(data):
    out=[]
    for l in data.decode().splitlines():
        if not l.strip():continue
        m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',l)
        if not m:break
        out.extend(m.group(1).split())
    return out
rows={};qualified=set()
for name in sorted(names):
    path=P/'source'/(name+'.lean.src');data=path.read_bytes()
    if name=='NaturalDvdReflectionSlim':
        assert data==helper
        selected='research/ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src'
        original=None;original_hash=None;kind='corrected-helper'
    else:
        row=old[name]
        original=row['original_path'];original_hash=row['original_sha256'];pin(D/original,original_hash)
        prior=pin(PREV/row['overlay_path'],row['overlay_sha256'])
        if name=='Natural79ZeroWDivisibility':
            assert prior==client_original and data==client
            selected='research/ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src'
            kind='slim-client-alternative'
        else:
            assert data==prior
            selected='research/ordinary14-natural79-combined-slim-overlay/'+row['overlay_path']
            kind='unchanged-79-overlay'
    imps=imports(data);bare=[n for n in imps if '.' not in n];qual=[n for n in imps if '.' in n]
    if name in old and name!='Natural79ZeroWDivisibility':
        assert bare==old[name]['bare_imports'] and qual==old[name]['qualified_imports']
    if name=='NaturalDvdReflectionSlim':
        assert imps==['Foundation.FirstOrder.Arithmetic.IOpen.Basic','DiophantineConsistency.ModelDifferenceRing','Mathlib.Tactic.Ring']
    qualified.update(qual)
    rows[name]={'module':name,'kind':kind,'original_path':original,'original_sha256':original_hash,
       'selected_path':selected,'selected_sha256':sha(data),'overlay_path':'source/'+path.name,
       'overlay_sha256':sha(data),'bare_imports':bare,'qualified_imports':qual}
order=[];seen=set();active=set()
def visit(n):
    assert n in rows,('unresolved bare import',n)
    if n in seen:return
    assert n not in active,('bare import cycle',n)
    active.add(n)
    for m in rows[n]['bare_imports']:visit(m)
    active.remove(n);seen.add(n);order.append(n)
visit('Natural79Endpoint')
assert seen==set(rows),('unreachable snapshots',sorted(set(rows)-seen))
assert len(order)==196
oldproj={r['module']:r for r in previous['qualified_direct_sources']}
proj={n for n in qualified if n.startswith('DiophantineConsistency.')}
removed='DiophantineConsistency.BFS943.Direct80NaturalProjection'
assert proj==set(oldproj)-{removed}
project=[]
for name in sorted(proj):
    row=oldproj[name];p=D/row['path'];pin(p,row['sha256']);project.append(row)
external=qualified-proj
assert external=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Algebra.Ring.Basic','Mathlib.Tactic.Ring'}
oldexternal={r['module']:r for r in previous['external_direct_sources']}
externalrows=[]
for n in sorted(external):
    if n.startswith('Foundation.'):
        p=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation')/(n.replace('.','/')+'.lean')
        h='4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b';pin(p,h)
        externalrows.append({'module':n,'path':str(p),'sha256':h})
    else:
        row=oldexternal[n];pin(ROOT/row['path'],row['sha256']);externalrows.append(row)
assert len(projection['projected_source_candidates'])==5 and len(projection['projected_project_frontier'])==41
assert set(projection['projected_external'])>=external
out={'scope':'inert snapshots and simple initial-header closure only; no Lean/provider/axiom/physical binding claim',
 'root':'Natural79Endpoint','previous_inventory_sha256':sha((PREV/'inventory.json').read_bytes()),
 'provider_projection_sha256':sha((D/'research/ordinary14-natural79-corrected-reflection-provider-cut/observation.json').read_bytes()),
 'draft_count':len(order),'unchanged_79_overlay_snapshots':194,'client_alternatives':1,'new_corrected_helper':1,
 'drafts_topological':[rows[n] for n in order], 'qualified_direct_count':len(project),
 'qualified_direct_sources':project,'removed_project_direct_vs_79':[removed],
 'external_direct_sources':externalrows}
print(json.dumps(out,sort_keys=True,indent=2))

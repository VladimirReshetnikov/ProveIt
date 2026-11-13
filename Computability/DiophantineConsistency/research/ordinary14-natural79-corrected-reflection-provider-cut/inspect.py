#!/usr/bin/env python3
"""Bounded read-only lexical projection and collision observation; no Lean."""
import hashlib, json, os, re, sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')
D = Path(__file__).resolve().parents[2]
O = D/'research/ordinary14-natural79-combined-slim-overlay'
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
PKG = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
FOUNDATION = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/lib/FormalizedFormalLogic-Foundation')
sha = lambda b: hashlib.sha256(b).hexdigest()
def pin(path, expected):
    data = path.read_bytes()
    assert sha(data) == expected, (str(path), sha(data))
    return data
inv = json.loads(pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
prior = json.loads(pin(D/'research/ordinary14-natural79-dvd-reflection-slim-draft/result.json','6ee95a0db3f72c4b49199e301f1f63812e9723b0e55ac8af3662e87722599ea6'))
cut = json.loads(pin(D/'research/ordinary14-natural79-qualified-provider-cut/observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
repair = json.loads(pin(D/'research/ordinary14-natural79-slim-reflection-import-repair/result.json','b441f7d6642584ea2f20bb2643179002dd02b8295252db31516b7ceb70832719'))
orighelper = pin(D/'research/ordinary14-natural79-dvd-reflection-slim-draft/NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb')
helper = pin(D/'research/ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src',repair['candidate_sha256'])
assert helper == b'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'+orighelper
client = pin(D/'research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293')
alt = pin(D/'research/ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896')
oldimp=b'import DiophantineConsistency.BFS943.Direct80NaturalProjection';newimp=b'import NaturalDvdReflectionSlim'
oldref=b'TenPositive80NaturalProjection.natural_dvd_of_signed';newref=b'NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert client.count(oldimp)==client.count(oldref)==1 and alt==client.replace(oldimp,newimp).replace(oldref,newref)
def imports(data):
    result=[]
    for line in data.decode().splitlines():
        if not line.strip(): continue
        m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
        if not m: break
        result.extend(m.group(1).split())
    return result
def evidence(path):
    if not os.path.lexists(path): return None
    if not path.is_file(): return {'path':str(path),'file':False,'symlink':path.is_symlink()}
    return {'path':str(path),'realpath':str(path.resolve(strict=True)),'sha256':sha(path.read_bytes()),'symlink':path.is_symlink()}
rows={r['module']:r for r in inv['drafts_topological']}
assert len(rows)==195 and 'NaturalDvdReflectionSlim' not in rows
qualified=set()
for name,row in rows.items():
    data=pin(O/row['overlay_path'],row['overlay_sha256'])
    assert [n for n in imports(data) if '.' not in n]==row['bare_imports']
    assert [n for n in imports(data) if '.' in n]==row['qualified_imports']
    if name=='Natural79ZeroWDivisibility': assert data==client; data=alt
    qualified.update(n for n in imports(data) if '.' in n)
assert imports(helper)==['Foundation.FirstOrder.Arithmetic.IOpen.Basic','DiophantineConsistency.ModelDifferenceRing','Mathlib.Tactic.Ring']
qualified.update(n for n in imports(helper) if '.' in n)
pending=list(qualified);seen=set();source={};front={};external={}
while pending:
    name=pending.pop()
    if name in seen: continue
    seen.add(name)
    if not name.startswith('DiophantineConsistency.'):
        p=PKG/(name.replace('.','/')+'.olean')
        external[name]={'path':str(p),'present':p.is_file(),'sha256':sha(p.read_bytes()) if p.is_file() else None}
        continue
    obj=P72/(name.replace('.','/')+'.olean');sp=D/'Lean'/(name.replace('.','/')+'.lean')
    assert sp.is_file(),name
    if obj.is_file():
        front[name]={'source_sha256':sha(sp.read_bytes()),'object_path':str(obj),'object_sha256':sha(obj.read_bytes())}
    else:
        deps=imports(sp.read_bytes());source[name]={'path':str(sp.relative_to(D)),'sha256':sha(sp.read_bytes()),'lexical_imports':deps};pending.extend(deps)
assert source==prior['projected_source_candidates']
assert front==prior['projected_project_frontier']
foundation_name='Foundation.FirstOrder.Arithmetic.IOpen.Basic'
assert set(external)==set(prior['projected_external'])|{foundation_name}
assert {n:v for n,v in external.items() if n!=foundation_name}==prior['projected_external']
assert all(v['present'] for v in external.values())
fsource=FOUNDATION/(foundation_name.replace('.','/')+'.lean')
assert sha(fsource.read_bytes())==repair['foundation_source_paths_and_sha256'][str(fsource)]
roots={k:Path(v) for k,v in cut['collision_scan']['roots'].items()}
suffixes=cut['collision_scan']['suffixes']; assert len(roots)==8 and len(suffixes)==13
names=sorted(set(rows)|set(source)|{'NaturalDvdReflectionSlim'})
hits=[]
for label,root in sorted(roots.items()):
    for n in names:
        for suffix in suffixes:
            p=root/(n.replace('.','/')+suffix)
            if os.path.lexists(p):hits.append({'root':label,'module':n,'suffix':suffix,'evidence':evidence(p)})
# Separate scan for dependency-provider names; these are not proposed outputs.
provider_hits=[]
for label,root in sorted(roots.items()):
    for suffix in suffixes:
        p=root/(foundation_name.replace('.','/')+suffix)
        if os.path.lexists(p):provider_hits.append({'root':label,'suffix':suffix,'evidence':evidence(p)})
assert len(names)==201
assert {(h['root'],h['module'],h['suffix']) for h in hits} == {
    ('captured_p72_endpoint','DiophantineConsistency.DiscreteOrderedRingFacts','.olean'),
    ('carrier_retry05','DiophantineConsistency.DiscreteOrderedRingFacts','.olean')}
assert external[foundation_name]['sha256']==evidence(PKG/(foundation_name.replace('.','/')+'.olean'))['sha256']
print(json.dumps({'scope':'bounded lexical source/presence projection and selected-root collision observations only; no Lean or provider authentication',
 'overlay_drafts':len(rows),'inert_helper':1,'direct_qualified_count':len(qualified),
 'candidate_source_sha256':sha(helper),'original_candidate_source_sha256':sha(orighelper),
 'projected_source_candidates':dict(sorted(source.items())), 'projected_project_frontier':dict(sorted(front.items())),
 'projected_external':dict(sorted(external.items())), 'added_external_vs_prior_slim':[foundation_name],
 'foundation_source':evidence(fsource),'foundation_package_root_symlink':{'path':str(PKG/'Foundation'),'realpath':str((PKG/'Foundation').resolve(strict=True)),'symlink':(PKG/'Foundation').is_symlink()},
 'proposed_output_collision_scan':{'names':names,'roots':{k:str(v) for k,v in roots.items()},'suffixes':suffixes,'hits':hits},
 'foundation_provider_name_observations':provider_hits,
 'helper_and_client_not_elaborated':True},sort_keys=True,indent=2))

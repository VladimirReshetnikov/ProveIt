#!/usr/bin/env python3
"""Independent copy/client/cut audit; no Lean or build execution."""
from pathlib import Path
from collections import deque
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ordinary14-natural79-dvd-reflection-slim-draft';O=R/'ordinary14-natural79-combined-slim-overlay';P72=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(path,want):
 raw=path.read_bytes();assert sha(raw)==want,(str(path),sha(raw));return raw
obs=json.loads(pin(P/'result.json','6ee95a0db3f72c4b49199e301f1f63812e9723b0e55ac8af3662e87722599ea6'))
pin(P/'check_source.py','eb4677478077a5eda31303c42310b3db956479cbfc24011f79544a525304b491')
inv=json.loads(pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
cut79=json.loads(pin(R/'ordinary14-natural79-qualified-provider-cut/observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
cut80=json.loads(pin(R/'ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979'))
origin=pin(D/'Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028').decode()
client=pin(R/'ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293').decode()
helper=pin(P/'NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb').decode()
alt=pin(P/'Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896').decode()
ring=pin(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998').decode()
# The theorem itself, not merely its statement, is copied byte-for-byte.
start='theorem natural_dvd_of_signed ';end='\ntheorem graph_natural_projection';end2='\n\nend DiophantineConsistency.NaturalDvdReflectionSlimDraft'
assert origin[origin.index(start):origin.index(end,origin.index(start))]==helper[helper.index(start):helper.index(end2,helper.index(start))]
assert 'BFS943/Direct80NaturalProjection.lean' in helper
for token in ('theorem nonneg_or_nonpos','theorem ι_eq_neg_ι','theorem ι_injective'):assert token in ring
oldimp='import DiophantineConsistency.BFS943.Direct80NaturalProjection';newimp='import NaturalDvdReflectionSlim'
oldref='TenPositive80NaturalProjection.natural_dvd_of_signed';newref='NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert client.count(oldimp)==client.count(oldref)==1
assert alt==client.replace(oldimp,newimp).replace(oldref,newref)
assert '#print axioms DiophantineConsistency.NaturalDvdReflectionSlimDraft.natural_dvd_of_signed' in helper

def headers(text):
 out=[]
 for line in text.splitlines():
  t=line.strip()
  if not t:continue
  if not t.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',t),t
  out.extend(t.split()[1:])
 return out
assert headers(helper)==['DiophantineConsistency.ModelDifferenceRing','Mathlib.Tactic.Ring']
rows={r['module']:r for r in inv['drafts_topological']};assert len(rows)==195
seeds=set(headers(helper));copied=0
for name,row in rows.items():
 data=pin(O/row['overlay_path'],row['overlay_sha256']).decode();copied+=1
 if name=='Natural79ZeroWDivisibility':assert data==client;data=alt
 seeds.update(n for n in headers(data) if '.' in n)
assert 'DiophantineConsistency.BFS943.Direct80NaturalProjection' not in seeds
# Independently breadth-first follow the projected qualified imports to the
# sampled P72/object boundary. This is not Lean's actual dependency resolution.
queue=deque(sorted(seeds));seen=set();sources={};front={};external={}
while queue:
 n=queue.popleft()
 if n in seen:continue
 seen.add(n)
 if not n.startswith('DiophantineConsistency.'):
  obj=PKG/(n.replace('.','/')+'.olean');external[n]={'path':str(obj),'present':obj.is_file(),'sha256':sha(obj.read_bytes()) if obj.is_file() else None};continue
 path=D/'Lean'/(n.replace('.','/')+'.lean');assert path.is_file(),n;raw=path.read_bytes();obj=P72/(n.replace('.','/')+'.olean')
 if obj.is_file():front[n]={'source_sha256':sha(raw),'object_path':str(obj),'object_sha256':sha(obj.read_bytes())}
 else:
  deps=headers(raw.decode());sources[n]={'path':str(path.relative_to(D)),'sha256':sha(raw),'lexical_imports':deps};queue.extend(deps)
assert sources==obs['projected_source_candidates'] and front==obs['projected_project_frontier'] and external==obs['projected_external']
assert len(sources)==5 and len(front)==41 and len(external)==5 and all(r['present'] for r in external.values())
assert set(sources)==set(cut80['source_candidates'])
assert sorted(set(cut79['source_candidates'])-set(sources))==obs['eliminated_source_names'] and len(obs['eliminated_source_names'])==39
assert set(cut80['selected_project_frontier'])<=set(front)
assert set(front)-set(cut80['selected_project_frontier'])=={'DiophantineConsistency.Compact44.ReducedNormSigned'}
assert set(external)==set(cut80['selected_external'])|{'Mathlib.Algebra.Ring.Basic'}
print(json.dumps({'scope':'source copy, two client edits and bounded BFS lexical projection only; no Lean or provider closure',
 'pinned_inputs':10,'theorem_body_exact':True,'client_replacements':2,'overlay_snapshots_checked':copied,
 'projected_missing_sources':len(sources),'removed_from_prior_lexical_cut':len(obs['eliminated_source_names']),
 'projected_frontier_objects':len(front),'projected_external_objects':len(external),'helper_axiom_report_unexecuted':True},sort_keys=True,indent=2))

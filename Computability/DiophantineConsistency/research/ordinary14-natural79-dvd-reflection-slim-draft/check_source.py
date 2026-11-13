#!/usr/bin/env python3
"""Read-only exact helper comparison and lexical cut projection; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];O=D/'research/ordinary14-natural79-combined-slim-overlay'
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105/lib');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
inv=json.loads(pin(O/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
cut79=json.loads(pin(D/'research/ordinary14-natural79-qualified-provider-cut/observation.json','c978df77d6a2c68947f827a31e45ede8070b5b76cd26c7eab2306811d6b2610c'))
cut80=json.loads(pin(D/'research/ordinary14-natural80-qualified-provider-cut/observation.json','c88630304b866b29fe68a11f14f44af210fcd8ea5eed173523ae687c8c157979'))
origin=pin(D/'Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028').decode()
client=pin(D/'research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293').decode()
helper=pin(P/'NaturalDvdReflectionSlim.lean','460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb').decode()
alt=pin(P/'Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896').decode()
a=origin.index('theorem natural_dvd_of_signed ');b=origin.index('\ntheorem graph_natural_projection',a)
c=helper.index('theorem natural_dvd_of_signed ');d=helper.index('\n\nend DiophantineConsistency.NaturalDvdReflectionSlimDraft',c)
assert origin[a:b]==helper[c:d]
oldimp='import DiophantineConsistency.BFS943.Direct80NaturalProjection';newimp='import NaturalDvdReflectionSlim'
oldref='TenPositive80NaturalProjection.natural_dvd_of_signed';newref='NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert client.count(oldimp)==client.count(oldref)==1 and alt==client.replace(oldimp,newimp).replace(oldref,newref)
assert 'import DiophantineConsistency.ModelDifferenceRing\nimport Mathlib.Tactic.Ring\n' in helper
assert '#print axioms DiophantineConsistency.NaturalDvdReflectionSlimDraft.natural_dvd_of_signed' in helper
def imports(text):
 out=[]
 for line in text.splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  out+=m.group(1).split()
 return out
rows={r['module']:r for r in inv['drafts_topological']};assert len(rows)==195 and 'Natural79ZeroWDivisibility' in rows
assert len(imports(helper))==2 and 'NaturalDvdReflectionSlim' in imports(alt)
direct=set()
for name,row in rows.items():
 data=pin(O/row['overlay_path'],row['overlay_sha256']).decode()
 if name=='Natural79ZeroWDivisibility':assert data==client;data=alt
 direct.update(n for n in imports(data) if '.' in n)
direct.update(n for n in imports(helper) if '.' in n)
assert oldimp.split()[-1] not in direct
pending=list(direct);seen=set();source={};front={};external={}
while pending:
 name=pending.pop()
 if name in seen:continue
 seen.add(name)
 if not name.startswith('DiophantineConsistency.'):
  path=PKG/(name.replace('.','/')+'.olean');external[name]={'path':str(path),'present':path.is_file(),'sha256':sha(path.read_bytes()) if path.is_file() else None};continue
 obj=P72/(name.replace('.','/')+'.olean');sp=D/'Lean'/(name.replace('.','/')+'.lean');assert sp.is_file(),name
 if obj.is_file():front[name]={'source_sha256':sha(sp.read_bytes()),'object_path':str(obj),'object_sha256':sha(obj.read_bytes())}
 else:
  deps=imports(sp.read_text());source[name]={'path':str(sp.relative_to(D)),'sha256':sha(sp.read_bytes()),'lexical_imports':deps};pending.extend(deps)
assert set(source)==set(cut80['source_candidates'])
assert set(cut80['selected_project_frontier'])<=set(front) and len(front)==41
assert set(external)==set(cut80['selected_external'])|{'Mathlib.Algebra.Ring.Basic'} and all(x['present'] for x in external.values())
assert len(cut79['source_candidates'])==44 and len(source)==5
print(json.dumps({'scope':'source-only exact helper copy, two client edits and point-in-time lexical presence projection; no Lean or provider-closure claim',
 'origin_theorem_body_byte_identical':True,'client_replacements':2,'inert_overlay_drafts':len(rows),'added_inert_helper':1,
 'prior79_source_candidates':len(cut79['source_candidates']),'projected_source_candidates':dict(sorted(source.items())),
 'eliminated_source_names':sorted(set(cut79['source_candidates'])-set(source)),
 'projected_project_frontier':dict(sorted(front.items())),'projected_external':dict(sorted(external.items())),
 'helper_axiom_report_unexecuted':True},sort_keys=True,indent=2))

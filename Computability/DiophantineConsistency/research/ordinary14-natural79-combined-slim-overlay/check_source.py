#!/usr/bin/env python3
"""Verify inert natural79 overlay and bounded initial headers; never run Lean."""
from pathlib import Path
from collections import defaultdict
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=D.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def pinned(p,h):
 raw=p.read_bytes();assert sha(raw)==h,(str(p),sha(raw));return raw
priorp=D/'research/ordinary14-natural80-combined-slim-overlay/inventory.json'
prior=json.loads(pinned(priorp,'bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
old={r['module']:r for r in prior['drafts_topological']};assert len(old)==184
added={
 'ForcedWDivisibility':('research/ordinary14-natural79-w-model-route/ForcedWDivisibility.lean','111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833'),
 'Natural79ConcreteUnits':('research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d'),
 'Natural79Endpoint':('research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'Natural79ResidueShapes':('research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38'),
 'Natural79WShift':('research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1'),
 'Natural79ZeroWDivisibility':('research/ordinary14-natural79-zero-w-divisibility-client-draft/Natural79ZeroWDivisibility.lean','5166f77208e4af6ed8214663aa3b07550f86796f7183c46e0f1039b0d87c4293'),
 'Natural79ZeroWJPos':('research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'Natural79ZeroWMainNorm':('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'Natural79ZeroWRootCut':('research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec'),
 'Natural79ZeroWUnits':('research/ordinary14-natural79-zero-w-unit-draft/Natural79ZeroWUnits.lean','2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c'),
 'P79NaturalForcedW':('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36')}
assert not set(added)&set(old)
files={p.name[:-9]:p for p in (P/'source').glob('*.lean.src')}
assert all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in (P/'source').iterdir())
assert set(files)==set(old)|set(added) and len(files)==195
# Duplicate bare-source candidates are checked only within this research tree.
by=defaultdict(list)
for path in (D/'research').rglob('*.lean'):by[path.stem].append(path)
def headers(raw):
 out=[]
 for l in raw.decode().splitlines():
  if not l.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',l)
  if not m:break
  out.extend(m.group(1).split())
 return out
rows={};project=set();external=set()
for n in sorted(files):
 if n in old:
  row=old[n];original= D/row['original_path'];pinned(original,row['original_sha256'])
  expected=pinned(D/'research/ordinary14-natural80-combined-slim-overlay'/row['overlay_path'],row['overlay_sha256'])
  kind='natural80-overlay-snapshot';op=row['original_path'];oh=row['original_sha256']
 else:
  op,oh=added[n];original=D/op;expected=pinned(original,oh);kind='natural79-endpoint-addition'
 assert len(by[n])==1 and by[n][0]==original,(n,by[n],str(original))
 actual=files[n].read_bytes();assert actual==expected,n
 imps=headers(actual);bare=[x for x in imps if '.' not in x];qual=[x for x in imps if '.' in x]
 if n in old:assert bare==old[n]['bare_imports'] and qual==old[n]['qualified_imports'],n
 project.update(x for x in qual if x.startswith('DiophantineConsistency.'))
 external.update(x for x in qual if not x.startswith('DiophantineConsistency.'))
 rows[n]={'module':n,'kind':kind,'original_path':op,'original_sha256':oh,
  'overlay_path':'source/'+n+'.lean.src','overlay_sha256':sha(actual),'bare_imports':bare,'qualified_imports':qual}
# Traverse the actual selected overlay headers, not an original-source inventory.
order=[];seen=set();active=set()
def visit(n):
 assert n in rows,('unresolved bare import',n)
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n)
 for m in rows[n]['bare_imports']:visit(m)
 active.remove(n);seen.add(n);order.append(n)
visit('Natural79Endpoint');assert seen==set(rows),('unreachable snapshots',sorted(set(rows)-seen))
assert set(external)=={'Mathlib.Algebra.Ring.Basic','Mathlib.Tactic.Ring'}
oldproj={r['module']:r for r in prior['qualified_direct_sources']}
extra={'DiophantineConsistency.BFS943.Direct80NaturalProjection':'85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028',
 'DiophantineConsistency.Compact44.ReducedNormSigned':'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c'}
assert project==set(oldproj)|set(extra)
qualified=[]
for name in sorted(project):
 path=D/'Lean'/('/'.join(name.split('.'))+'.lean');raw=path.read_bytes()
 if name in oldproj:assert str(path.relative_to(D))==oldproj[name]['path'] and sha(raw)==oldproj[name]['sha256'],name
 else:assert sha(raw)==extra[name],name
 qualified.append({'module':name,'path':str(path.relative_to(D)),'sha256':sha(raw)})
externalpins={'Mathlib.Algebra.Ring.Basic':'2827d8284708b7c08f57af71cbcbb31a5fa0500485457524682956b36c5b9aab',
 'Mathlib.Tactic.Ring':'d3ef5c49ebbd1108ce3f935e5ad95485e143abf02f28c027dba4bb6f3be8196e'}
external_sources=[]
for name in sorted(external):
 path=ROOT/'.lake/packages/mathlib'/('/'.join(name.split('.'))+'.lean')
 raw=pinned(path,externalpins[name]);external_sources.append({'module':name,'path':str(path.relative_to(ROOT)),'sha256':sha(raw)})
out={'scope':'inert source snapshots and bounded initial-header closure only; no Lean/provider/axiom/physical binding claim',
 'natural80_combined_inventory_sha256':sha(priorp.read_bytes()),'root':'Natural79Endpoint',
 'draft_count':len(order),'reused_natural80_drafts':len(old),'added_natural79_modules':sorted(added),
 'drafts_topological':[rows[n] for n in order],'qualified_direct_count':len(qualified),
 'qualified_direct_sources':qualified,'added_project_direct_vs_natural80':sorted(extra),
 'external_direct_sources':external_sources}
print(json.dumps(out,sort_keys=True,indent=2))

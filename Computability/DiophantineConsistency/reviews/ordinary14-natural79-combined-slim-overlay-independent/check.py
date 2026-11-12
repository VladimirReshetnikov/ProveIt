#!/usr/bin/env python3
"""Independent byte/header audit of inert natural79 snapshots; no Lean."""
import hashlib,json,re,sys
from collections import Counter,defaultdict
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];R=D/'research';P=R/'ordinary14-natural79-combined-slim-overlay'
def sha(data):return hashlib.sha256(data).hexdigest()
def pinned(path,want):
 b=path.read_bytes();assert sha(b)==want,(str(path),sha(b));return b
invpath=P/'inventory.json';inv=json.loads(pinned(invpath,'7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
pinned(P/'check_source.py','9a65f6e207206098d0e61df2322d74d01544cd05d7f8b809d8d482562cec4022')
O=R/'ordinary14-natural80-combined-slim-overlay';old=json.loads(pinned(O/'inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
rows=inv['drafts_topological'];prior={r['module']:r for r in old['drafts_topological']}
assert len(rows)==len({r['module'] for r in rows})==195 and len(prior)==184
assert inv['root']=='Natural79Endpoint' and inv['draft_count']==195 and inv['reused_natural80_drafts']==184
expected={'P79NaturalForcedW','Natural79ResidueShapes','Natural79ZeroWUnits','Natural79ConcreteUnits','Natural79ZeroWJPos','Natural79ZeroWMainNorm','ForcedWDivisibility','Natural79ZeroWRootCut','Natural79ZeroWDivisibility','Natural79WShift','Natural79Endpoint'}
assert {r['module'] for r in rows}-set(prior)==expected==set(inv['added_natural79_modules']) and set(prior)<={r['module'] for r in rows}
files=list((P/'source').iterdir());assert all(x.is_file() and not x.is_symlink() and x.name.endswith('.lean.src') for x in files)
assert {x.name for x in files}=={r['module']+'.lean.src' for r in rows}
# Candidate-name uniqueness is checked in the research tree only.
by=defaultdict(list)
for p in R.rglob('*.lean'):by[p.stem].append(p)
def headers(text):
 names=[]
 for line in text.splitlines():
  t=line.strip()
  if not t:continue
  if not t.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',t),t
  names.extend(t.split()[1:])
 return names
seen=set();nodes={};direct=set();kinds=Counter()
for row in rows:
 n=row['module'];original=D/row['original_path'];snap=P/row['overlay_path']
 assert row['overlay_path']=='source/'+n+'.lean.src'
 ob=pinned(original,row['original_sha256']);sb=pinned(snap,row['overlay_sha256'])
 assert len(by[n])==1 and by[n][0]==original,(n,[str(x) for x in by[n]])
 if n in prior:
  assert row['kind']=='natural80-overlay-snapshot';oldrow=prior[n]
  assert oldrow['original_path']==row['original_path'] and oldrow['original_sha256']==row['original_sha256']
  assert sb==pinned(O/oldrow['overlay_path'],oldrow['overlay_sha256'])
 else:assert row['kind']=='natural79-endpoint-addition' and ob==sb
 kinds[row['kind']]+=1
 imps=headers(sb.decode());bare=[x for x in imps if '.' not in x];qualified=[x for x in imps if '.' in x]
 assert bare==row['bare_imports'] and qualified==row['qualified_imports']
 assert set(bare)<=seen,(n,set(bare)-seen);seen.add(n);nodes[n]=bare;direct.update(qualified)
assert kinds=={'natural80-overlay-snapshot':184,'natural79-endpoint-addition':11}
reach=set();todo=[inv['root']]
while todo:
 n=todo.pop()
 if n in reach:continue
 assert n in nodes,n;reach.add(n);todo.extend(nodes[n])
assert reach==set(nodes) and len(reach)==195
# Verify all direct project/external source bytes independently of imports.
q={r['module']:r for r in inv['qualified_direct_sources']};ext={r['module']:r for r in inv['external_direct_sources']}
assert len(q)==42 and len(ext)==2 and set(q)|set(ext)==direct and not set(q)&set(ext)
for n,row in q.items():
 assert row['path']=='Lean/'+n.replace('.','/')+'.lean';pinned(D/row['path'],row['sha256'])
for n,row in ext.items():
 assert row['path']=='.lake/packages/mathlib/'+n.replace('.','/')+'.lean';pinned(ROOT/row['path'],row['sha256'])
qold={r['module'] for r in old['qualified_direct_sources']}
extra={'DiophantineConsistency.BFS943.Direct80NaturalProjection','DiophantineConsistency.Compact44.ReducedNormSigned'}
assert set(q)==qold|extra and set(q)-qold==set(inv['added_project_direct_vs_natural80'])==extra
assert set(ext)=={'Mathlib.Algebra.Ring.Basic','Mathlib.Tactic.Ring'}
print(json.dumps({'scope':'independent bounded snapshot/header review; no Lean, provider, axiom or physical binding',
 'overlay_inventory_sha256':sha(invpath.read_bytes()),'drafts':len(rows),'natural80_snapshots':kinds['natural80-overlay-snapshot'],
 'natural79_additions':kinds['natural79-endpoint-addition'],'endpoint_reachable':len(reach),
 'direct_project_sources':len(q),'direct_mathlib_sources':len(ext),'research_tree_unique_names':len(nodes)},sort_keys=True,indent=2))

#!/usr/bin/env python3
"""Check inert beta-only overlay and actual bare-header closure, no Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ROOT=D.parents[1]
PREV=D/'research/ordinary14-natural79-corrected-reflection-overlay'
ALT=D/'research/ordinary14-natural79-beta-only-zero-w-draft/source'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(path,h):
 b=path.read_bytes();assert sha(b)==h,(str(path),sha(b));return b
previous=json.loads(pin(PREV/'inventory.json','fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434'))
author=json.loads(pin(D/'research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json','5331a284de1853e0314c9346c7cc922701a64c99a7328f15b66cbfb7827cba24'))
review=json.loads(pin(D/'reviews/ordinary14-natural79-beta-only-zero-w-independent/result.json','a82524b1c97d283766f477228eab6108f12439b95f99efbdf68a422791b6e324'))
old={r['module']:r for r in previous['drafts_topological']};assert len(old)==196
replace={
 'Natural79ZeroWMainNorm':'82d5e0219a93d826b7eff180cfc33c062e1fece7fa18a198208cc787a0a7ee7b',
 'Natural79ZeroWRootCut':'2be6d79d7cf0bbf86139da63b1120f93509a3dd49ee89a4e221ec6c07ecc7a3d',
 'Natural79ZeroWDivisibility':'d5240f8385c2a0bd472f25d080c9b4f3312a24ac995dcca51d1a6ac7269acf7f',
 'Natural79Endpoint':'da1bbfbc339c26ea5763e5ff4c1aaa885898dab9c3fafd21854b8b69e5c54b7b'}
assert all(author['inert_snapshots'][n+'.lean.src']==h for n,h in replace.items())
for n,h in replace.items():
 pin(ALT/(n+'.lean.src'),h)
 assert review['inputs']['new_'+{'Natural79ZeroWMainNorm':'main','Natural79ZeroWRootCut':'root','Natural79ZeroWDivisibility':'div','Natural79Endpoint':'endpoint'}[n]]['sha256']==h
# Recheck every predecessor snapshot and its exact selected and original source,
# including the one no longer reachable. This does not authenticate Lean objects.
for n,r in old.items():
 data=pin(PREV/r['overlay_path'],r['overlay_sha256'])
 assert pin(D/r['selected_path'],r['selected_sha256'])==data,n
 if r['original_path'] is not None:pin(D/r['original_path'],r['original_sha256'])
def imports(data):
 result=[]
 for line in data.decode().splitlines():
  if not line.strip():continue
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)\s*',line)
  if not m:break
  result.extend(m.group(1).split())
 return result
selected={n:(ALT/(n+'.lean.src') if n in replace else PREV/r['overlay_path']) for n,r in old.items()}
seen=set();active=set();order=[]
def visit(n):
 assert n in selected,('unresolved bare import',n)
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n)
 for dep in imports(selected[n].read_bytes()):
  if '.' not in dep:visit(dep)
 active.remove(n);seen.add(n);order.append(n)
visit('Natural79Endpoint')
assert set(old)-seen=={'Natural79ZeroWJPos'} and set(replace)<=seen and len(order)==195
files=list((P/'source').iterdir());assert len(files)==195
assert all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in files)
names=[p.name[:-9] for p in files];assert len(set(names))==195 and set(names)==seen
rows={};qualified=set()
for n in sorted(seen):
 p=P/'source'/(n+'.lean.src');data=p.read_bytes();assert data==selected[n].read_bytes(),n
 imps=imports(data);bare=[x for x in imps if '.' not in x];qual=[x for x in imps if '.' in x]
 if n not in replace:assert bare==old[n]['bare_imports'] and qual==old[n]['qualified_imports'],n
 qualified.update(qual)
 rows[n]={'module':n,'kind':'beta-only-alternative' if n in replace else 'unchanged-corrected-overlay',
  'selected_path':str(selected[n].relative_to(D)),'selected_sha256':sha(data),
  'previous_overlay_sha256':old[n]['overlay_sha256'],'overlay_path':'source/'+p.name,'overlay_sha256':sha(data),
  'bare_imports':bare,'qualified_imports':qual}
oldproject={r['module']:r for r in previous['qualified_direct_sources']}
oldexternal={r['module']:r for r in previous['external_direct_sources']}
project={n for n in qualified if n.startswith('DiophantineConsistency.')};external=qualified-project
assert project==set(oldproject) and external==set(oldexternal)
for n in project:
 row=oldproject[n];pin(D/row['path'],row['sha256'])
for n in external:
 row=oldexternal[n];path=Path(row['path']);path=path if path.is_absolute() else ROOT/path;pin(path,row['sha256'])
# The former module is not a bare import. Its name can still appear in the
# copied lemma's attribution comment; no declaration-resolution claim follows.
assert all('Natural79ZeroWJPos' not in r['bare_imports'] for r in rows.values())
out={'scope':'inert source snapshots and actual simple-header closure only; no Lean, provider, axiom or physical-binding claim',
 'root':'Natural79Endpoint','previous_inventory_sha256':sha((PREV/'inventory.json').read_bytes()),
 'beta_only_author_receipt_sha256':sha((D/'research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json').read_bytes()),
 'beta_only_review_receipt_sha256':sha((D/'reviews/ordinary14-natural79-beta-only-zero-w-independent/result.json').read_bytes()),
 'draft_count':len(order),'unchanged_corrected_snapshots':len(order)-len(replace),'selected_beta_only_alternatives':sorted(replace),
 'unreachable_previous_modules':sorted(set(old)-seen),
 'drafts_topological':[rows[n] for n in order],
 'qualified_direct_sources':[oldproject[n] for n in sorted(project)],
 'external_direct_sources':[oldexternal[n] for n in sorted(external)],
 'project_direct_added':sorted(project-set(oldproject)),'project_direct_removed':sorted(set(oldproject)-project),
 'external_direct_added':sorted(external-set(oldexternal)),'external_direct_removed':sorted(set(oldexternal)-external)}
print(json.dumps(out,sort_keys=True,indent=2))

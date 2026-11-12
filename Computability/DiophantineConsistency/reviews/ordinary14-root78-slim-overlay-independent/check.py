from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-root78-slim-overlay'
orig=json.loads((D/'research/ordinary14-root78-endpoint-import-inventory/inventory.json').read_text())
inv=json.loads((A/'inventory.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
rows={r['module']:r for r in orig['drafts_topological']}
mods={r['module']:r for r in inv['drafts_topological']}
assert len(rows)==138 and len(mods)==139 and set(mods)==set(rows)|{'CompactPortBoundsSlim'}
assert mods['Root78Endpoint']==inv['drafts_topological'][-1]
expected={'CompactEquivalence':(1,1),'Compact78To85':(0,1),'Compact78To86':(0,1),'CompactEquivalence8687':(1,1),'CompactEquivalence8788':(1,1),'Quotient88PositiveBridge':(1,1)}
oldimp=b'import DiophantineConsistency.Compact44.C44Short15Facts'
newimp=b'import CompactPortBoundsSlim'
oldcall=b'C44Short15Facts.port_bounds'
newcall=b'CompactPortBoundsSlimDraft.port_bounds'
changed={}
for module,row in rows.items():
 old=(D/row['path']).read_bytes(); new=(A/mods[module]['path']).read_bytes()
 assert sha(old)==row['sha256']==mods[module]['source_sha256']
 assert sha(new)==mods[module]['overlay_sha256']
 assert new==old.replace(oldimp,newimp).replace(oldcall,newcall)
 if old!=new:changed[module]=(old.count(oldimp),old.count(oldcall))
 assert oldimp not in new and oldcall not in new
assert changed==expected
helper=(D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean').read_bytes()
assert helper==(A/mods['CompactPortBoundsSlim']['path']).read_bytes()
assert b'namespace DiophantineConsistency.CompactPortBoundsSlimDraft' in helper
assert b'theorem port_bounds ' in helper
order={r['module']:i for i,r in enumerate(inv['drafts_topological'])}
for n,r in mods.items():
 text=(A/r['path']).read_text()
 assert re.search(r'^namespace DiophantineConsistency\.',text,re.M) or n not in expected
 bare=[x for x in re.findall(r'^import ([A-Za-z0-9_.]+)\s*$',text,re.M) if '.' not in x]
 assert bare==r['bare_imports'], n
 assert all(x in order and order[x]<order[n] for x in bare),(n,bare)
# Only explore the six changed clients; guard against combinatorial path explosion by
# independently computing a shortest reachable path via breadth-first traversal.
def shortest(n):
 q=[(n,)];seen={n}
 while q:
  path=q.pop(0)
  if path[-1]=='CompactPortBoundsSlim':return list(path)
  for m in mods[path[-1]]['bare_imports']:
   if m not in seen:seen.add(m);q.append(path+(m,))
 raise AssertionError(n)
helperpaths={n:shortest(n) for n in expected}
reachable=set(); q=['Root78Endpoint']
while q:
 n=q.pop()
 if n in reachable: continue
 reachable.add(n); q.extend(mods[n]['bare_imports'])
assert reachable == set(mods)

# The author lexical traversal is replayed; it is not Lean's resolver.
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==inv
print(json.dumps({'author_readme_sha256':sha((A/'README.md').read_bytes()),'author_checker_sha256':sha((A/'check_source.py').read_bytes()),'author_inventory_sha256':sha((A/'inventory.json').read_bytes()),'original_inventory_sha256':sha((D/'research/ordinary14-root78-endpoint-import-inventory/inventory.json').read_bytes()),'snapshot_count':len(mods),'changed_clients':{n:{'imports':v[0],'calls':v[1],'helper_path':helperpaths[n]} for n,v in sorted(changed.items())},'overlay_helper_sha256':sha(helper),'snapshot_exact_edit_check':True,'bare_import_topological_check':True,'author_receipt_replayed':True,'lean_run':False},sort_keys=True,indent=2))

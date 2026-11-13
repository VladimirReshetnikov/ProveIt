#!/usr/bin/env python3
"""Independent byte, dependency-header, and attributed-theorem comparison. No Lean."""
from collections import Counter
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]; ROOT=D.parents[1]
def digest(b):return hashlib.sha256(b).hexdigest()
def pinned(path,expected):
 b=path.read_bytes();assert digest(b)==expected,(path,digest(b));return b
new=D/'research/ordinary14-natural79-corrected-reflection-overlay'
old79=D/'research/ordinary14-natural79-combined-slim-overlay'
old80=D/'research/ordinary14-natural80-combined-slim-overlay'
info=json.loads(pinned(new/'inventory.json','fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434'))
i79=json.loads(pinned(old79/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
i80=json.loads(pinned(old80/'inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
records=info['drafts_topological'];byname={r['module']:r for r in records};p79={r['module']:r for r in i79['drafts_topological']};p80={r['module']:r for r in i80['drafts_topological']}
assert len(records)==len(byname)==196 and len(p79)==195 and len(p80)==184
assert set(byname)==set(p79)|{'NaturalDvdReflectionSlim'} and set(p80)<set(p79)
files=list((new/'source').iterdir());assert len(files)==196
assert all(f.is_file() and not f.is_symlink() and f.name.endswith('.lean.src') for f in files)
assert {f.name for f in files}=={n+'.lean.src' for n in byname}
# Check actual bytes in both ancestry generations, rather than their inventory claims alone.
client='Natural79ZeroWDivisibility';helper='NaturalDvdReflectionSlim'
for n in p79:
 before=(old79/p79[n]['overlay_path']).read_bytes();current=(new/byname[n]['overlay_path']).read_bytes()
 assert digest(before)==p79[n]['overlay_sha256']
 if n!=client:assert before==current
 if n in p80:
  base=(old80/p80[n]['overlay_path']).read_bytes()
  assert digest(base)==p80[n]['overlay_sha256'] and base==before==current
# The sole client replacement changes exactly one direct import and theorem reference.
c0=(old79/p79[client]['overlay_path']).read_bytes(); c1=(new/byname[client]['overlay_path']).read_bytes()
a=b'import DiophantineConsistency.BFS943.Direct80NaturalProjection';b=b'import NaturalDvdReflectionSlim'
x=b'TenPositive80NaturalProjection.natural_dvd_of_signed';y=b'NaturalDvdReflectionSlimDraft.natural_dvd_of_signed'
assert c0.count(a)==c0.count(x)==1 and c1==c0.replace(a,b).replace(x,y)
prior=D/'research/ordinary14-natural79-dvd-reflection-slim-draft/NaturalDvdReflectionSlim.lean'
helper0=pinned(prior,'460a52783433fa02c1e9a695e69dcfb8d5c839e3d82d4d26df68816aa67c1ceb')
helper1=(new/byname[helper]['overlay_path']).read_bytes()
assert helper1==b'import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n'+helper0
assert helper1==pinned(D/'research/ordinary14-natural79-slim-reflection-import-repair/NaturalDvdReflectionSlim.lean.src','90acd025abeaf3e687a28e1e4d2c8695f8443340848430419e3057c4c7ff33f4')
original=pinned(D/'Lean/DiophantineConsistency/BFS943/Direct80NaturalProjection.lean','85e1fdcee61eeea97af1dead36de5f6593a94fb7c1f63678922ef0909b128028').decode()
# Compare source theorem statements and bodies exactly, including both sign branches.
def theorem(s):
 return s[s.index('theorem natural_dvd_of_signed'):].split('\n\ntheorem ',1)[0].split('\n\nend ',1)[0].rstrip()
assert theorem(original)==theorem(helper1.decode())
# Parse the simple initial headers; verify recorded order AND independent reachability.
headers={};actual_qual=set();idx={r['module']:i for i,r in enumerate(records)}
for r in records:
 p=new/r['overlay_path'];raw=p.read_bytes();assert digest(raw)==r['overlay_sha256']==r['selected_sha256']
 assert (D/r['selected_path']).read_bytes()==raw
 if r['original_path'] is not None:assert digest((D/r['original_path']).read_bytes())==r['original_sha256']
 entries=[]
 for line in raw.decode().splitlines():
  if not line.strip():continue
  if not line.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*\s*',line),line
  entries.extend(line.split()[1:])
 bare=[z for z in entries if '.' not in z];qualified=[z for z in entries if '.' in z]
 assert bare==r['bare_imports'] and qualified==r['qualified_imports']
 assert all(z in idx and idx[z]<idx[r['module']] for z in bare)
 actual_qual.update(qualified);headers[r['module']]=bare
seen=set();todo=['Natural79Endpoint']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(headers[n])
assert seen==set(byname)
proj={x for x in actual_qual if x.startswith('DiophantineConsistency.')};ext=actual_qual-proj
expected={r['module']:r for r in info['qualified_direct_sources']};assert proj==set(expected) and len(proj)==41
priorproj={r['module'] for r in i79['qualified_direct_sources']}
assert proj==priorproj-{'DiophantineConsistency.BFS943.Direct80NaturalProjection'}
for r in expected.values():assert digest((D/r['path']).read_bytes())==r['sha256']
external={r['module']:r for r in info['external_direct_sources']}
assert ext==set(external)=={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Algebra.Ring.Basic','Mathlib.Tactic.Ring'}
for r in external.values():
 p=Path(r['path']);p=p if p.is_absolute() else ROOT/p
 assert digest(p.read_bytes())==r['sha256']
assert Counter(r['kind'] for r in records)=={'unchanged-79-overlay':194,'slim-client-alternative':1,'corrected-helper':1}
assert headers[client].count(helper)==1
assert byname[helper]['qualified_imports']==['Foundation.FirstOrder.Arithmetic.IOpen.Basic','DiophantineConsistency.ModelDifferenceRing','Mathlib.Tactic.Ring']
print(json.dumps({'scope':'independent snapshot bytes, initial headers and theorem body comparison; no Lean or provider proof',
 'pinned_inventories':3,'snapshot_count':196,'prior_79_unchanged':194,'prior_80_preserved':184,
 'client_exact_two_replacements':True,'helper_exact_added_import_and_copied_body':True,
 'qualified_project_sources':len(proj),'external_direct_sources':sorted(ext),
 'all_reachable_in_dependency_first_order':True,'lean_executed':False},sort_keys=True,indent=2))

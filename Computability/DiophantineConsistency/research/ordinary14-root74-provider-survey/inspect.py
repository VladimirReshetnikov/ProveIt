#!/usr/bin/env python3
"""Read-only bounded root74 provider/source survey; never invokes Lean."""
from pathlib import Path
import hashlib,json,os,re
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1]
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105');BASE=Path('/tmp/current14-standard-fresh-build-20261104');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json':'2977037ef7d1a8ebe7e9fc6a7363e9c03e887577750c70f04a573389bc839cb7',D/'research/ordinary14-root74-slim-overlay/inventory.json':'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e',D/'research/ordinary14-root78-slim-overlay/inventory.json':'f788b0c3ec66615d670d028ae123e57a06441fb8c46672e9ca82da0cb0b6d7d8',P72/'progress.json':'f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a',P72/'source-snapshot.json':'4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8',P72/'rows/0027.json':'e8e9d39f88fb1b0184104f7ff992af70a75af83270789dac31dad3a6cf1e2653',P72/'rows/0028.json':'dfac2112c641cbd0eb8d344b15ec445e84b837f659ed029910f8a90c7190a978',BASE/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',ROOT/'lean-toolchain':'2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e',ROOT/'lake-manifest.json':'95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665',TOOL.parent.parent/'bin/lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
for p,h in pins.items():assert hashfile(p)==h,(str(p),hashfile(p),h)
base=json.loads((BASE/'state.json').read_text());progress=json.loads((P72/'progress.json').read_text());snap=json.loads((P72/'source-snapshot.json').read_text());assert base['status']=='PASS' and progress['status']=='PASS'
orig=json.loads((D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json').read_text());slim=json.loads((D/'research/ordinary14-root74-slim-overlay/inventory.json').read_text());prior=json.loads((D/'research/ordinary14-root78-slim-overlay/inventory.json').read_text())
a={r['module'] for r in slim['drafts_topological']};b={r['module'] for r in prior['drafts_topological']};assert len(a)==159 and len(b)==139 and len(a-b)==21 and b-a=={'Root78Endpoint'}
def obj(root,n):return root/Path(*n.split('.')).with_suffix('.olean')
missing=[]
for row in orig['qualified_direct_sources']:
 p=D/row['path'];assert hashfile(p)==row['sha256']
 if not obj(P72/'lib',row['module']).is_file():missing.append(row['module'])
assert set(missing)=={'DiophantineConsistency.Compact44.C44Short15Facts','DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts'}
def walk(seeds):
 pending=list(seeds);seen=set();new=set();front=set();external=set()
 while pending:
  n=pending.pop()
  if n in seen:continue
  seen.add(n)
  if not n.startswith('DiophantineConsistency.'):
   external.add(n);continue
  if obj(P72/'lib',n).is_file():front.add(n);continue
  p=D/'Lean'/Path(*n.split('.')).with_suffix('.lean');assert p.is_file(),n
  new.add(n)
  for line in p.read_text().splitlines():
   m=re.match(r'^import\s+([^\s]+)',line)
   if m:pending.append(m.group(1))
   elif line.strip() and not line.strip().startswith(('--','/-','-/','*')):break
 return sorted(new),sorted(front),sorted(external)
new,front,external=walk(slim['direct_qualified']);assert new==sorted(['DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt','DiophantineConsistency.DiscreteOrderedRingFacts']);assert len(front)==31 and len(external)==4
external_objects={}
for name in external:
 p=obj(PKG,name);assert p.is_file(),name
 external_objects[name]={'path':str(p),'realpath':str(p.resolve(strict=True)),'sha256':hashfile(p)}
def checkslots(slots):
 for path,expected in slots.items():
  p=Path(path)
  if expected is None:assert not os.path.lexists(p),path
  else:assert str(p.resolve(strict=True))==expected['realpath'] and hashfile(p)==expected['sha256'],path
 return len(slots)
row27=json.loads((P72/'rows/0027.json').read_text());row28=json.loads((P72/'rows/0028.json').read_text());assert row27['status']=='PASS' and row27['module']=='DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011'
for dep in row27['dependencies'].values():
 p=Path(dep['path']);assert str(p.resolve(strict=True))==dep['realpath'] and hashfile(p)==dep['sha256']
row27guards=checkslots(row27['direct_guard']);checkslots(row28['direct_guard'])
factorobj=obj(P72/'lib',row27['module']);assert hashfile(factorobj)==row27['object_sha256']=='e357624f5ab38852b316b0b492050dbc1ae4c0f90c90fc8cb0481c9061529f65';assert hashfile(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean')==row27['source_sha256']
negname='DiophantineConsistency.ArithmeticNegativeNorms';rec=next(r for r in base['records'] if r['module']==negname);assert rec['exit']==0
negobj=obj(P72/'lib',negname);assert hashfile(negobj)==rec['object_sha256']=='33cf47041c950f77cd4535d629dcddfa27ff9ea1fcd21cc1af0fb732dd5eb319';assert hashfile(D/'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean')==rec['source_sha256'];slots=checkslots(base['outputs'][negname])
for value in rec['direct_inputs'].values():assert hashfile(Path(value['path']))==value['sha256']
discrete='DiophantineConsistency.DiscreteOrderedRingFacts';assert discrete not in snap and not any(r['module']==discrete for r in base['records']) and not obj(P72/'lib',discrete).exists() and not obj(BASE/'lib',discrete).exists()
init={}
for suff in ('.olean','.olean.private','.olean.server','.ir','.ilean'):
 p=PKG/('Init'+suff);q=TOOL/('Init'+suff);init[suff]={'package_exists':p.is_file(),'package_realpath':str(p.resolve()) if p.is_file() else None,'core_exists':q.is_file(),'core_realpath':str(q.resolve()) if q.is_file() else None,'core_sha256':hashfile(q) if q.is_file() else None}
 if suff!='.ilean':assert p.resolve(strict=True)==q.resolve(strict=True) and hashfile(p)==hashfile(q)
roots=[P72/'lib',BASE/'lib',PKG,TOOL,ROOT/'.lake/build/lib/lean'];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib'];names=sorted(a|set(new));hits=[]
for root in roots:
 for name in names:
  for suffix in suffixes:
   path=root/(name.replace('.','/')+suffix)
   if os.path.lexists(path):hits.append(str(path))
print(json.dumps({'scope':'read-only point-in-time lexical and selected recorded provider checks; no Lean, complete transitive provider or readiness proof','pins':{str(p):h for p,h in pins.items()},'bare_count':len(a),'new_vs_slim78':sorted(a-b),'omitted_vs_slim78':sorted(b-a),'original_direct_missing_p72':missing,'slim_cut_new_sources':new,'slim_cut_frontier':front,'slim_cut_external':external_objects,'factor_units_object':{'path':str(factorobj),'realpath':str(factorobj.resolve()),'sha256':hashfile(factorobj),'row27_guard_count':row27guards},'negative_norm_object':{'path':str(negobj),'realpath':str(negobj.resolve()),'sha256':hashfile(negobj),'base_output_guard_count':slots,'direct_inputs_checked':len(rec['direct_inputs'])},'discrete_source_sha256':hashfile(D/'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean'),'init':init,'collision_check':{'name_count':len(names),'root_count':len(roots),'suffix_count':len(suffixes),'hits':hits}},sort_keys=True,indent=2))

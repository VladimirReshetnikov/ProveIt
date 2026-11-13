#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-direct-four-block-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-boundary-concrete-zero-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='988dd618c628d3ee9e76391a4a95c871ccbb8ce83292ebe01ac27a7e8dd54f20'
assert sha(OO/'terminal.json')=='b0b4568809866bd1dab298decec302eece80193a6bcaf953cbfe8315e9bae0cb'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='831e409ac02787ba797b0edffb9a6d7092ffead067823e5ab295b3d951c2447e'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='dab1c59cd5032829d019846170171b99e682b07d6fa0aec20cca2ada43cdd82c'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='1405f58decb30ba349a3e0c7b5bc6afab01fbca4082e112fb513210336fa436e'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="'Trace74DirectFourBlock.rank_identity' depends on axioms: [propext, Quot.sound]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='6e977f68e25e4bbc290d4c6b43f67f429696a500a071cee7b196c955985eb003'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74DirectFourBlock']==['Init','Init','Mathlib.Tactic.Ring']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74DirectFourBlock':s['object']}; assert len(allrec)==2034==a['union_count']
lib=Path(a['output_root'])/'lib'; assert lib.is_dir()
wanted=set()
for name,bundle in allrec.items():
 stem=lib/name.replace('.','/')
 for suffix,rec in bundle.items():
  f=Path(str(stem)+suffix)
  if rec is None: assert not os.path.lexists(f); continue
  wanted.add(str(f.relative_to(lib)));assert f.is_file() and str(f.resolve())==rec['resolved'] and sha(f)==rec['sha256']
actual={str(x.relative_to(lib)) for x in lib.rglob('*') if x.is_file() or x.is_symlink()};assert actual==wanted
for path,hashval in a['inputs'].items():assert sha(path)==hashval
for name,cl in a['closures'].items():
 if name=='Trace74DirectFourBlock':continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
r=a['selected_outside']['Mathlib.Tactic.Ring']['.olean'];assert r['sha256']=='cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4'
print('PASS: outer/child/stage/header receipts, exact source/report, 2034 selected union bundles, 81 outside, 15 retained closure sets and bundles')

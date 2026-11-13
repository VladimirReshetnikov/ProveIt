#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-mask-abstract-cover-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-conditional-saturation-guard-rebuild/observations/attempt02/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='afc1610f51385166532983d2d5179872a8fc026049eb82a2455caa36b4e47a30'
assert sha(OO/'terminal.json')=='b769e3ebcfea926a1cd91e09a22d91c922070a5ee535c52b9cb49fe6eea83251'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='a55113d40aeae95bc420b51d1a1a2809a3ed4bb28968af45b22b4152e6501709'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='f63cf891352e8756c9f3feae574253eb810f794c14f07c35ec1e26454549cd03'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='6804ba7740804bc046e32dd03d90c43bccebd9a0c05eeab8b81a38110a4105ba'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="'Trace74AbstractCover.of_identity' does not depend on any axioms\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='72d5c66a1959b6a5e52811a7a277296e6434cd4f1865e2199b6b89abcb45ac80'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74AbstractCover']==['Init','Init','Mathlib.Data.Nat.Basic']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74AbstractCover':s['object']}; assert len(allrec)==2036==a['union_count']
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
 if name=='Trace74AbstractCover':continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
assert a['selected_outside']['Mathlib.Data.Nat.Basic']['.olean']['sha256']=='b7313829708c3c06eafa1e8c1d6e8d537c322c675a0c7536c44d31963638c250'
print('PASS: outer/child/stage/header receipts, exact source/report, 2036 selected union bundles, 82 outside, 17 retained closure sets and bundles')

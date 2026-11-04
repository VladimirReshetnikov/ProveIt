#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-cover-bind-beta-warning-policy-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-symbolic-cover-fixed-geometry-v2-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='4aabf2bba3e729a9d3e92bb8f13e342ad8f7168abfdb725d0205323f7b51e462'
assert sha(OO/'terminal.json')=='69bf2d41c543bab901d3bc511a992c961af3fbade8aab07f95b923aeb3af205e'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='3e4f10df0f0318429ae9786463a7426f5edd76163e9e8849616d8dc250c21f2d'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='9668a65f671e443709a4f7b0375bc489a91a8d4c529f2dc957b775bf3d336782'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='dd14955b76fa843fa70623cc275bdf3fd0b503e139e66d48acac9f17ae43fe82'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()==str(Path(a['output_root'])/'src/Trace74CoverBindBeta.lean')+":18:4: warning: exponent 8807 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold\n'Trace74CoverBindBeta.cover' depends on axioms: [propext]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='d3770ef007c07da40a0d960cf079981700f1af511b0c40341d821fffc5e57467'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74CoverBindBeta']==['Init','Init','Trace74FixedGeometryCover','Trace74BetaPower']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74CoverBindBeta':s['object']}; assert len(allrec)==2040==a['union_count']
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
 if name in ('Trace74CoverBindBeta','Trace74BetaPower'):continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
support=json.loads((D/'research/trace74-symbolic-mask-beta-power-v2-rebuild/observations/attempt01/result.json').read_text())
assert a['closures']['Trace74BetaPower']==support['closures']['Trace74BetaPower']
for kind,key in [('project','selected_project'),('outside','selected_outside')]:
 for dep in support['closures']['Trace74BetaPower'][kind]:
  assert {k:None if v is None else v['sha256'] for k,v in a[key][dep].items()} == {k:None if v is None else v['sha256'] for k,v in support[key][dep].items()}
print('PASS: outer/child/stage/header receipts, exact source/report, 2040 selected union bundles, 82 outside, 20 retained closure sets and bundles')

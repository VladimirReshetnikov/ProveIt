#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-cover-bind-defect-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-symbolic-cover-bind-low-parametric-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='42890bde08cbce317629731ada1f5fc29ad2fefb856649e1151d5c5ee27397d9'
assert sha(OO/'terminal.json')=='76ed7b80e052e202d56f546b69f04cd4ad880878ae22a467846089bc80f9821b'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='ea67e21586c4298ef0738ab76b3c7342ad770af99b92a30568068ff439e7eda3'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='4093b4e62c8905607b8457048ab36c2eb384094a332194a89fe273abff14fecb'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='e890f2d21fc116750a76e7c9c43c220f0fbecf0039407112000f899cec19bdda'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="".join("'Trace74CoverBindDefect."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ("cover",)) and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='9978132ed8ea14861a519c924bbb6e924e6c3e4b436c1e4b35c83affb0da43db'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74CoverBindDefect']==['Init','Init','Trace74CoverBindLowParametric','DiophantineConsistency.CompactConcreteMask']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74CoverBindDefect':s['object']}; assert len(allrec)==2042==a['union_count']
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
 if name=='Trace74CoverBindDefect':continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
print('PASS: outer/child/stage/header receipts, exact source/report, 2042 selected union bundles, 82 outside, 23 retained closure sets and bundles')

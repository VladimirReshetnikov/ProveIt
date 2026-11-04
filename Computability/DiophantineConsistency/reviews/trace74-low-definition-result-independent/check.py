#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-mask-low-definition-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-conditional-saturation-guard-rebuild/observations/attempt02/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='7399ca5b440dc883c08c0738aba4b7c681af9bb648322930e646da4f0f6d2bde'
assert sha(OO/'terminal.json')=='eb9cb9d84d870447abbefc9032b1e457e3d9bbe485f277bc8b72b22458643b15'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='a55113d40aeae95bc420b51d1a1a2809a3ed4bb28968af45b22b4152e6501709'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='58be8dd6f4c5f287854054fca56b02fe33b6339797d8f2bfbd7762d0fbbc7ba4'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='e05dec25774e6f1806b2c85d5f036180a2b20367f2554f7ef35d17f58151d5fe'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="".join("'Trace74LowNatDefinition."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ("low_nat_definition",)) and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='ea2cc1c7962d8e1190c8944df85207c9d56a5d6c3e9dca872e1f7ae75166064b'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74LowNatDefinition']==['Init','Init','DiophantineConsistency.CompactSymbolicPorts']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74LowNatDefinition':s['object']}; assert len(allrec)==2036==a['union_count']
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
 if name=='Trace74LowNatDefinition':continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
assert a['selected_project']['DiophantineConsistency.CompactSymbolicPorts']['.olean']['sha256']=='69927a2a645ea7c4ba99f7413357bfbbd7a344b2e0a026f08392e67870c8bff5'
print('PASS: outer/child/stage/header receipts, exact source/report, 2036 selected union bundles, 81 outside, 17 retained closure sets and bundles')

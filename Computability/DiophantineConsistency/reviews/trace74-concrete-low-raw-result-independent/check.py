#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-mask-concrete-low-raw-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-symbolic-mask-radix-indices-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='38616f5b0dbbbd20aaaa6a98d5cda55a02c8282082429bf32dd280ce8b8c4ce6'
assert sha(OO/'terminal.json')=='07b9d3eee6169cd3e0c0dc74fce616860c6cbffd6a2fe5a0322ffca56ea5565c'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='da19b3a409b5bcf144e979d1ac2ecd3e7988aae934b49d9472484cb8260c27bf'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='e147cfe2ae6fd42aa4e36827bf71435aa91714f8d5a8991b201eba4902127037'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='add4b00118fa4083d5e7e79e2db5947a8d5bfc62b091c8f85e32d70abde71a77'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="".join("'Trace74ConcreteLowRaw."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ("low_add_defect",)) and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='f08fc4f2893b673d894348f7565abcc68dc4122f783ab804402d8d75b6b3d831'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74ConcreteLowRaw']==['Init','Init','Trace74RadixIndices','Trace74SupportShort']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74ConcreteLowRaw':s['object']}; assert len(allrec)==2040==a['union_count']
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
 if name in ('Trace74ConcreteLowRaw','Trace74SupportShort'):continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
assert a['selected_project']['Trace74GenericDefect']['.olean']['sha256']=='0aa1257ae2e0885a8e8c4cd1fa78f8442b23510de9c0106533e88bc25e639d90'
support=json.loads((D/'research/trace74-symbolic-mask-support-short-rebuild/observations/attempt01/result.json').read_text())
assert a['closures']['Trace74SupportShort']==support['closures']['Trace74SupportShort']
for kind,key in [('project','selected_project'),('outside','selected_outside')]:
 for dep in support['closures']['Trace74SupportShort'][kind]:
  assert {k:None if v is None else v['sha256'] for k,v in a[key][dep].items()} == {k:None if v is None else v['sha256'] for k,v in support[key][dep].items()}
print('PASS: outer/child/stage/header receipts, exact source/report, 2040 selected union bundles, 81 outside, 20 retained closure sets and bundles')

#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-symbolic-mask-fixed-radix-rebuild/observations/attempt01'; OO=O.parent/'outer-attempt01'; P=D/'research/trace74-symbolic-mask-generic-defect-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='cad5eb2a633c763c79e7e2197caed91cc5aacd3e1bde8f9af738ad7f924011e8'
assert sha(OO/'terminal.json')=='42f36fac9ed372fe19e717d4a643d3571977eac0c58b4c87a56329073ce8a115'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='3aa11826e07b5d67901577917433f147ce426a737c828743c403b4f9edd6ad07'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='a2999f5dc0e86c460bfae89162c1be33daead75c2aaf36284f3dad372c7b1c5d'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='079d6a935908d678212dca47d418aee5ad94ff3ab2c6b164f90f89e2e8778d71'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="".join("'Trace74FixedRadix."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ("low_add_defect",)) and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='2232e9d8877bd3b6b854378884d7b5d4df5e62df27d064c1d352f077a931669d'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74FixedRadix']==['Init','Init','Trace74GenericDefect']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74FixedRadix':s['object']}; assert len(allrec)==2037==a['union_count']
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
 if name=='Trace74FixedRadix':continue
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
print('PASS: outer/child/stage/header receipts, exact source/report, 2037 selected union bundles, 81 outside, 18 retained closure sets and bundles')

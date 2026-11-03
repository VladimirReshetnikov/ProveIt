#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2]; O=D/'research/trace74-conditional-saturation-guard-rebuild/observations/attempt02'; OO=O.parent/'outer-attempt02'; P=D/'research/trace74-direct-four-block-rebuild/observations/attempt01/result.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'result.json')=='a55113d40aeae95bc420b51d1a1a2809a3ed4bb28968af45b22b4152e6501709'
assert sha(OO/'terminal.json')=='b8108201952a11db44245fec9d671ddbbf6897a78726ba10aaf94254d541997a'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());p=json.loads(P.read_text())
assert sha(P)=='988dd618c628d3ee9e76391a4a95c871ccbb8ce83292ebe01ac27a7e8dd54f20'
assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='d1363bf8f100a5985ff3b59d446039ab86d3c884db9ec2094673a245c5a2125b'
for f,h in o['inputs_before'].items():assert sha(f)==h
assert sha(OO/'stdout')==o['stdout_sha256'] and sha(OO/'stderr')==o['stderr_sha256']
s=a['stages'][0]; assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='9920fb51ab7f6d45ff5b671ac98d39da38adf45b211c8f69910aa343deaffd9b'==sha(s['source'])==sha(O/'stage-01.source.lean')
assert sha(O/'stage-01.stdout')==s['stdout_sha256'] and sha(O/'stage-01.stderr')==s['stderr_sha256']
assert (O/'stage-01.stdout').read_text()=="'Trace74ConditionalSaturationGuard.guard_of_block_and_population' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='bef6328b824d01237e750a8447dab1ed157ef5f1ab6958b27ac4b65c518f7e63'
assert len(a['headers'])==1
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 assert sha(O/f'header-{i:03}.stdout')==v['stdout_sha256'] and sha(O/f'header-{i:03}.stderr')==v['stderr_sha256']
assert a['serialized_headers']['Trace74ConditionalSaturationGuard']==['Init','Init','DiophantineConsistency.ArithmeticSaturation','DiophantineConsistency.ArithmeticRankForcing']
assert sha(O/'initial-union.json')==a['initial_union_sha256']; initial=json.loads((O/'initial-union.json').read_text()); allrec={**initial,'Trace74ConditionalSaturationGuard':s['object']}; assert len(allrec)==2035==a['union_count']
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
 if name=='Trace74ConditionalSaturationGuard':continue
 assert cl==p['closures'][name]
 for kind,key in [('project','selected_project'),('outside','selected_outside')]:
  for dep in cl[kind]:
   before=p[key][dep]; after=a[key][dep]
   assert {s:None if v is None else v['sha256'] for s,v in before.items()}=={s:None if v is None else v['sha256'] for s,v in after.items()}
for name,bundle in a['selected_outside'].items():
 r=bundle['.olean']; f=Path(r['path']);assert f.is_file() and str(f.resolve())==r['resolved'] and sha(f)==r['sha256']
 for suffix,rec in bundle.items():
  if rec is not None: assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
assert a['selected_project']['DiophantineConsistency.ArithmeticSaturation']['.olean']['sha256']=='7270ac9e040b9be18433f25b2956f6f9c53d17d3832b40e1a43ac36467fc017e'
assert a['selected_project']['DiophantineConsistency.ArithmeticRankForcing']['.olean']['sha256']=='13724d5518f0d59a72d8874747804c1bed263f3d5e9a181e6023f4e3738e6b83'
print('PASS: outer/child/stage/header receipts, exact source/report, 2035 selected union bundles, 81 outside, 16 retained closure sets and bundles')

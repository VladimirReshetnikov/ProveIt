from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-guardfree-rank-upper-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='33b34e3f1f2eacf1eaad393cfc98644ee4d82cb0775113e1cb668040e6285e8b'
assert sha(OO/'terminal.json')=='8b1029208113aa53fa88da7e96d6f96d218d24e51f59b445d4cd2837e6ca1be6'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='813d615c6e1236b4c926fb440605701f8b49b60472ddc8dc4dfcd2fda0d1ad65'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
s=a['stages'][0];assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='7375f1b6a417aa4605b212fb4802fa84db74fe2418f25505e5d4067669fb243f'==sha(s['source'])==sha(O/'stage-01.source.lean')
for f in ['stdout','stderr']:assert sha(O/('stage-01.'+f))==s[f+'_sha256']
names=['slack_identity','signed_upper','graph_rank_upper']; expected="'Trace74GuardFreeRankUpper.slack_identity' depends on axioms: [propext, Quot.sound]\n"+''.join("'Trace74GuardFreeRankUpper."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names[1:])
assert (O/'stage-01.stdout').read_text()==expected and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='b2df40152e0bd1cb7fcd2ccee358646ad0f4db4ebd7125fca09205a70a4bd07d'
assert a['serialized_headers']['Trace74GuardFreeRankUpper']==['Init','Init','Trace74RankBinding']
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records={**initial,'Trace74GuardFreeRankUpper':s['object']};assert len(records)==a['union_count']==2068
lib=Path(a['output_root'])/'lib';wanted=set()
for name,b in records.items():
 for suff,rec in b.items():
  p=Path(str(lib/name.replace('.','/'))+suff)
  if rec is None:assert not os.path.lexists(p);continue
  wanted.add(str(p.relative_to(lib)));assert p.is_file() and str(p.resolve())==rec['resolved'] and sha(p)==rec['sha256']
assert wanted=={str(p.relative_to(lib)) for p in lib.rglob('*') if p.is_file() or p.is_symlink()}
for p,h in a['inputs'].items():assert sha(p)==h
for b in a['selected_outside'].values():
 for rec in b.values():
  if rec is not None:assert Path(rec['path']).is_file() and str(Path(rec['path']).resolve())==rec['resolved'] and sha(rec['path'])==rec['sha256']
parent=D/'research/trace74-repunit-population-saturation-rebuild/observations/attempt01/result.json'
assert sha(parent)=='7796dfd7f24d7739f2d455454d9ab90792c513c9e87689576ee211a1721d06dc'
producer={}
checks=[(json.loads(parent.read_text()),None)]
for n,path in producer.items():
 p=D/'research'/path/'observations/attempt01/result.json';assert str(p) in a['inputs'] and sha(p)==a['inputs'][str(p)];checks.append((json.loads(p.read_text()),n))
for old,only in checks:
 for root in ([only] if only else old['closures']):
  c=old['closures'][root];assert a['closures'][root]==c
  for kind,key in [('project','selected_project'),('outside','selected_outside')]:
   for n in c[kind]:
    assert hashes(a[key][n])==hashes(old[key][n])
    if kind=='project' and only:assert a['serialized_headers'][n]==old['serialized_headers'][n]
print('PASS: result/log/object, 2068 union bundles, outside selections and all parent closures')

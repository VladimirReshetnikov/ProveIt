from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-generic-repunit-population-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='93b806e863c5dc06e92f5c154c89fbb5129624404108ad102f261e8f21ff55e5'
assert sha(OO/'terminal.json')=='029d6abb32c1cace35d92e82892bf3fa2c9897ced794430ef4dc13c902919bcf'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='04d695e02f608a3c744da057aee2de405680dd2cda7ab7f580a3a9516bd14b88'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
s=a['stages'][0];assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='2e310e5d739520dd75432c5de6d84921a38f26f654f489299474af3a79aabd5c'==sha(s['source'])==sha(O/'stage-01.source.lean')
for f in ['stdout','stderr']:assert sha(O/('stage-01.'+f))==s[f+'_sha256']
assert (O/'stage-01.stdout').read_text()=="'Trace74GenericRepunitPopulation.radix_and_mask_population' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='b09a8fe9ba4e2688dec1be3651cd4d0f251fe32a88e23851fe65c95c1bf536c8'
assert a['serialized_headers']['Trace74GenericRepunitPopulation']==['Init','Init','DiophantineConsistency.ArithmeticMaskPopulation']
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records={**initial,'Trace74GenericRepunitPopulation':s['object']};assert len(records)==a['union_count']==2058
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
parent=D/'research/trace74-fixed-mask-saturation-conditional-rebuild/observations/attempt01/result.json'
assert sha(parent)=='e0c4394107493b89ebde645c4da0724f9a7e380430026f0c76ad1a7b0fddd09c'
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
print('PASS: result/log/object, 2058 union bundles, outside selections and all parent closures')

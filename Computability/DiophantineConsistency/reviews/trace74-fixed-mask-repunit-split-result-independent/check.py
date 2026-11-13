from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-fixed-mask-repunit-split-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='4658f7f4ce12299fcb9af6cf76db5af37977f1e817297804e7bd255b76269b1d'
assert sha(OO/'terminal.json')=='99b300fa09136de3972eaeb69050375ad2290ec8dc5fc409566a4c5c046cd294'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='1c9047de292d143118067670ba37ae3ae12b7140db283549579b3f74cf4a1fc8'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
s=a['stages'][0];assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='8c69cb21194cab9a0dafc49ea998e928bb3d4d9a4283da808e20b411d8082958'==sha(s['source'])==sha(O/'stage-01.source.lean')
for f in ['stdout','stderr']:assert sha(O/('stage-01.'+f))==s[f+'_sha256']
names=['radix_and_mask_population']; expected=''.join("'Trace74FixedMaskRepunitSplit."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in names)
assert (O/'stage-01.stdout').read_text()==expected and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='cbaa957bcef3b3fc0dde10fea555542053463b8f66197b92997f9398aa408a41'
assert a['serialized_headers']['Trace74FixedMaskRepunitSplit']==['Init','Init','Trace74GenericRepunitPopulation','Trace74MaskPopulationData','DiophantineConsistency.CompactFixedBeta','DiophantineConsistency.CompactLowEven','DiophantineConsistency.CompactHighResidue']
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records={**initial,'Trace74FixedMaskRepunitSplit':s['object']};assert len(records)==a['union_count']==2060
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
parent=D/'research/trace74-fixed-mask-population-data-rebuild/observations/attempt01/result.json'
assert sha(parent)=='3f1217a72ad96a537341d903763b204f7a7d3d176495c97122ca64d1b3fe7d51'
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
print('PASS: result/log/object, 2060 union bundles, outside selections and all parent closures')

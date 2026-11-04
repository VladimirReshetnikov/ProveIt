from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-fixed-mask-saturation-conditional-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='e0c4394107493b89ebde645c4da0724f9a7e380430026f0c76ad1a7b0fddd09c'
assert sha(OO/'terminal.json')=='bff5e72604e647c7993958e2b663c682a260e8997763e25d4bf5fd572ca92def'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='e006a5e624d23355a6986b7a64a0aa675961afb5dec220f9093ae8dd91b8cb0b'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
stages=[('Trace74MaskCoverGuard','66991596012af7ec03a3ac082865fe4bbd367205e36ec45d89070f2977d258d2','796cc640c35507ac712804ac98ac15a38f607f2d94a7f82261a51b19631f077f',['Trace74MaskCoverGuard.compare_from_cover','Trace74MaskCoverGuard.compare_from_mask_bounds'],['Init','Init','DiophantineConsistency.ArithmeticRankForcing']),('Trace74SaturationMaskGuard','5013eb4fb60c7c4af4baedb9f65e605a9bcec8961ff1603544704b7b6235dc72','ee3884c9d4ab0bcd67a554c03ae7faf7f054e8e73a3494326c86eba688ece688',['Trace74SaturationMaskGuard.guard_from_saturation_and_cover'],['Init','Init','Trace74MaskCoverGuard','DiophantineConsistency.ArithmeticSaturation']),('Trace74FixedMaskSaturationGuard','d8861a81910d30cb8f5d5c36dbef98773bac092e50a2331b4a0862bf266cb48f','aa922719f1bd884df30458da4a608b789e0aa46f5e4b7f73dd0029cdef98f6c4',['Trace74FixedMaskSaturationGuard.guard'],['Init','Init','Trace74SymbolicCoverModel','Trace74SaturationMaskGuard'])]
assert len(a['stages'])==len(stages)
for i,(name,src,obj,reports,header) in enumerate(stages,1):
 s=a['stages'][i-1];assert s['module']==name and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
 assert s['source_sha256']==src==sha(s['source'])==sha(O/f'stage-{i:02}.source.lean')
 for f in ['stdout','stderr']:assert sha(O/f'stage-{i:02}.{f}')==s[f+'_sha256']
 assert (O/f'stage-{i:02}.stdout').read_text()==''.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in reports) and not (O/f'stage-{i:02}.stderr').read_bytes()
 assert s['object']['.olean']['sha256']==obj and a['serialized_headers'][name]==header
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records=dict(initial);records.update({s['module']:s['object'] for s in a['stages']});assert len(records)==a['union_count']==2057
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
parent=D/'research/trace74-symbolic-cover-model-cast-rebuild/observations/attempt01/result.json'
assert sha(parent)=='80aac76470d187d1eb71b40807bbcd56b4e3a50e727815d3c69bb85cb92d1c63'
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
print('PASS: result/log/object, 2057 union bundles, outside selections and all parent closures')

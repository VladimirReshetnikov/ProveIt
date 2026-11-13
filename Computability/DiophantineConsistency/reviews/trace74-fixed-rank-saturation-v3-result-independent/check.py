from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-fixed-mask-rank-saturation-v3-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='7e729fb067a2a17a35bd509bc8968652cd89f6f1d908d79fb8101cfa2540d836'
assert sha(OO/'terminal.json')=='cce217672642f1248844bd50ce60c16097fd16414f85fb9dc218019769c1c0bf'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='2cdb8853f2245959e2336c5c7fc907bcfe2b8bab758490b1a8af4fbe7b49b022'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
stages=[('Trace74NaturalRankWindow','41ed8bb4e577c4d1acd15214de7ad3683d0d48233ac2bfef2ca2555118c9cec0','0deddd45225a1522fddef89f1505a164c6e88b82dadecd427cebb46fc55b6ca4',[('Trace74NaturalRankWindow.scalar_window','propext, Classical.choice, Quot.sound')],['Init','Init','DiophantineConsistency.ArithmeticAdaptiveRankWindow2011']),('Trace74RankBinding','130ffe9918763946c023d383ed06826416fe49ad64249bb5c63edbf36a809ec8','a6bee53b66c09cd224bb3d89d2c8341ae93158502dc98197fc81958259b4f57c',[('Trace74RankBinding.ring_rank_shape','propext, Quot.sound'),('Trace74RankBinding.graph_rank_eval','propext, Classical.choice, Quot.sound')],['Init','Init','Trace74NaturalRankWindow','Trace74Mask','Trace75Factors']),('Trace74NaturalBlock','49d908e5b290c76613da30d72523670243c66731b474c03634bab30d6b0013f7','63cac4c4534d9c5fb79a5e261f8d236c76be9dbc874c3a06631ba0da62682352',[('Trace74NaturalBlock.natural_block','propext, Classical.choice, Quot.sound')],['Init','Init','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticSaturation','Trace74DirectFourBlock']),('Trace74FixedRankSaturation','b0a41cda3e3a9da74163f344df9ea4ab0a107d146c8f96c77513654d1a39136c','4d27de35edfda2c79a53142cc2c5b32e9c451f486ce26f0e82412c76c2372109',[('Trace74FixedRankSaturation.fixed_rank_saturation','propext, Classical.choice, Quot.sound')],['Init','Init','Trace74RankBinding','Trace74NaturalBlock','Trace74FixedMaskSaturationGuard'])]
assert len(a['stages'])==len(stages)
for i,(name,src,obj,reports,header) in enumerate(stages,1):
 s=a['stages'][i-1];assert s['module']==name and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
 assert s['source_sha256']==src==sha(s['source'])==sha(O/f'stage-{i:02}.source.lean')
 for f in ['stdout','stderr']:assert sha(O/f'stage-{i:02}.{f}')==s[f+'_sha256']
 assert (O/f'stage-{i:02}.stdout').read_text()==''.join("'"+n+"' depends on axioms: ["+axioms+"]\n" for n,axioms in reports) and not (O/f'stage-{i:02}.stderr').read_bytes()
 assert s['object']['.olean']['sha256']==obj and a['serialized_headers'][name]==header
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records=dict(initial);records.update({s['module']:s['object'] for s in a['stages']});assert len(records)==a['union_count']==2061
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
print('PASS: result/log/object, 2061 union bundles, outside selections and all parent closures')

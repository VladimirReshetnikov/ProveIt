from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-symbolic-cover-discharge-low-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='032ec89fd0b8bd7ac6246dedfec435cb9d5c0506ea50197110317be1e2d04711'
assert sha(OO/'terminal.json')=='9fcdbc5e9c792bc2f6e236c50cdd7a9f4a20233cdde2a273caa8c18213f1c40b'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='9ccec3088302ac26c111a17c200e0d33b202874c9e35c8d656f0517072368949'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
s=a['stages'][0];assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='76ba522eeb1a37b8deacad68d3a9719c7b5587110ae0e47ae47368d7010bb185'==sha(s['source'])==sha(O/'stage-01.source.lean')
for f in ['stdout','stderr']:assert sha(O/('stage-01.'+f))==s[f+'_sha256']
assert (O/'stage-01.stdout').read_text()=="'Trace74CoverDischargeLow.cover' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='1c12cccf25551e3d6bb700ebe505787fb9f2fedf264cf154c230a79c15efdf1a'
assert a['serialized_headers']['Trace74CoverDischargeLow']==['Init','Init','Trace74CoverBindDefect','Trace74LowPortIdentity']
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records={**initial,'Trace74CoverDischargeLow':s['object']};assert len(records)==a['union_count']==2049
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
parent=D/'research/trace74-symbolic-mask-low-port-identity-rebuild/observations/attempt01/result.json'
assert sha(parent)=='80daf9e5e612371230f730b928b1193bd7043bf28c4aa693f328014ccd49abaf'
producer={
'Trace74CoverBindDefect':'trace74-symbolic-cover-bind-defect-rebuild',
'Trace74CoverBindLowParametric':'trace74-symbolic-cover-bind-low-parametric-rebuild',
'Trace74CoverBindBeta':'trace74-symbolic-cover-bind-beta-warning-policy-rebuild',
'Trace74FixedGeometryCover':'trace74-symbolic-cover-fixed-geometry-v2-rebuild',
'Trace74GenericPowerCover':'trace74-symbolic-cover-generic-join-rebuild',
'Trace74AbstractCover':'trace74-symbolic-mask-abstract-cover-rebuild',
'Trace74BetaPower':'trace74-symbolic-mask-beta-power-v2-rebuild'}
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
print('PASS: result/log/object, 2049 union bundles, outside selections, all parent and seven producer closures')

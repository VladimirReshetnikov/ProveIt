from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-symbolic-cover-bind-high-warning-policy-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='1adc8523e61b59941d6a1688b947b63e05c97ba75aca094f4fd0854e59a9e8dd'
assert sha(OO/'terminal.json')=='7cc307f34635cfe40636518f3e0da902fae99aaf1e60c39a89957d9df3c0ddaf'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='c8a73c9acf8f02471b7351409a7e649942aa2438fd215b72c6e371be4fd761b5'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
s=a['stages'][0];assert len(a['stages'])==1 and s['status']=='PASS' and s['exit']==0 and s['reason'] is None
assert s['source_sha256']=='d7511af2da5b84d6222ff95fac72e1ccda6b7e6412d346084474c9b868cc12fd'==sha(s['source'])==sha(O/'stage-01.source.lean')
for f in ['stdout','stderr']:assert sha(O/('stage-01.'+f))==s[f+'_sha256']
assert (O/'stage-01.stdout').read_text()==s['command'][-3]+":14:50: warning: exponent 4393 exceeds the threshold 256, exponentiation operation was not evaluated, use `set_option exponentiation.threshold <num>` to set a new threshold\n"+"'Trace74CoverBindHigh.cover_nat' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stage-01.stderr').read_bytes()
assert s['object']['.olean']['sha256']=='7a1c5a48b47287109f6ec343c88cb7c72acf25e09a8a458e66f8932779757527'
assert a['serialized_headers']['Trace74CoverBindHigh']==['Init','Init','Trace74CoverDischargeDefect','Trace74HighDigitBound']
for i,v in enumerate(a['headers']):
 assert v['status']=='PASS' and v['exit']==0 and v['reason'] is None
 for f in ['stdout','stderr']:assert sha(O/f'header-{i:03}.{f}')==v[f+'_sha256']
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records={**initial,'Trace74CoverBindHigh':s['object']};assert len(records)==a['union_count']==2053
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
parent=D/'research/trace74-symbolic-cover-discharge-defect-rebuild/observations/attempt01/result.json'
assert sha(parent)=='c9e6d05e8c023dec54d226b225460284ac4abe79951aaba1330574642dd19b64'
producer={'Trace74HighDigitBound':'trace74-symbolic-mask-high-digit-bound-v5-rebuild'}
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
print('PASS: result/log/object, 2053 union bundles, outside selections, all parent and independent high producer closures')

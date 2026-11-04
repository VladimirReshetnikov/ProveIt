from pathlib import Path
import hashlib,json,os
D=Path(__file__).resolve().parents[2];O=D/'research/trace74-n3-scalar-discrete-v2-rebuild/observations/attempt01';OO=O.parent/'outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashes(d):return {k:None if v is None else v['sha256'] for k,v in d.items()}
assert sha(O/'result.json')=='c56f50101472e542385769a4b8c69715483d3a00c9aa5f439d29be6accceb637'
assert sha(OO/'terminal.json')=='92e15a214c3d33140141c2f30c7b0f0b5f695d5274b44bd313551909f9f9aa70'
a=json.loads((O/'result.json').read_text());o=json.loads((OO/'terminal.json').read_text());assert a['status']=='PASS' and o['exit']==0 and o['child_status']=='PASS' and o['child_result_sha256']==sha(O/'result.json')
assert o['inputs_before']==o['inputs_after'] and o['wrapper_sha256_before']==o['wrapper_sha256_after']=='003ecef59ad4ef6c99019092a45c0e038cba9f0e3a40f125d53699fa51d56148'
for p,h in o['inputs_before'].items():assert sha(p)==h
for f in ['stdout','stderr']:assert sha(OO/f)==o[f+'_sha256']
stages=[('Trace74N3UpperCertificate', 'e38ba8c43123de3915c3dbdfdb8045a3833bbc2e70d8243b09e7a333886a5cb0', '6cb78bc5565c8eafe6a909091972804e949eee95ab40c26c55e344b836ff40ab', [('Trace74N3UpperCertificate.shifted_upper_certificate', 'propext, Classical.choice, Quot.sound')], ['Init', 'Init', 'Mathlib.Algebra.Order.Ring.Basic', 'Mathlib.Tactic.Ring', 'Mathlib.Tactic.Positivity']), ('Trace74N3UpperBound', '926746d00bdb89aaa1c6797766ec875f41821d9ffdffddbb9c2b5b049fb63b72', 'bd42e9a3ea027efae121a2fa77c5d18603210cfb36a94c5fdc33f8bcdbb84361', [('Trace74N3UpperBound.upper_of_polynomials', 'propext, Classical.choice, Quot.sound')], ['Init', 'Init', 'Trace74N3UpperCertificate', 'Mathlib.Tactic.Linarith']), ('Trace74N3ScalarDiscrete', 'e7771fdb1dd529fcc0d07ad6d1877f41a0581b124171f330fc9f0f453f793670', '1cbc0a63ccf24cc5b36f97f970abb3a7b96f26a1cc64b26179e96c8ef655e93a', [('Trace74N3ScalarDiscrete.interval', 'propext, Classical.choice, Quot.sound'), ('Trace74N3ScalarDiscrete.no_scalar_solution', 'propext, Classical.choice, Quot.sound')], ['Init', 'Init', 'Trace74FirstThreeLower', 'Trace74N3UpperBound'])]
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
assert sha(O/'initial-union.json')==a['initial_union_sha256'];initial=json.loads((O/'initial-union.json').read_text());records=dict(initial);records.update({s['module']:s['object'] for s in a['stages']});assert len(records)==a['union_count']==2072
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
parent=D/'research/trace74-first-three-lower-ordered-rebuild/observations/attempt01/result.json'
assert sha(parent)=='d165ec74913ebce9a5d4e1ba5ba0eded960eae07079bb98430b5006ab937a01e'
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
print('PASS: result/log/object, 2072 union bundles, outside selections and all parent closures')

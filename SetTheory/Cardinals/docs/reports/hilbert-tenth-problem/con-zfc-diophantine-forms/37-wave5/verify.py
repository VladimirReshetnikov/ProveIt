#!/usr/bin/env python3
"""Sealed, offline replay. Finite evidence, not a formal consistency proof."""
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent
STAGES=['coefficients/rebuild.py','positive/build_positive.py','positive/check_positive.py','nine/build_nine.py','nine/verify_nine.py','signed/build_signed.py','signed/check_signed.py','lowdegree/build.py','lowdegree/check.py','root/check_completed_square_bounds.py','root/check_pell_orbits.py','root/check_nine_telescoping.py','review/check_literal_structure.py']
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def hashes(root):return {p.relative_to(root).as_posix():digest(p) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix not in ['.pyc','.log','.aux','.out'] and p.name not in ['VERIFICATION.json','NEGATIVE_CONTROLS.json']}
def validate(root):
 seal=json.loads((root/'SHA256SUMS.json').read_text())
 for rel,expected in seal.items():
  f=root/rel
  assert f.is_file(), 'Missing sealed dependency: '+rel
  assert digest(f)==expected,'Sealed content differs: '+rel
 instance=json.loads((root/'INSTANCE.json').read_text())
 for name,row in instance['ports'].items():
  raw=(root/'coefficients/coefficients_compact'/f'{name}.bin').read_bytes()
  assert hashlib.sha256(raw).hexdigest()==row['sha256'],'Coefficient mismatch: '+name
  assert len(raw)==row['bytes'] and int.from_bytes(raw,'little').bit_length()==row['bit_length']
 assert instance['coefficient_variant']=='wang943-compact-5pow10'
 assert instance['Jones_nu']==31 and instance['index_exponent']==45933757
 packets=list((root/'signed/generated').glob('signed*.json'))+list((root/'nine/generated').glob('nine_*.json'))
 packets+=list((root/'positive').glob('*_product.json'))+list((root/'positive').glob('*_system.json'))+list((root/'positive').glob('*_sos.json'))
 packets+=list((root/'lowdegree').glob('integer*.json'))
 for f in packets:
  packet=json.loads(f.read_text());binding=packet.get('coefficient_binding')
  assert isinstance(binding,dict),'Missing explicit binding: '+str(f.relative_to(root))
  if 'coefficient_files' in binding:
   for name,row in binding['coefficient_files'].items():
    assert row['sha256']==instance['ports'][name]['sha256'],'Wrong tuple in '+f.name
    assert (f.parent/row['path']).is_file(),'Missing bound payload in '+f.name
  else:
   manifest=binding['manifest']
   target=root/manifest if binding.get('path_base')=='package_root' else f.parent/manifest
   assert target.resolve() in [(root/'INSTANCE.json').resolve(),(root/'coefficients/COMPACT_COEFFICIENT_BINDING.json').resolve()],'Wrong selected binding '+f.name
   assert target.is_file()
 return len(seal)
def main():
 if not __debug__:raise SystemExit('Do not disable assertions.')
 sealed=validate(P);before=hashes(P);rewritten=set();results=[]
 with TemporaryDirectory(prefix='conzfc-wave5-') as tmp:
  Q=Path(tmp)/'package';shutil.copytree(P,Q,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.log','*.aux','*.out'))
  for stage in STAGES:
   stamps={p.relative_to(Q).as_posix():p.stat().st_mtime_ns for p in Q.rglob('*') if p.is_file()}
   result=subprocess.run([sys.executable,str(Q/stage)],cwd=Q,capture_output=True,text=True)
   if result.returncode:
    print(result.stdout);print(result.stderr,file=sys.stderr);raise AssertionError('Failed replay: '+stage)
   rebuilt=[]
   for f in Q.rglob('*'):
    if not f.is_file() or '__pycache__' in f.parts or f.suffix in ['.pyc','.log','.aux','.out']:continue
    rel=f.relative_to(Q).as_posix()
    if stamps.get(rel)!=f.stat().st_mtime_ns:
     if rel in ['VERIFICATION.json','NEGATIVE_CONTROLS.json']:continue
     assert rel in before,'Unpackaged generated artifact: '+rel
     assert digest(f)==before[rel],'Rebuild not byte-identical: '+rel
     rebuilt.append(rel);rewritten.add(rel)
   results.append({'stage':stage,'status':'PASS','byte_identical_outputs':sorted(rebuilt)})
   print('PASS',stage,flush=True)
  validate(Q)
 assert hashes(P)==before,'Replay modified the sealed original'
 receipt={'status':'PASS','sealed_files':sealed,'stage_count':len(results),'stages':results,'distinct_byte_identical_outputs':len(rewritten),'regenerated_files':sorted(rewritten),'scope':'Finite reconstruction and audits only; no new end-to-end kernel proof or solvability decision.'}
 (P/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items() if k not in ['stages','regenerated_files']},indent=2))
if __name__=='__main__':main()

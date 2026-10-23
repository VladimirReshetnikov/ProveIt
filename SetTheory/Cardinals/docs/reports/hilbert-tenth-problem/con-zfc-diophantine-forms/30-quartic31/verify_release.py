"""New-owned immutable verifier. All mutation happens in a temporary tree.
Dependencies: Python 3.10+ and NumPy. No received Python/Lean is executed.
"""
import sys
if not __debug__:raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
import os,json,hashlib,gzip,io,shutil,subprocess,tempfile,time,ast
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def require(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(root,rel):
 p=(root/rel).resolve();require(p.is_relative_to(root.resolve()),'Path escapes release: '+rel);return p
def integrity(root):
 require(not any(p.is_symlink() for p in root.rglob('*')),'Symlinks are not permitted in the immutable release')
 manifest=json.loads((root/'RELEASE_MANIFEST.json').read_text());expected={r['path'] for r in manifest['files']}
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and str(p.relative_to(root))!='RELEASE_MANIFEST.json'}
 require(expected==actual,'Manifest file set mismatch')
 for r in manifest['files']:
  p=safe(root,r['path']);require(p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'Manifest mismatch: '+r['path'])
 return len(expected)
def sources(root):
 count=0;maps=json.loads((root/'review/INERT_SOURCE_PATHS.json').read_text())
 led=json.loads((root/'review/SOURCE_LEDGER.json').read_text())
 for x in led['files']:
  path=maps.get(x['path'],x['path']);p=root/'review'/path
  if not p.exists():p=root/'review/primary'/Path(path).name
  raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==x['local_sha256'],'Source SHA256 mismatch: '+str(p));require(hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==x['sha'],'Git blob mismatch: '+str(p));count+=1
 for dirname,ledger,key in [('arithmetic','SOURCE_LEDGER.json','files'),('integers','SOURCE_MANIFEST.json','sources'),('compiler','PINNED_SOURCE_LEDGER.json','files')]:
  d=json.loads((root/dirname/ledger).read_text())
  for x in d[key]:
   rel=x.get('file',x.get('path'));p=(root/rel) if dirname=='compiler' else root/dirname/rel;raw=p.read_bytes();require(hashlib.sha256(raw).hexdigest()==x['sha256'],'Pinned source digest mismatch');blob=x.get('git_blob_sha1',x.get('git_blob_sha'));require(hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest()==blob,'Pinned source Git blob mismatch');count+=1
 return count
def payloads(root):
 d=json.loads((root/'compiler/COMPACT_COEFFICIENT_BINDING.json').read_text());total=0
 for x in d['files']:
  p=root/'compiler'/x['path'];raw=p.read_bytes();v=int.from_bytes(raw,'little');require(sha(p)==x['sha256'] and len(raw)==x['bytes'] and v.bit_length()==x['bit_length'],'Coefficient payload mismatch');total+=len(raw);packed=p.with_suffix(p.suffix+'.gz').read_bytes();require(len(packed)==x['gzip_bytes'] and hashlib.sha256(packed).hexdigest()==x['gzip_sha256'] and gzip.decompress(packed)==raw,'Compiler original gzip mismatch')
 require(total==5312269,'Wrong total compiler bytes')
 z=json.loads((root/'nine/Z_MATERIALIZATION.json').read_text());raw=(root/'nine/z_index.bin').read_bytes();require(hashlib.sha256(raw).hexdigest()==z['sha256'] and len(raw)==z['raw_bytes'],'z payload mismatch');require(int.from_bytes(raw,'little')==1<<45933757,'z is not exact stated power of two')
 packed=(root/'nine/z_index.bin.gz').read_bytes();require(len(packed)==z['gzip_bytes'] and hashlib.sha256(packed).hexdigest()==z['gzip_sha256'] and gzip.decompress(packed)==raw,'z original gzip mismatch')
 # All new lane bindings must resolve to exactly the same four central values.
 positive=json.loads((root/'positive/COEFFICIENT_BINDING.json').read_text())
 for name,x in positive['coefficient_files'].items():require(sha(root/'positive'/x['path'])==x['sha256'],'Positive binding mismatch')
 integer=json.loads((root/'integers/COEFFICIENT_BINDINGS.json').read_text())
 for name,x in integer['backends']['wang943_compact']['coefficients'].items():require(sha(root/'integers'/x['path'])==x['sha256'],'Integer binding mismatch')
 return total+len(raw)
def run():
 start=time.monotonic();files=integrity(ROOT);
 # Static dependency hygiene: no inherited workspace or previous-round filesystem path in executable modules.
 for py in ROOT.rglob('*.py'):
  if py.name=='verify_release.py':continue
  txt=py.read_text();require('/workspace/' not in txt and 'diophantine_zfc_round3/' not in txt,'Nonportable executable dependency: '+str(py))
 before={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()};pinned=sources(ROOT);raw=payloads(ROOT);completed=[]
 with tempfile.TemporaryDirectory(prefix='con-zfc-round4-') as name:
  temp=Path(name)/'release';shutil.copytree(ROOT,temp);env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None);env['PYTHONNOUSERSITE']='1'
  cmds=[['positive/build_positive.py'],['positive/check_positive.py'],['integers/build_odd_scale_family.py'],['integers/check_odd_scale_family.py'],['arithmetic/build_arithmetic.py'],['audit/pell_bound_checks.py'],['audit/pell_independent_checks.py'],['review/independent_review_audit.py'],['review/generic_jones_circuit.py'],['nine/rebuild_nu31.py','--compiler-root','compiler'],['nine/verify_compact_instance.py','nine/nu31','--compiler-root','compiler'],['audit_selected_nine.py']]
  # Record arithmetic skeletons before emitters. Portability-only metadata may differ.
  paths=list((temp/'positive').glob('positive12_*.json'))+list((temp/'integers').glob('integer*_degree*.json'))+[temp/'arithmetic'/f for f in ('quartic31.json','quartic31_system.json','quartic31_circuit.json')]
  snapshots={str(p.relative_to(temp)):json.loads(p.read_text()) for p in paths}
  for cmd in cmds:
   print('Checking '+cmd[0]+' ...',flush=True);t=time.monotonic();r=subprocess.run([sys.executable,'-B',*cmd],cwd=temp,env=env,text=True,capture_output=True)
   require(r.returncode==0,cmd[0]+' failed:\n'+r.stdout[-6000:]+'\n'+r.stderr[-6000:]);completed.append(dict(script=cmd[0],seconds=round(time.monotonic()-t,2)))
  for rel,old in snapshots.items():
   new=json.loads((temp/rel).read_text())
   for key in ('source','witnesses','fixed_numerals','variables','constants','equations','residuals','output','comparisons','outputs','ledger','exact_degree'):
    if key in old:require(new.get(key)==old[key],'Emitter changes frozen arithmetic: '+rel+' '+key)
 require(integrity(ROOT)==files,'Delivered tree changed during verification')
 after={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()};require(before==after,'Complete delivered tree including manifest changed during verification')
 print(json.dumps(dict(status='PASS',immutable_files=files,pinned_source_blobs=pinned,materialized_bytes=raw,delivered_tree_unchanged=True,checks=completed,seconds=round(time.monotonic()-start,2),scope='Finite arithmetic/provenance replay only; not a new end-to-end kernel proof.'),indent=2))
if __name__=='__main__':run()

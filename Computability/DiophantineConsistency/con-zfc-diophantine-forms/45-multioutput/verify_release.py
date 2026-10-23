#!/usr/bin/env python3
"""Read-only release audit; all mutating verifiers run in an isolated copy."""
import hashlib,json,pathlib,shutil,subprocess,sys,tempfile
if sys.flags.optimize:raise SystemExit('OPTIMIZATION FORBIDDEN: checks require assertions enabled')
R=pathlib.Path(__file__).resolve().parent
manifest=json.loads((R/'RELEASE_HASHES.json').read_text())
def safe(name):
 p=pathlib.PurePosixPath(name)
 if p.is_absolute() or '..' in p.parts or not p.parts or str(p)!=name or '\\' in name:raise SystemExit('UNSAFE MANIFEST PATH: '+name)
for p in R.rglob('*'):
 if p.is_symlink():raise SystemExit('SYMLINK FORBIDDEN: '+str(p))
actual={p.relative_to(R).as_posix() for p in R.rglob('*') if p.is_file()}
if actual!=set(manifest)|{'RELEASE_HASHES.json'}:raise SystemExit('FILE SET MISMATCH')
for name,digest in manifest.items():
 safe(name)
 p=R/name
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:raise SystemExit('HASH FAILURE: '+name)
pins=json.loads((R/'review/SOURCE_PINS.json').read_text())
for row in pins:
 raw=(R/'review/sources'/row['package']/row['path']).read_bytes()
 if hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()!=row['sha']:raise SystemExit('SOURCE PIN FAILURE: '+row['path'])
scripts=['quartic/verify_quadratic_targets.py','nine/verify_multitarget_nine.py','sun/verify_multitarget_sun.py','positive/check_bound_instance.py','positive/check_weight_identity.py','positive/check_weight_degrees.py','short/check_short_audit.py','short/check_positive_weight_review.py','audit/check_complete_equations.py','audit/check_degree_certificates.py','audit/check_fixed_bindings.py']
with tempfile.TemporaryDirectory(prefix='proveit-multioutput-') as td:
 target=pathlib.Path(td)/'release';shutil.copytree(R,target)
 for script in scripts:
  print('CHECK',script,flush=True)
  subprocess.run([sys.executable,str(target/script)],cwd=target,check=True)
print('PASS:',len(manifest),'release hashes;',len(pins),'source pins;',len(scripts),'authored isolated checks.')

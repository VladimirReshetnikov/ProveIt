"""Public, non-mutating release verifier. Python 3 standard library only.
All mutable computation happens in a disposable temporary copy. Never imports
or executes received upstream repository code. See verify_worktree.py for checks.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
if not __debug__ or sys.flags.optimize:
 raise SystemExit('ERROR: verification requires unoptimized Python; remove -O and PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def snapshot():
 return {str(p.relative_to(ROOT)):sha(p) for p in sorted(ROOT.rglob('*')) if p.is_file()}
def manifest_check():
 manifest=ROOT/'SHA256SUMS.txt'
 if not manifest.is_file():raise SystemExit('ERROR: SHA256SUMS.txt is required.')
 for line in manifest.read_text().splitlines():
  expected,name=line.split('  ',1);p=Path(name)
  if p.is_absolute() or '..' in p.parts:raise SystemExit('ERROR: invalid manifest path.')
  if not (ROOT/p).is_file() or sha(ROOT/p)!=expected:
   raise SystemExit('ERROR: release manifest mismatch: '+name)
manifest_check();before=snapshot()
print('PASS: immutable release manifest; running in a fresh temporary copy',flush=True)
try:
 with tempfile.TemporaryDirectory(prefix='diophantine-verification-') as temp:
  work=Path(temp)/'release';shutil.copytree(ROOT,work)
  child_env=os.environ.copy();child_env.pop('PYTHONOPTIMIZE',None)
  result=subprocess.run([sys.executable,'-B',str(work/'verify_worktree.py')],cwd=work,env=child_env)
  if result.returncode:raise SystemExit(result.returncode)
  receipt=json.loads((work/'VERIFICATION_RESULT.json').read_text())
  print('PASS:',len(receipt['circuits']),'circuits;',receipt['pinned_source_files'],'pinned files;',len(receipt['independent_checkers']),'independent checkers',flush=True)
finally:
 manifest_check()
 if snapshot()!=before:raise SystemExit('ERROR: original release tree changed during verification.')
 print('PASS: original release files remain byte-for-byte unchanged',flush=True)

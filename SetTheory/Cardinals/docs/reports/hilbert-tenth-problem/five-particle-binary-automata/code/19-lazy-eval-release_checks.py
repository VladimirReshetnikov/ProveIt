"""Exercise inventory, symlink, and documented output handling on a temporary copy."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent

def require(ok,detail):
    if not ok:raise RuntimeError(detail)

def main():
    checks=[]
    with tempfile.TemporaryDirectory(prefix='report19-release-check-') as td:
        root=Path(td)/'release'
        shutil.copytree(ROOT,root,ignore=shutil.ignore_patterns('.build','replay-output','__pycache__'))
        def run(script,*args):
            return subprocess.run([sys.executable,'-E','-s','-B',script,*args],cwd=root,capture_output=True,text=True)
        require(run('verify_release.py').returncode==0,'clean copy verification');checks.append('clean copy')
        (root/'unexpected.py').write_text('raise RuntimeError("must not execute")\n')
        result=run('verify_release.py');require(result.returncode!=0 and 'inventory mismatch' in result.stderr,'unexpected Python file rejection');checks.append('unexpected Python file rejected')
        (root/'unexpected.py').unlink()
        (root/'unexpected-directory').mkdir()
        require(run('verify_release.py').returncode!=0,'unexpected directory rejection');checks.append('unexpected empty directory rejected')
        (root/'unexpected-directory').rmdir()
        (root/'bad-link').symlink_to(root/'README.md')
        result=run('verify_release.py');require(result.returncode!=0 and 'symlink in release tree' in result.stderr,'symlink rejection');checks.append('symlink rejected')
        (root/'bad-link').unlink()
        (root/'replay-output').mkdir();(root/'replay-output'/'generated.json').write_text('{}\n')
        require(run('verify_release.py').returncode==0,'documented generated output accepted');checks.append('documented generated output accepted')
        result=run('replay.py','--out','replay-output')
        require(result.returncode!=0 and 'Output directory must not already exist' in result.stderr,'existing output rejection');checks.append('existing output rejected without overwrite')
        result=run('replay.py','--out','unapproved-output')
        require(result.returncode!=0 and 'only the documented replay-output directory' in result.stderr,'custom in-release output rejection');checks.append('custom in-release output rejected')
        require(not (root/'unapproved-output').exists(),'no rejected output side effect');checks.append('rejected output not created')
        require(not list(root.rglob('__pycache__')),'bytecode suppression');checks.append('no bytecode cache created by advertised commands')
        require(run('verify_release.py').returncode==0,'verification after expected rejections');checks.append('copy still verifies after rejection tests')
    receipt=dict(status='passed',checks=checks,check_count=len(checks),verification_scope='fresh temporary copy of release; all intentional mutations removed')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

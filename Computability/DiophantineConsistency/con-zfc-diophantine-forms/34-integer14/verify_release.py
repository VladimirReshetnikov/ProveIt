"""Verify the sealed release, replaying only newly authored checks in a copy.
Python 3.10+, SymPy, and NumPy are required. No received program is executed.
"""
import sys
if not __debug__:
    raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
import hashlib, json, os, shutil, subprocess, tempfile, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise RuntimeError(message)
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def snapshot(root):
    return {str(p.relative_to(root)):digest(p) for p in root.rglob('*') if p.is_file()}
def integrity(root):
    require(not any(p.is_symlink() for p in root.rglob('*')), 'Symlinks are not allowed.')
    manifest=json.loads((root/'RELEASE_MANIFEST.json').read_text())
    expected={r['path'] for r in manifest['files']}
    actual={str(p.relative_to(root)) for p in root.rglob('*')
            if p.is_file() and str(p.relative_to(root))!='RELEASE_MANIFEST.json'}
    require(len(expected)==len(manifest['files']), 'Duplicate manifest path.')
    require(expected==actual, 'Manifest file set mismatch.')
    for row in manifest['files']:
        p=(root/row['path']).resolve()
        require(p.is_relative_to(root.resolve()), 'Path escapes release.')
        require(p.stat().st_size==row['bytes'] and digest(p)==row['sha256'],
                'Digest mismatch: '+row['path'])
    return len(expected)

def main():
    started=time.monotonic(); count=integrity(ROOT); before=snapshot(ROOT)
    plan=json.loads((ROOT/'CHECK_PLAN.json').read_text())
    done=[]
    with tempfile.TemporaryDirectory(prefix='con-zfc-round5-') as tmp:
        work=Path(tmp)/'release'; shutil.copytree(ROOT,work)
        env=os.environ.copy()
        env['PYTHONDONTWRITEBYTECODE']='1'
        env['PYTHONNOUSERSITE']='1'
        env.pop('PYTHONOPTIMIZE',None); env.pop('PYTHONPATH',None)
        for check in plan['checks']:
            args=check['args']; script=work/args[0]
            require(script.is_file() and script.suffix=='.py','Missing checker: '+args[0])
            t=time.monotonic(); print('Checking '+args[0]+' ...',flush=True)
            result=subprocess.run([sys.executable,'-B',*args],cwd=work,env=env,
                                  text=True,capture_output=True)
            require(result.returncode==0,args[0]+' failed:\n'+result.stdout[-7000:]+'\n'+result.stderr[-7000:])
            done.append({'script':args[0],'seconds':round(time.monotonic()-t,3)})
        for item in plan.get('arithmetic_packets',[]):
            old=json.loads((ROOT/item['path']).read_text())
            new=json.loads((work/item['path']).read_text())
            for key in item['keys']:
                require(old.get(key)==new.get(key), 'Emitter changed frozen arithmetic: '+item['path']+' '+key)
    require(integrity(ROOT)==count and snapshot(ROOT)==before,
            'Original release tree changed, including its manifest.')
    print(json.dumps({'status':'PASS','files':count,'checks':done,
         'seconds':round(time.monotonic()-started,3),'delivered_tree_unchanged':True,
         'scope':'Finite algebraic, numerical and provenance audits; not a kernel certificate.'},indent=2))
if __name__=='__main__':
    main()

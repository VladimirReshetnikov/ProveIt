#!/usr/bin/env python3
"""Owned package-isolation negative controls; only temporary copies are modified."""
import os,sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE'in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION')
import hashlib,json,shutil,subprocess,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def require(ok,message):
    if not ok:raise SystemExit(message)

def inventory(root):
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}

def run(root,flags=(),environ=None):
    env=dict(os.environ)
    for k in ('PYTHONPATH','PYTHONHOME','PYTHONOPTIMIZE','PYTHONSTARTUP'):env.pop(k,None)
    env['PYTHONDONTWRITEBYTECODE']='1'
    env.update(environ or {})
    return subprocess.run([sys.executable,*flags,'-B',str(root/'verify_release.py'),'--hash-only'],cwd=root.parent,env=env,text=True,capture_output=True,timeout=90)

def main():
    before=inventory(ROOT);results={}
    with tempfile.TemporaryDirectory(prefix='k215-outer-controls-')as td:
        root=Path(td)/'packet';shutil.copytree(ROOT,root)
        clean=run(root)
        require(clean.returncode==0,'CLEAN_COPY_FAILED: '+clean.stdout+clean.stderr)
        results['clean_copy_outside_original_cwd']='passed'
        for label,flags,env in [('optimized_O',('-O',),{}),('optimized_OO',('-OO',),{}),('optimize_environment',(),{'PYTHONOPTIMIZE':'1'}),('optimize_zero_environment',(),{'PYTHONOPTIMIZE':'0'})]:
            r=run(root,flags,env);require(r.returncode!=0 and 'UNSAFE_PYTHON_OPTIMIZATION'in r.stdout+r.stderr,'UNSAFE_OPTIMIZATION_ACCEPTED: '+label);results[label]='rejected'
        cases=[('changed_payload','calibration/check_fresh_padding.py','PAYLOAD_SHA256_MISMATCH'),('changed_manifest','MANIFEST.json','MANIFEST_SHA256_MISMATCH')]
        for label,name,reason in cases:
            p=root/name;old=p.read_bytes();p.write_bytes(old+b'\n');r=run(root);p.write_bytes(old)
            require(r.returncode!=0 and reason in r.stdout+r.stderr,'TAMPERING_ACCEPTED: '+label);results[label]='rejected'
        p=root/'unexpected.txt';p.write_text('unlisted');r=run(root);p.unlink()
        require(r.returncode!=0 and 'UNMANIFESTED_OR_MISSING_FILE'in r.stdout+r.stderr,'EXTRA_FILE_ACCEPTED');results['unlisted_file']='rejected'
        p=root/'calibration/finite_checks.json';old=p.read_bytes();p.unlink();r=run(root);p.write_bytes(old)
        require(r.returncode!=0 and 'MISSING_OR_SYMLINK_FILE'in r.stdout+r.stderr,'MISSING_FILE_ACCEPTED');results['missing_file']='rejected'
        p.unlink();p.symlink_to(ROOT/'calibration/finite_checks.json');r=run(root);p.unlink();p.write_bytes(old)
        require(r.returncode!=0 and 'MISSING_OR_SYMLINK_FILE'in r.stdout+r.stderr,'FILE_SYMLINK_ACCEPTED');results['payload_symlink']='rejected'
        p=root/'extra_directory';p.symlink_to(ROOT/'calibration',target_is_directory=True);r=run(root);p.unlink()
        require(r.returncode!=0 and 'SYMLINK_IN_RELEASE'in r.stdout+r.stderr,'DIRECTORY_SYMLINK_ACCEPTED');results['directory_symlink']='rejected'
        require(run(root).returncode==0,'RESTORED_COPY_FAILED')
        results['restored_copy']='passed'
    require(inventory(ROOT)==before,'ORIGINAL_CHANGED_BY_TESTS')
    print(json.dumps({'status':'PASS_OUTER_ISOLATION_NEGATIVE_CONTROLS','checks':results,'original_packet_unchanged':True},indent=2))
if __name__=='__main__':main()

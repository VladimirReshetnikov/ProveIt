#!/usr/bin/env python3
"""Exercise the public builder's output guards normally and with python -O.

No full build is run here. Every attempted target must be rejected before work.
The source tree and sentinel bytes are checked after every case.
"""
import sys
sys.dont_write_bytecode = True
if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(640)
from pathlib import Path
import hashlib
import json
import os
import subprocess
import shutil
import tempfile

SOURCE=Path(__file__).resolve().parent


def require(condition,message):
    if not condition: raise ValueError(message)


def inventory():
    return {p.relative_to(SOURCE).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in SOURCE.rglob('*') if p.is_file()}


def main():
    require(len(sys.argv)==1,'guard_tests.py takes no arguments')
    initial=inventory()
    passed=[]
    with tempfile.TemporaryDirectory(prefix='report232-guards-') as raw:
        root=Path(raw)
        file=root/'existing-file';file.write_bytes(b'untouched\n')
        directory=root/'existing-directory';directory.mkdir()
        (directory/'sentinel').write_bytes(b'untouched-directory\n')
        dangling=root/'dangling';dangling.symlink_to(root/'absent-target')
        real_parent=root/'real-parent';real_parent.mkdir()
        linked_parent=root/'linked-parent';linked_parent.symlink_to(real_parent,target_is_directory=True)
        targets={'existing file':file,'existing directory':directory,'dangling symlink':dangling,
                 'symlink parent':linked_parent/'new-child','inside source':SOURCE/'forbidden-new-output'}
        for optimized in (False,True):
            for name,target in targets.items():
                command=[sys.executable,'-B',*(['-O'] if optimized else []),str(SOURCE/'build.py'),'--output',str(target)]
                completed=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
                require(completed.returncode!=0,'Guard unexpectedly accepted '+name)
                require(file.read_bytes()==b'untouched\n','Existing file modified')
                require((directory/'sentinel').read_bytes()==b'untouched-directory\n','Existing directory modified')
                require(dangling.is_symlink() and not (root/'absent-target').exists(),'Dangling symlink followed')
                require(not (real_parent/'new-child').exists(),'Symlink parent followed')
                require(inventory()==initial,'Source tree modified during guard test')
                passed.append({'case':name,'optimized':optimized,'rejected':True})
            clone=root/('clone-optimized' if optimized else 'clone-normal')
            shutil.copytree(SOURCE,clone)
            readme=clone/'README.md'
            original=readme.read_bytes()
            readme.write_bytes(original+b'\nINTENTIONAL TEST CORRUPTION\n')
            for case in ('tampered source','missing manifest'):
                if case == 'missing manifest':
                    readme.write_bytes(original)
                    (clone/'SHA256SUMS').unlink()
                target=root/('invalid-'+str(optimized)+'-'+case.replace(' ','-'))
                command=[sys.executable,'-B',*(['-O'] if optimized else []),str(clone/'build.py'),'--output',str(target)]
                completed=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
                require(completed.returncode!=0 and not target.exists(),'Manifest guard accepted '+case)
                require(inventory()==initial,'Source tree modified by corruption test')
                passed.append({'case':case,'optimized':optimized,'rejected':True})
    print(json.dumps({'status':'PASS','cases':passed,'source_unchanged':True},sort_keys=True,indent=2))


if __name__=='__main__': main()

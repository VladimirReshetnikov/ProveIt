#!/usr/bin/env python3
"""Negative package regressions and explicit optimized-mode arithmetic guards.

All mutations are confined to disposable package copies. The source is read-only.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import verify_package as v

ROOT=Path(__file__).resolve().parent

def rejected(root):
    try:
        v.inventory(root)
    except (v.PackageError,OSError,ValueError):
        return
    raise RuntimeError('Mutated package was accepted')

def rewrite_manifest(root, transform):
    p=root/'SHA256SUMS';p.write_text(transform(p.read_text()))

def main():
    before=v.inventory(ROOT)
    tests=[]
    mutations=[
        ('extra_file',lambda p:(p/'unexpected.txt').write_text('extra')),
        ('extra_empty_directory',lambda p:(p/'unexpected').mkdir()),
        ('missing_file',lambda p:(p/'certificate/certificate.json').unlink()),
        ('changed_bytes',lambda p:(p/'certificate/certificate.json').write_bytes(b'{}\n')),
        ('missing_manifest',lambda p:(p/'SHA256SUMS').unlink()),
        ('duplicate_manifest_entry',lambda p:rewrite_manifest(p,lambda s:s+s.splitlines()[0]+'\n')),
        ('unsafe_manifest_path',lambda p:rewrite_manifest(p,lambda s:'0'*64+'  ../escape\n'+s)),
        ('malformed_manifest_hash',lambda p:rewrite_manifest(p,lambda s:'g'+s[1:])),
        ('missing_manifest_newline',lambda p:rewrite_manifest(p,lambda s:s.rstrip('\n'))),
        ('unsorted_manifest',lambda p:rewrite_manifest(p,lambda s:'\n'.join(reversed(s.splitlines()))+'\n')),
        ('symlink_file',lambda p:(p/'unexpected-link').symlink_to('certificate/certificate.json')),
        ('symlink_directory',lambda p:(p/'unexpected-link').symlink_to('certificate',target_is_directory=True)),
    ]
    with tempfile.TemporaryDirectory(prefix='report130-negative-') as tmp:
        base=Path(tmp)
        for name,mutate in mutations:
            copy=base/name;shutil.copytree(ROOT,copy)
            # The source may be read-only; only its disposable copy is made writable.
            copy.chmod(0o755)
            for entry in copy.rglob('*'):
                entry.chmod(0o755 if entry.is_dir() else 0o644)
            mutate(copy);rejected(copy);tests.append(name)
        code='''import sys
sys.path.insert(0,sys.argv[1])
import certify as c
from fractions import Fraction as Q
checks=[]
for name,fn in [
 ('zero_reciprocal',lambda:c.I(0).inv()),
 ('straddling_reciprocal',lambda:c.I.endpoints(-1,1).inv()),
 ('negative_square_root',lambda:c.I(-1).sqrt()),
 ('explicit_false_guard',lambda:c.require(False))]:
 try: fn()
 except c.CertificationError: checks.append(name)
 else: raise RuntimeError(name+' accepted')
c.RHO_LO[3]=Q('0.39')
try: c.certify(3,c.pi_bound())
except c.CertificationError: checks.append('wrong_radius_locator')
else: raise RuntimeError('Wrong locator accepted')
import json
print(json.dumps(checks))
'''
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
        for flags,label in (([],'ordinary'),(['-O'],'optimized')):
            result=subprocess.run([sys.executable,'-B',*flags,'-c',code,str(ROOT/'certificate')],cwd=base,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
            v.require(result.returncode==0,'Guard test failed: '+result.stderr.decode(errors='replace'))
            guards=json.loads(result.stdout)
            v.require(len(guards)==5,'Incomplete guard test')
            tests.extend(label+'_'+name for name in guards)
    v.require(v.inventory(ROOT)==before,'Source changed during negative tests')
    print(json.dumps({'status':'PASS','negative_tests':tests,'source_unchanged':True},indent=2))

if __name__=='__main__':main()

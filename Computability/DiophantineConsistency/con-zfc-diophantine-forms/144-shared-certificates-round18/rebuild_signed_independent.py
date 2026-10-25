#!/usr/bin/env python3
"""Rebuild all twelve signed equations in a clean temporary component copy."""
import hashlib, json, pathlib, shutil, subprocess, sys, tempfile
ROOT=pathlib.Path(__file__).resolve().parent
source=ROOT/'signed'
names=[str(p.relative_to(source)) for p in sorted(source.glob('sphere_*/*')) if p.is_file()]
before={n:hashlib.sha256((source/n).read_bytes()).hexdigest() for n in names}
with tempfile.TemporaryDirectory(prefix='round18-signed-') as td:
    target=pathlib.Path(td)/'signed'
    shutil.copytree(source,target,ignore=shutil.ignore_patterns('__pycache__'))
    proc=subprocess.run([sys.executable,'-B','build_spheres.py'],cwd=target,capture_output=True,text=True)
    if proc.returncode:
        raise RuntimeError(proc.stdout+proc.stderr)
    after={n:hashlib.sha256((target/n).read_bytes()).hexdigest() for n in names}
    if before != after:
        raise ValueError('Non-identical signed reconstruction')
print(json.dumps({'status':'PASS','byte_identical_files':len(names),'sha256':before},indent=2))

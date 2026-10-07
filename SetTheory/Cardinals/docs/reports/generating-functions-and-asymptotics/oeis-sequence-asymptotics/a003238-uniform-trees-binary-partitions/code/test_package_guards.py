#!/usr/bin/env python3
"""Deliberate package-level failures; each must fail before any reproduction."""
import importlib.util
import json
from pathlib import Path
import tempfile
import sys
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('runner',Path(__file__).with_name('reproduce.py'))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
cases=[]
def reject(name,action,phrase):
 try:action()
 except RuntimeError as err:
  if phrase not in str(err):raise RuntimeError(name+': unexpected failure '+str(err))
  cases.append(name)
 else:raise RuntimeError('UNSAFE: accepted '+name)
with tempfile.TemporaryDirectory() as tmp:
 root=Path(tmp)/'package';root.mkdir();m.ROOT=root
 (root/'reproduce.py').write_text('print(1)\n')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\n')
 names=m.source_names()
 (root/'extra.py').write_text('print(1)\n')
 reject('unlisted source file',m.source_names,'unlisted package files');(root/'extra.py').unlink()
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\nreproduce.py\n')
 reject('duplicate source inventory',m.source_names,'duplicate source inventory')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\n../outside.py\n')
 reject('traversal source path',m.source_names,'unsafe source path')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\n./reproduce.py\nreproduce.py\n')
 reject('noncanonical source path',m.source_names,'unsafe source path')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\nReport215.pdf\n')
 reject('reserved generated inventory member',m.source_names,'reserved generated file')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\nmissing.py\n')
 reject('missing source file',m.source_names,'missing or linked source')
 (root/'SOURCE_FILES.txt').write_text('SOURCE_FILES.txt\nreproduce.py\n')
 (root/'reproduce.py').write_text('assert True\n')
 reject('removable assertion',m.source_names,'assert in');(root/'reproduce.py').write_text('print(1)\n')
 target=Path(tmp)/'external';target.write_text('x')
 (root/'linked').symlink_to(target)
 reject('linked package path',m.source_names,'linked package path');(root/'linked').unlink()
 (root/'MANIFEST.json').write_text('{"x":1,"x":2}')
 reject('duplicate JSON keys',lambda:m.read_json(root/'MANIFEST.json'),'duplicate JSON key')
 manifest={'format':'Report215 SHA256 manifest v1','files':{name:m.sha((root/name).read_bytes()) for name in names}}
 m.write_json(root/'MANIFEST.json',manifest);m.verify_manifest(root,names)
 (root/'reproduce.py').write_text('print(2)\n')
 reject('source byte tampering',lambda:m.verify_manifest(root,names),'manifest byte mismatch')
 manifest['files'].pop('reproduce.py');m.write_json(root/'MANIFEST.json',manifest)
 reject('manifest inventory mismatch',lambda:m.verify_manifest(root,names),'manifest inventory mismatch')
 reject('existing output',lambda:m.validate_output(root),'output already exists')
 reject('source descendant output',lambda:m.validate_output(root/'new'),'output overlaps source tree')
 reject('missing output parent',lambda:m.validate_output(Path(tmp)/'missing'/'new'),'output parent does not exist')
 linked=Path(tmp)/'linked';linked.symlink_to(Path(tmp)/'notthere')
 reject('dangling output symlink',lambda:m.validate_output(linked),'symbolic link')
 before=sorted(str(p.relative_to(root)) for p in root.rglob('*'))
 reject('intentional pre-write failure',lambda:m.require(False,'intentional pre-write failure'),'intentional pre-write failure')
 if before!=sorted(str(p.relative_to(root)) for p in root.rglob('*')):raise RuntimeError('pre-write guard changed files')
print(json.dumps({'status':'PASS','deliberate_rejection_count':len(cases),'deliberate_rejections':cases,'all_checks_explicit':True},indent=2,sort_keys=True))

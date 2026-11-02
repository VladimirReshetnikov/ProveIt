#!/usr/bin/env python3
"""No-Lean controls for the required direct Init object."""
import importlib.util,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('replay',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
with tempfile.TemporaryDirectory(prefix='compact-symbolic-init-') as d:
 package=Path(d);init=package/'Init.olean'
 for label in ('missing','directory','dangling-symlink'):
  if label=='directory':init.mkdir()
  if label=='dangling-symlink':init.rmdir();init.symlink_to(package/'absent')
  try:m.require_init(package)
  except ValueError:continue
  raise RuntimeError('failed to reject '+label)
 init.unlink();init.write_bytes(b'fake regular object')
 if m.require_init(package)!=str(init):raise RuntimeError('valid file rejected')
print('PASS required Init file and 3 negative controls; no Lean launched')

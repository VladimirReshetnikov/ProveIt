#!/usr/bin/env python3
"""No-Lean mutation controls for direct companions, outputs and frozen sources."""
import importlib.util,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('replay',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def reject(label,fn):
 try:fn()
 except ValueError:return
 raise RuntimeError('failed to reject '+label)
with tempfile.TemporaryDirectory(prefix='fixed-graph-integrity-') as d:
 root=Path(d);stem=root/'Obj';obj=root/'Obj.olean';obj.write_bytes(b'object');snap=m.guard(stem);m.checkguards(snap);m.require_output(obj)
 obj.write_bytes(b'changed');reject('changed object',lambda:m.checkguards(snap));obj.write_bytes(b'object')
 obj.unlink();reject('removed object',lambda:m.checkguards(snap));reject('missing output',lambda:m.require_output(obj));obj.write_bytes(b'object')
 companion=root/'Obj.olean.private';companion.write_bytes(b'late');reject('added companion',lambda:m.checkguards(snap));companion.unlink()
 target=root/'other';target.write_bytes(b'object');obj.unlink();obj.symlink_to(target);reject('repointed object',lambda:m.checkguards(snap));reject('symlink output',lambda:m.require_output(obj));obj.unlink();obj.mkdir();reject('directory output',lambda:m.require_output(obj));obj.rmdir()
 source=root/'Source.lean';source.write_bytes(b'source');rows=[('Source',source,m.H(source),[])];m.check_frozen(rows);source.write_bytes(b'late mutation');reject('late source change',lambda:m.check_frozen(rows));source.write_bytes(b'source');source.unlink();source.symlink_to(target);target.write_bytes(b'source');reject('symlink frozen source with matching bytes',lambda:m.check_frozen(rows))
print('PASS object/companion/frozen-source checks and 9 negative controls; no Lean launched')

import importlib.util,tempfile
from pathlib import Path
BASE=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge').resolve()
def reject(label,fn):
 try:fn()
 except ValueError:return
 raise RuntimeError('accepted '+label)
with tempfile.TemporaryDirectory(prefix='independent-contextual-row-controls-',dir='/tmp') as d:
 root=Path(d)
 for directory in ('compact44-inverse-lookup-prototype','compact44-model-noextra-prototype'):
  p=BASE/directory/'contextual-replay.py';s=importlib.util.spec_from_file_location('driver',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
  q=root/directory;q.mkdir();init=q/'Init.olean';dep=q/'Dep.olean';init.write_bytes(b'init');dep.write_bytes(b'dep');m.require_objects({str(init),str(dep)},'test','test')
  for f in (init,dep):
   old=f.read_bytes();f.unlink();reject('missing direct '+str(f),lambda:m.require_objects({str(init),str(dep)},'test','test'));f.write_bytes(old)
  g=m.guard(str(dep)[:-6]);m.checkguards(g);dep.write_bytes(b'changed');reject('changed direct',lambda:m.checkguards(g));dep.write_bytes(b'dep')
  added=q/'Dep.olean.private';added.write_bytes(b'late');reject('late companion',lambda:m.checkguards(g));added.unlink()
  original=m.HERE/('CompactInverseInventory.lean' if 'inverse' in directory else 'CompactNoExtra.lean');f=q/'Frozen.lean';f.write_bytes(original.read_bytes());m.check_frozen(f,original);f.unlink();f.symlink_to(original);reject('matching-content source symlink',lambda:m.check_frozen(f,original))
  print(directory,'PASS independent direct/companion/frozen-source mutations')
print('PASS no Lean launched')

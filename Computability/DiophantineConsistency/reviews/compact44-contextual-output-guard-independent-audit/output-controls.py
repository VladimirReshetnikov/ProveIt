import importlib.util,tempfile
from pathlib import Path
BASE=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge').resolve()
def reject(label,fn):
 try:fn()
 except ValueError:return
 raise RuntimeError('accepted '+label)
with tempfile.TemporaryDirectory(prefix='independent-context-output-',dir='/tmp') as d:
 root=Path(d)
 for directory in ('compact44-inverse-lookup-prototype','compact44-model-noextra-prototype'):
  p=BASE/directory/'contextual-replay.py';s=importlib.util.spec_from_file_location('driver',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);q=root/directory;q.mkdir();obj=q/'Output.olean';m.output_guards(obj,before=True)
  for suffix in m.SUFFIXES:
   f=q/('Output'+suffix);f.write_bytes(b'preexisting');reject('preexisting '+suffix,lambda:m.output_guards(obj,before=True));f.unlink()
  obj.write_bytes(b'object');snap=m.output_guards(obj,before=False);m.checkguards(snap)
  for suffix in m.SUFFIXES[1:]:
   f=q/('Output'+suffix);f.write_bytes(b'late');reject('late companion '+suffix,lambda:m.checkguards(snap));reject('post-output companion '+suffix,lambda:m.output_guards(obj,before=False));f.unlink()
  obj.write_bytes(b'changed');reject('changed output',lambda:m.checkguards(snap));obj.unlink();reject('missing output',lambda:m.output_guards(obj,before=False));other=q/'target';other.write_bytes(b'object');obj.symlink_to(other);reject('symlink output',lambda:m.output_guards(obj,before=False))
  print(directory,'PASS all',len(m.SUFFIXES),'preexisting slots,',len(m.SUFFIXES)-1,'post/late companions, and output mutation cases')
print('PASS no Lean launched')

#!/usr/bin/env python3
"""Focused no-Lean controls for carry-reset source, object and report guards."""
import importlib.util,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('replay',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def reject(label,fn):
 try:fn()
 except ValueError:return
 raise RuntimeError('failed to reject '+label)
m.validate_output(m.EXPECTED)
for label,text in [('missing report',m.EXPECTED.splitlines(True)[0]),('extra axiom',m.EXPECTED.replace('Quot.sound','Quot.sound, bogus',1)),('warning',m.EXPECTED+'warning: injected\n'),('sorryAx',m.EXPECTED+'sorryAx\n')]:reject(label,lambda text=text:m.validate_output(text))
with tempfile.TemporaryDirectory(prefix='clean-carry-controls-',dir='/tmp') as d:
 root=Path(d);init=root/'Init.olean';reject('missing Init',lambda:m.require_init(root));init.write_bytes(b'init');m.require_init(root)
 seed=root/'seed.olean';seed.write_bytes(b'seed');g=m.guard(str(seed)[:-6]);m.checkguards(g);m.require_no_seed_companions(g,seed,'test');seed.write_bytes(b'changed');reject('seed mutation',lambda:m.checkguards(g));seed.write_bytes(b'seed')
 extra=root/'seed.olean.private';extra.write_bytes(b'new');reject('new companion',lambda:m.checkguards(g));g2=m.guard(str(seed)[:-6]);reject('initial seed companion',lambda:m.require_no_seed_companions(g2,seed,'test'));extra.unlink()
 out=root/'output.olean';out.write_bytes(b'object');m.require_output(out);out.unlink();reject('missing output',lambda:m.require_output(out));out.symlink_to(seed);reject('symlink output',lambda:m.require_output(out))
 target=root/'Slot.olean';m.output_guards(target,before=True)
 for suffix in m.SUFFIXES:
  slot=root/('Slot'+suffix);slot.write_bytes(b'unexpected');reject('preexisting output slot '+suffix,lambda:m.output_guards(target,before=True));slot.unlink()
 target.write_bytes(b'object');snapshot=m.output_guards(target,before=False)
 for suffix in m.SUFFIXES[1:]:
  slot=root/('Slot'+suffix);slot.write_bytes(b'injected');reject('post-output companion '+suffix,lambda:m.output_guards(target,before=False));reject('late output companion '+suffix,lambda:m.checkguards(snapshot));slot.unlink()
 source=root/'Frozen.lean';source.write_bytes(m.SOURCE.read_bytes());m.check_source(source);source.write_bytes(b'changed');reject('source mutation',lambda:m.check_source(source));source.unlink();source.symlink_to(m.SOURCE);reject('matching-content source symlink',lambda:m.check_source(source))
print('PASS clean-carry positive cases and 40 negative checks; no Lean launched')

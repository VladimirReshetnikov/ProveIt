#!/usr/bin/env python3
import hashlib,importlib.util,subprocess,sys,tempfile
from pathlib import Path
p=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-row-transport-prototype/replay.py').resolve();h='4030748893a24268b76ee70fb97164d9b9649b796acbad1a557e73a0b9feb80a'
if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise ValueError('driver hash')
s=importlib.util.spec_from_file_location('guard',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.PINS={p:'0'*64}
try:m.pins();raise AssertionError('bad pin accepted')
except ValueError as e:
 if 'fixed input drift' not in str(e):raise
with tempfile.TemporaryDirectory(prefix='row-guard-review-') as d:
 stem=Path(d)/'obj';obj=Path(str(stem)+'.olean');obj.write_bytes(b'a');guards=m.guard(stem);m.checkguards(guards);obj.write_bytes(b'b')
 try:m.checkguards(guards);raise AssertionError('changed companion accepted')
 except ValueError as e:
  if 'companion drift' not in str(e):raise
 obj.write_bytes(b'a');Path(str(stem)+'.ilean').write_bytes(b'extra')
 try:m.checkguards(guards);raise AssertionError('new companion accepted')
 except ValueError as e:
  if 'unexpected companion' not in str(e):raise
for flags in (['-O','-I','-S'],[]):
 q=subprocess.run([sys.executable,*flags,str(p),'--help'],capture_output=True,text=True,timeout=10)
 if q.returncode==0 or 'requires nonoptimized python3 -I -S' not in q.stderr:raise ValueError('interpreter guard')
with tempfile.TemporaryDirectory(prefix='ipra-compact-row-transport-pair-review-',dir='/tmp') as d:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d],capture_output=True,text=True,timeout=10)
 if q.returncode==0 or 'output exists' not in q.stderr or list(Path(d).iterdir()):raise ValueError('existing output')
print('PASS_PIN_COMPANION_INTERPRETER_OUTPUT_GUARDS')

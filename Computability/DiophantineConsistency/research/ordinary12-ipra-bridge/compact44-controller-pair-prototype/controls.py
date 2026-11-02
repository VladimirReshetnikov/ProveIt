#!/usr/bin/env python3
"""Fast no-Lean interpreter, pins, output and HEAD guard controls."""
import importlib.util,subprocess,sys,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent/'replay.py';s=importlib.util.spec_from_file_location('driver',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
old=m.PINS;m.PINS={m.DATA:'0'*64}
try:
 try:m.verify(Path('/tmp/ipra-historical-audit-review-01'));raise AssertionError('bad pin accepted')
 except ValueError as e:
  if 'pinned input drift' not in str(e):raise
finally:m.PINS=old
for flags in (['-I','-S','-O'],[],['-S','-B'],['-I','-B']):
 q=subprocess.run([sys.executable,*flags,str(p),'--help'],capture_output=True,text=True,timeout=10)
 if not q.returncode or 'invoke with python3 -I -S' not in q.stderr:raise ValueError('interpreter guard')
with tempfile.TemporaryDirectory(prefix='ipra-compact-controller-pair-control-',dir='/tmp') as d:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d,'--expected-head','invalid','--historical-view','/tmp/ipra-historical-audit-review-01'],capture_output=True,text=True,timeout=10)
 if not q.returncode or 'fresh direct /tmp output required' not in q.stderr or list(Path(d).iterdir()):raise ValueError('occupied output guard')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d+'-new','--expected-head','invalid','--historical-view','/tmp/ipra-historical-audit-review-01'],capture_output=True,text=True,timeout=10)
 if not q.returncode or 'unexpected launch HEAD' not in q.stderr or Path(d+'-new').exists():raise ValueError('head guard')
print('PASS_BAD_PIN_INTERPRETER_OUTPUT_AND_HEAD_GUARDS')

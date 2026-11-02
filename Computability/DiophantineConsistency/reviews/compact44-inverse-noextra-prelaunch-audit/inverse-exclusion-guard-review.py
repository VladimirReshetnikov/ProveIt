import hashlib,importlib.util,subprocess,sys,tempfile
from pathlib import Path
B=Path(__file__).resolve().parents[2]/'research/ordinary12-ipra-bridge'
for name,h,prefix in [('compact44-inverse-lookup-prototype','ec9888b8345faa873f6d419bbcedf5696f06e1f8e5ffc6ad3833353bafcac0e3','ipra-compact-inverse-lookup-pair-'),('compact44-model-noextra-prototype','6e14d1d6f10172d84b7ca4d7abf171771a8021868a2d2f723f42e0ceb608e12e','ipra-compact-model-noextra-pair-')]:
 p=B/name/'replay.py';assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 s=importlib.util.spec_from_file_location('guard',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.PINS={p:'0'*64}
 try:m.pins();raise AssertionError('bad pin accepted')
 except ValueError as e:assert 'fixed input drift' in str(e)
 with tempfile.TemporaryDirectory(prefix='word-guard-review-') as d:
  stem=Path(d)/'obj';obj=Path(str(stem)+'.olean');obj.write_bytes(b'a');guards=m.guard(stem);m.checkguards(guards);obj.write_bytes(b'b')
  try:m.checkguards(guards);raise AssertionError('changed companion accepted')
  except ValueError as e:assert 'companion drift' in str(e)
  obj.write_bytes(b'a');Path(str(stem)+'.ilean').write_bytes(b'extra')
  try:m.checkguards(guards);raise AssertionError('new companion accepted')
  except ValueError as e:assert 'unexpected companion' in str(e)
 for flags in (['-O','-I','-S'],[],['-S','-B'],['-I','-B']):
  q=subprocess.run([sys.executable,*flags,str(p),'--help'],capture_output=True,text=True,timeout=10);assert q.returncode and 'requires nonoptimized python3 -I -S' in q.stderr
 with tempfile.TemporaryDirectory(prefix=prefix+'review-',dir='/tmp') as d:
  q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d],capture_output=True,text=True,timeout=10);assert q.returncode and 'output exists' in q.stderr and not list(Path(d).iterdir())
 print(name,'PASS_PIN_COMPANION_INTERPRETER_OUTPUT_GUARDS')

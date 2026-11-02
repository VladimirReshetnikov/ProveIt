#!/usr/bin/env python3
"""Pin/output/optimized controls for the exact no-Lean replay."""
import hashlib,importlib.util,subprocess,sys,tempfile
from pathlib import Path
p=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-concrete-digits-client-prototype/replay.py').resolve();h='9b760773ff4a03a67226406868ecc3de17902154c9515da20e502024f408a6bf'
if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise ValueError('driver hash')
s=importlib.util.spec_from_file_location('guard',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.PINS={m.SOURCES[0]:'0'*64}
try:m.verify();raise AssertionError('bad pin accepted')
except ValueError as e:
 if 'fixed input drift' not in str(e):raise
with tempfile.TemporaryDirectory(prefix='ipra-freej-concrete-digits-client-pair-review-',dir='/tmp') as d:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d],capture_output=True,text=True,timeout=10)
 if q.returncode==0 or 'fresh direct' not in q.stderr or list(Path(d).iterdir()):raise ValueError('existing output accepted')
q=subprocess.run([sys.executable,'-O','-I','-S','-B',str(p),'--output','/tmp/ipra-freej-concrete-digits-client-pair-opt-review'],capture_output=True,text=True,timeout=10)
if q.returncode==0 or 'optimized Python rejected' not in q.stderr:raise ValueError('optimized accepted')
print('PASS_PIN_OUTPUT_OPT_GUARDS')

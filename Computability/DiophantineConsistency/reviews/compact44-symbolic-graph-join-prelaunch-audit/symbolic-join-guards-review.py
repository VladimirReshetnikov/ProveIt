import hashlib,importlib.util,subprocess,sys,tempfile
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'research/ordinary12-ipra-bridge/compact44-symbolic-graph-join-prototype/replay.py';assert hashlib.sha256(p.read_bytes()).hexdigest()=='71c0e0da4a04e62152a37ac68fd940487d14df2f0ed47cacfdbc35506e7934ad'
s=importlib.util.spec_from_file_location('g',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for f,h in m.PINS.items():assert hashlib.sha256(f.read_bytes()).hexdigest()==h,str(f)
m.PINS={m.LOW_AUDIT/'CHECK.json':'0'*64}
try:m.verify();raise AssertionError('bad low-audit pin accepted')
except ValueError as e:assert 'fixed input drift' in str(e)
for flags in (['-I','-S','-O'],[],['-S','-B'],['-I','-B']):
 q=subprocess.run([sys.executable,*flags,str(p),'--help'],capture_output=True,text=True,timeout=10);assert q.returncode and 'invoke with python3 -I -S, without optimization' in q.stderr
with tempfile.TemporaryDirectory(prefix='ipra-compact-symbolic-graph-join-pair-review-',dir='/tmp') as d:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d],capture_output=True,text=True,timeout=10);assert q.returncode and 'fresh direct' in q.stderr and not list(Path(d).iterdir())
print('PASS_ALL_INPUT_PINS_AND_NEGATIVE_PIN_INTERPRETER_OUTPUT_GUARDS')

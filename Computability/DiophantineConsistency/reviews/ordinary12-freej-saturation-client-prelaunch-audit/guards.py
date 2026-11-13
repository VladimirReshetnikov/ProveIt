#!/usr/bin/env python3
"""No-build guard controls against exact replay module."""
import hashlib,importlib.util,os,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2]
DRIVER=BASE/'research/ordinary12-ipra-bridge/free-j-saturation-client-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest() != '05e5563e0eaf17f7beb6a6e0b5412159b488c12fa615806d85b8678cef917d3f': raise ValueError('reviewed driver drift')
def need(ok,message):
 if not ok:raise ValueError(message)
spec=importlib.util.spec_from_file_location('guard_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.PINS={m.SOURCES[0]:'0'*64}
try:m.verify();raise AssertionError('accepted wrong source pin')
except ValueError as exc:need('fixed input drift' in str(exc),'unexpected pin failure')
with tempfile.TemporaryDirectory(prefix='ipra-freej-saturation-client-pair-existing-',dir='/tmp') as temp:
 p=subprocess.run([sys.executable,'-I','-S','-B',str(DRIVER),'--output',temp],capture_output=True,text=True,timeout=10)
 need(p.returncode!=0 and 'fresh direct' in p.stderr and not list(Path(temp).iterdir()),'existing output guard')
p=subprocess.run([sys.executable,'-O','-I','-S','-B',str(DRIVER),'--output','/tmp/ipra-freej-saturation-client-pair-optimized-review'],capture_output=True,text=True,timeout=10)
need(p.returncode!=0 and 'optimized Python rejected' in p.stderr,'optimized guard')
need(not Path('/tmp/ipra-freej-saturation-client-pair-optimized-review').exists(),'optimized created output')
print('PASS_PIN_AND_OUTPUT_AND_OPTIMIZATION_GUARDS')

#!/usr/bin/env python3
"""No-Lean HEAD, pin, companion and interpreter rejection controls."""
import hashlib,importlib.util,subprocess,sys,tempfile
from pathlib import Path
BASE=Path(__file__).resolve().parents[2];DRIVER=BASE/'research/ordinary12-ipra-bridge/compact44-relabel-pair-prototype/replay.py'
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='f2d574483b92a6648462a2700a23e2884ea5572c8f5b2162ccf6b068c9d61510':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
s=importlib.util.spec_from_file_location('relabel_guard',DRIVER);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.EXPECTED_HEAD='0'*40
try:m.check_head();raise AssertionError('accepted wrong HEAD')
except ValueError as e:need('HEAD changed' in str(e),'wrong HEAD check')
m.PINS={DRIVER:'0'*64}
try:m.check_pins();raise AssertionError('accepted bad pin')
except ValueError as e:need('fixed input drift' in str(e),'bad pin check')
with tempfile.TemporaryDirectory(prefix='relabel-guard-review-') as root:
 stem=Path(root)/'module';obj=Path(str(stem)+'.olean');obj.write_bytes(b'a');guards=m.scan(stem);m.check_guards(guards);obj.write_bytes(b'b')
 try:m.check_guards(guards);raise AssertionError('accepted modified object')
 except ValueError as e:need('companion drift' in str(e),'companion guard')
 obj.write_bytes(b'a');Path(str(stem)+'.ilean').write_bytes(b'extra')
 try:m.check_guards(guards);raise AssertionError('accepted unexpected companion')
 except ValueError as e:need('unexpected companion' in str(e),'missing companion guard')
for flags,reason in ((['-O','-I','-S'],'optimized Python rejected'),([], 'invoke with python3 -I -S')):
 p=subprocess.run([sys.executable,*flags,str(DRIVER),'--help'],capture_output=True,text=True,timeout=10)
 need(p.returncode!=0 and reason in p.stderr,'interpreter guard')
print('PASS_HEAD_PIN_COMPANION_INTERPRETER_GUARDS')

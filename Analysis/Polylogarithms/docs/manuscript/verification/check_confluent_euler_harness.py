"""Check stale-PASS replacement on an intentionally failed exact gate."""
import importlib.util
import json
from pathlib import Path

base=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('euler_checks',base/'check_confluent_euler.py')
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
target=base/'confluent-euler-intentional-failure.json'
target.write_text('{"status":"PASS","stale":true}\n',encoding='utf-8')

def fail():
    current=json.loads(target.read_text(encoding='utf-8'))
    if current.get('status')!='RUNNING' or 'stale' in current:
        raise RuntimeError('Stale receipt was not invalidated before checking')
    raise ValueError('Intentional exact-check failure for stale-PASS control')

module.exact_checks=fail
try:
    module.main(['--exact-only','--output',str(target)])
except ValueError as exc:
    if str(exc)!='Intentional exact-check failure for stale-PASS control':
        raise
else:
    raise RuntimeError('Injected failure was accepted')
receipt=json.loads(target.read_text(encoding='utf-8'))
if receipt.get('status')!='FAIL' or 'stale' in receipt:
    raise RuntimeError('Failed run left a stale PASS receipt')
print('PASS: stale PASS changed to RUNNING before exact checks and FAIL afterward')

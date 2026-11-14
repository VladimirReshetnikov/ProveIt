#!/usr/bin/env python3
"""Reconstruct PA194QH5 and replay its finite/universal certificates offline.

Python 3.10+ standard library. Default includes the independent literal-tape
engine. Historical PA logical calibration is a mathematical dependency.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile
ROOT=Path(__file__).resolve().parent
assert __debug__ and not sys.flags.optimize,'Run without -O or PYTHONOPTIMIZE.'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(command,cwd):
 result=subprocess.run([sys.executable,'-B',*map(str,command)],cwd=cwd,
  check=True,capture_output=True,text=True)
 print(Path(command[0]).name,'PASS',flush=True)
 return result.stdout
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--quick',action='store_true',help='Skip only the independent literal-tape replay.')
p.add_argument('--receipt',type=Path)
a=p.parse_args()
pins=json.loads((ROOT/'INPUT_HASHES.json').read_text())
for relative,digest in pins.items():assert sha(ROOT/relative)==digest,('input hash',relative)
with tempfile.TemporaryDirectory(prefix='pa194qh5-')as temp:
 work=Path(temp)/'qh5'
 shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.log'))
 run([work/'construction/build_qh5.py','--output',work/'machine'],work)
 run([work/'proof/check_source_binding5.py'],work)
 run([work/'proof/check_commands.py'],work)
 run([work/'proof/exchange_certificate.py'],work)
 run([work/'comparison/check_novelty.py'],work)
 for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json',
              'instructions.json','sites.json','folds.json','local_fold_cases.json']:
  assert(work/'machine'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),('rebuilt file differs',name)
 result={'status':'PASS','machine':'PA194QH5','dense_sha256':sha(work/'machine/machine.tm'),
  'working_states':194,'input_pins_checked':len(pins),
  'construction':json.loads((work/'machine/receipt.json').read_text()),
  'source_binding':json.loads((work/'proof/source_binding.json').read_text()),
  'command_words':json.loads((work/'proof/emitter_and_words_receipt.json').read_text()),
  'exchange_lines':len(json.loads((work/'proof/exchange_certificate.json').read_text())['lines']),
  'novelty':json.loads((work/'comparison/novelty.json').read_text()),
  'independent_replay':not a.quick,'kernel_checked':False}
 if not a.quick:
  run([work/'verification/check.py',work/'machine'],work)
  independent=json.loads((work/'machine/independent/receipt.json').read_text())
  assert independent==json.loads((ROOT/'machine/independent/receipt.json').read_text()),'independent receipt differs'
  result['independent']=independent
 if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k in('status','machine','dense_sha256','working_states','independent_replay','kernel_checked')},indent=2))

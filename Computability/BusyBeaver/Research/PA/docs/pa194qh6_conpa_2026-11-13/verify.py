#!/usr/bin/env python3
"""Rebuild and verify PA194QH6 without modifying delivered artifacts.

Python 3.10+, standard library only; no network, checkout, or solver needed.
The default also replays every universal literal-tape source contract.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
assert __debug__ and not sys.flags.optimize,'Keep Python assertions enabled.'
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--quick',action='store_true',help='Skip the independent literal-tape replay only.')
p.add_argument('--receipt',type=Path)
a=p.parse_args()
sha=lambda b:hashlib.sha256(b).hexdigest()
for name,digest in json.loads((ROOT/'PINNED_INPUTS.json').read_text()).items():
 assert sha((ROOT/name).read_bytes())==digest,('input integrity',name)
with tempfile.TemporaryDirectory(prefix='pa194qh6-verify-')as temp:
 out=Path(temp);machine=out/'machine'
 commands=[
  [ROOT/'construction/build_qh6.py','--output',machine],
  [ROOT/'proof/check_commands.py','--output',out/'commands.json'],
  [ROOT/'proof/check_source_binding.py','--output',out/'source_binding.json'],
  [ROOT/'proof/exchange_certificate.py','--output',out/'exchange.json'],
  [ROOT/'comparison/check_novelty.py','--candidate',ROOT/'machine/machine.tm',
   '--native',ROOT/'machine/machine.native.tm','--census-dir',ROOT/'comparison',
   '--output',out/'novelty.json'],
 ]
 for cmd in commands:
  subprocess.run([sys.executable,'-B',*map(str,cmd)],check=True,capture_output=True,text=True)
  print(Path(cmd[0]).name,'PASS',flush=True)
 for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json','instructions.json','sites.json','folds.json','local_fold_cases.json']:
  assert(machine/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),('rebuild mismatch',name)
 result={'status':'PASS','machine':'PA194QH6','dense_sha256':sha((machine/'machine.tm').read_bytes()),'construction':json.loads((machine/'receipt.json').read_text()),'command_words':json.loads((out/'commands.json').read_text()),'source_binding':json.loads((out/'source_binding.json').read_text()),'exchange_lines':len(json.loads((out/'exchange.json').read_text())['lines']),'independent_replay':not a.quick}
 result['novelty']=json.loads((out/'novelty.json').read_text())
 if not a.quick:
  subprocess.run([sys.executable,'-B',str(ROOT/'verification/check.py'),str(machine)],check=True)
  fresh=json.loads((machine/'independent/receipt.json').read_text())
  old=json.loads((ROOT/'machine/independent/receipt.json').read_text())
  # This one field is an output-directory label, not mathematical data.
  fresh.pop('family');old.pop('family')
  assert fresh==old,('independent receipt differs',fresh,old)
  result['independent']=fresh
 if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','independent_replay':not a.quick,'working_states':194,'dense_sha256':result['dense_sha256']},indent=2),flush=True)

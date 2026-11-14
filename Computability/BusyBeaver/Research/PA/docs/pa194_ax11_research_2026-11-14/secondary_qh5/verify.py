#!/usr/bin/env python3
"""Rebuild QH5 and replay its exact finite and universal symbolic certificates."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
assert __debug__ and not sys.flags.optimize,'Keep Python assertions enabled.'
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--quick',action='store_true',help='Skip only the independent literal-tape checker.')
p.add_argument('--receipt',type=Path)
a=p.parse_args();sha=lambda b:hashlib.sha256(b).hexdigest()
for name,digest in json.loads((ROOT/'PINNED_INPUTS.json').read_text()).items():
 assert sha((ROOT/name).read_bytes())==digest,('input mismatch',name)
with tempfile.TemporaryDirectory(prefix='pa194qh5-verify-')as tmp:
 out=Path(tmp);machine=out/'machine'
 for cmd in [[ROOT/'construction/build.py','--output',machine],
             [ROOT/'proof/check_commands.py','--output',out/'commands.json'],
             [ROOT/'proof/exchange_certificate.py','--output',out/'exchange.json']]:
  subprocess.run([sys.executable,'-B',*map(str,cmd)],check=True,capture_output=True,text=True)
  print(Path(cmd[0]).name,'PASS',flush=True)
 for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json','instructions.json','sites.json','folds.json','local_fold_cases.json','source_binding.json']:
  assert(machine/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),('exact rebuild mismatch',name)
 result={'status':'PASS','machine':'PA194QH5','dense_sha256':sha((machine/'machine.tm').read_bytes()),
         'construction':json.loads((machine/'receipt.json').read_text()),
         'source_binding':json.loads((machine/'source_binding.json').read_text()),
         'command_words':json.loads((out/'commands.json').read_text()),
         'exchange_lines':len(json.loads((out/'exchange.json').read_text())['lines']),
         'independent_replay':not a.quick,'kernel_checked':False}
 if not a.quick:
  subprocess.run([sys.executable,'-B',str(ROOT/'verification/check.py'),str(machine)],check=True)
  fresh=json.loads((machine/'independent/receipt.json').read_text());old=json.loads((ROOT/'machine/independent/receipt.json').read_text())
  fresh.pop('family');old.pop('family');assert fresh==old,('independent receipt differs',fresh,old)
  result['independent']=fresh
 if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','working_states':194,'dense_sha256':result['dense_sha256'],'independent_replay':not a.quick},indent=2),flush=True)

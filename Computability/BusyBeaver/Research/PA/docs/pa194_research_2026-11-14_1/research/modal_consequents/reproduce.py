#!/usr/bin/env python3
"""Reproduce the finite logical and compilation-input claims, offline."""
from pathlib import Path
import subprocess,sys,tempfile,json,re,hashlib
import verify_logic,check_emitter
HERE=Path(__file__).resolve().parent
NAMES=['old_to_BA.json','BA_to_old.json','old_to_BP.json','BP_to_old.json','H5_to_H5X.json','H5X_to_H5.json']
if not __debug__ or sys.flags.optimize:raise SystemExit('Use Python with assertions enabled.')
def run(*args):
 subprocess.run([sys.executable,'-B',*map(str,args)],check=True,cwd=HERE,stdout=subprocess.DEVNULL)
with tempfile.TemporaryDirectory(prefix='modal-consequents-') as temp:
 t=Path(temp);run(HERE/'prove.py','--output',t/'certificates')
 for name in NAMES+['generation.json']:
  assert (t/'certificates'/name).read_bytes()==(HERE/'certificates'/name).read_bytes(),name
 checks=[verify_logic.check(t/'certificates'/name)for name in NAMES]
 for positive,filename in [(False,'BAh5X.templates.txt'),(True,'BPh5X.templates.txt')]:
  args=[HERE/'make_templates.py','--output',t/filename]
  if positive:args.append('--positive')
  run(*args)
  assert (t/filename).read_bytes()==(HERE/filename).read_bytes(),filename
 emitter=[check_emitter.inspect(HERE/f'{stem}.best.grammar.json')for stem in ('BA','BP')]
 receipt=json.loads((HERE/'search_receipt.json').read_text())
 for row in receipt['runs']:
  text=(HERE/row['log']).read_text()
  match=re.search(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',text)
  assert match,'search log does not show completion'
  obs=dict(zip(['iterations','accepted','hits','best_score'],map(int,match.groups()[:4])))
  assert all(row[k]==v for k,v in obs.items()),row
  assert abs(row['elapsed_seconds']-float(match.group(5)))<0.000001
  for name,value in row['sha256'].items():
   assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==value,name
 result={'status':'PASS','certificate_checks':checks,'emitters':emitter,
         'search_records_verified':len(receipt['runs']),
         'searches_rerun':False,'physical_source_contracts_claimed':False}
 print(json.dumps(result,indent=2))

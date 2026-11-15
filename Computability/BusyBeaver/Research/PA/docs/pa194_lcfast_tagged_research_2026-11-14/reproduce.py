#!/usr/bin/env python3
"""Rebuild in a temporary directory and compare with frozen outputs."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--construction-only',action='store_true');args=p.parse_args()
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
with tempfile.TemporaryDirectory(prefix='pa194-lcghf-')as tmp:
 target=Path(tmp)/'packet';shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 subprocess.run([sys.executable,str(target/'construction/build.py')],check=True)
 checked=[]
 for name in ('PA194LCAX11GHF','PA194LCAX11GHSF'):
  for fn in ('machine.tm','machine.native.tm','raw.native.tm','nodes.json','grammar.tree.json','folds.json','fold_cases.json','sites.json','instructions.json','labels.json'):
   a=ROOT/'machines'/name/fn;b=target/'machines'/name/fn;assert sha(a)==sha(b),(name,fn);checked.append(str(a.relative_to(ROOT)))
 if not args.construction_only:
  results=target/'verification/independent/results';shutil.rmtree(results)
  subprocess.run([sys.executable,str(target/'verification/independent/check.py')],check=True)
  for name in ('PA194LCAX11GHF','PA194LCAX11GHSF'):
   for fn in ('contracts.json','list_lemmas.json','startup.json','receipt.json'):
    a=ROOT/'verification/independent/results'/name/fn;b=results/name/fn
    assert sha(a)==sha(b),(name,fn);checked.append(str(a.relative_to(ROOT)))
 subprocess.run([sys.executable,str(target/'verification/check_clocks.py')],check=True)
 print(json.dumps(dict(status='PASS',frozen_files_compared=len(checked),literal_replayed=not args.construction_only,frozen_outputs_untouched=True,files=checked),indent=2))

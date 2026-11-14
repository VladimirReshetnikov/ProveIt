#!/usr/bin/env python3
"""Run the portable primary checks; this is not a full Lean or search build."""
from pathlib import Path
import json,subprocess,sys,time

ROOT=Path(__file__).resolve().parent
CHECKS=[
 ('comparison','comparison/verify_comparisons.py'),
 ('source_zero_invariant','verification/source_zero_jumps/verify_zero_jumps.py'),
 ('new196_and_rejected195','verification/zero_jump_machine/verify.py'),
 ('composed_jump_contracts','verification/jump_products/replay.py'),
 ('low_level_saved_certificates','verification/low_level_search/verify.py'),
 ('formula_recoding_witnesses','experiments/formula_recoding/check_witnesses.py'),
 ('base8_runtime','experiments/base8_parity/build_b8.py'),
]

def main():
 records=[];started=time.monotonic()
 for name,relative in CHECKS:
  script=ROOT/relative
  began=time.monotonic()
  p=subprocess.run([sys.executable,str(script)],cwd=script.parent,capture_output=True,text=True)
  record=dict(name=name,script=relative,exit_code=p.returncode,
              seconds=time.monotonic()-began,stdout=p.stdout,stderr=p.stderr)
  records.append(record)
  print(name,'PASS'if p.returncode==0 else'FAIL',flush=True)
  if p.returncode:
   print(p.stdout);print(p.stderr,file=sys.stderr);break
 success=len(records)==len(CHECKS)and all(x['exit_code']==0 for x in records)
 out=dict(status='PASS'if success else'FAIL',sub196_machine_certified=False,
          full_lean_build_run=False,large_fold_searches_rerun=False,
          elapsed_seconds=time.monotonic()-started,checks=records)
 (ROOT/'verification_results.json').write_text(json.dumps(out,indent=2)+'\n')
 if not success:raise SystemExit(1)

if __name__=='__main__':main()

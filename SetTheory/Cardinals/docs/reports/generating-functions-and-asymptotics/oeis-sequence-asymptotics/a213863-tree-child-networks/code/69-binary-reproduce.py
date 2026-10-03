#!/usr/bin/env python3
"""Replay exact assertions, with optional uncertified numerical diagnostics."""
from pathlib import Path
import subprocess,sys,time,json,argparse,hashlib
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--numerical',action='store_true');args=ap.parse_args()
commands=[['check_exact_cocycle.py'],['coefficients/derive_coefficients.py','--order','7'],['coefficients/check_natural_field.py'],['verify_total_transfer.py'],['check_inverse.py'],['verification/check_independent.py'],['verification/check_independent_order7.py'],['verification/check_total_transfer.py'],['verification/check_total_transfer_order6.py'],['verification/check_inverse_independent.py'],['verification/check_distribution.py']]
if args.numerical:commands += [['coefficients/check_forward_numerical.py'],['coefficients/check_frozen_numerical.py']]
(root/'logs').mkdir(exist_ok=True)
report=[]
for i,command in enumerate(commands):
 t=time.time();r=subprocess.run([sys.executable,*command],cwd=root,text=True,capture_output=True)
 logfile=f"{i+1:02d}-{Path(command[0]).stem}.log"
 (root/'logs'/logfile).write_text(r.stdout+r.stderr)
 item={'command':command,'exit_code':r.returncode,'seconds':round(time.time()-t,3),'log':'logs/'+logfile}
 report.append(item);print(json.dumps(item),flush=True)
 if r.returncode:
  print(r.stderr);raise SystemExit(r.returncode)
(root/'reproduction-results.json').write_text(json.dumps(report,indent=2)+'\n')
print('All finite algebraic assertions passed. Numerical results, if requested, remain uncertified.')

"""Negative controls against the independent verifier, using temporary copies."""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile
D=Path(__file__).resolve().parent
results=[]
for case in ('optimized','missing_initial','closure_hole','truncated_certificate','changed_table'):
 with tempfile.TemporaryDirectory(prefix='window-negative-')as temp:
  W=Path(temp)
  for name in ('verify.py','inputs.json'):shutil.copy2(D/name,W/name)
  for name in ('inputs','K215','CM215','ST215','COMMON215'):shutil.copytree(D/name,W/name)
  args=[sys.executable]
  if case=='optimized':args.append('-O')
  elif case in ('missing_initial','closure_hole','truncated_certificate'):
   p=W/'K215/r1_a0.bits';raw=bytearray(p.read_bytes())
   if case=='missing_initial':raw[0]&=~1
   elif case=='closure_hole':
    # A live noninitial state/window must have a predecessor in the least set.
    i=next(i for i in range(8,len(raw)*8)if raw[i//8]>>(i%8)&1);raw[i//8]&=~(1<<(i%8))
   else:raw=raw[:-1]
   p.write_bytes(raw)
  elif case=='changed_table':
   p=W/'inputs/K215.native.tm';raw=p.read_bytes();p.write_bytes(raw+b'\n')
  args.append(str(W/'verify.py'));run=subprocess.run(args,text=True,capture_output=True)
  if run.returncode==0:raise RuntimeError('Verifier accepted '+case)
  diagnostic=(run.stderr or run.stdout).strip().splitlines()[-1]
  results.append({'case':case,'returncode':run.returncode,'diagnostic':diagnostic})
report={'status':'ALL_NEGATIVE_CONTROLS_REJECTED','controls':results}
(D/'negative_controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

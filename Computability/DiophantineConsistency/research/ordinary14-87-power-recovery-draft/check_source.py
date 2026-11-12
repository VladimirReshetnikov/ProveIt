from pathlib import Path
import json,subprocess,sys,hashlib
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'PowerRecovery87.lean').read_text()
for t in ('P72ExactIndices87Draft.exact_indices','FirstQuotient87Draft.quotient_and_root','Growth87Draft.growth','projection_quotient aa R','mod_cancel hHp hres','hbeta46 : 46≤beta','P87ShiftedGuard.graph p'):assert t in s
r=D/'research/ordinary14-87-growth-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
count=0
for H in range(1,80):
 for x in range((H+2)//3):
  for y in range((H+2)//3):
   if 3*x<H and 3*y<H and (3*x)%H==(3*y)%H:
    assert x==y
    count+=1
print(json.dumps({'strict_remainder_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'PowerRecovery87.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))

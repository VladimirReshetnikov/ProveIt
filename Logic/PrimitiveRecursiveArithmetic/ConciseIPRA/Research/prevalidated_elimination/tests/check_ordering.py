"""Exact regression and raw-language ordering counterexamples."""
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[1]
old=ROOT/'reference/checkers/checker_bytes.py'
new=ROOT/'code/checker_bytes.py'
zero=0
one=[0]
s1=[0,one,0]
s2=[0,one,one]
major1=[s1,one]
major2=[s2,one]
comp1=[0,0,one,0]
comp2=[0,0,one,one]
outer=[major1,s1,one,[-1,one]]
inner=[major2,s2,one,[3,one]]
goal=[one,one]
cases=[
 dict(name='new_accept_old_reject',packet=[comp1,comp1,outer,goal],old=False,new=True),
 dict(name='old_accept_new_reject',packet=[comp2,comp2,inner,comp1,outer,goal],old=True,new=False),
]
receipt=[]
for case in cases:
 for label,path in [('old',old),('new',new)]:
  for optimized in (False,True):
   run=subprocess.run([sys.executable]+(['-O'] if optimized else[])+[str(path)],input=json.dumps(case['packet']),text=True,capture_output=True,timeout=10)
   verdict=run.returncode==0 and run.stdout=='ACCEPT\n'
   receipt.append(dict(case=case['name'],checker=label,optimized=optimized,expected=case[label],actual=verdict,pass_=verdict==case[label],stderr=run.stderr[-500:] if verdict!=case[label] else''))
output=dict(ordering_cases=cases,runs=len(receipt),failures=[r for r in receipt if not r['pass_']],results=receipt)
(ROOT/'evidence/ordering_receipt.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:v for k,v in output.items() if k not in ('results','ordering_cases')},indent=2))

if output["failures"]: raise SystemExit(1)

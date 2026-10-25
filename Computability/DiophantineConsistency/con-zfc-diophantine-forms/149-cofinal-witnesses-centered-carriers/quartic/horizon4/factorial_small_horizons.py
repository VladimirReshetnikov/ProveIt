"""Complete exact exceptional cases for the rising square-radius fixed point."""
from pathlib import Path
from math import comb,factorial
import json
ROOT=Path(__file__).resolve().parent
rows=[]
for t in (4,5):
 T=factorial(t)
 for F in range(1,T+1):
  V=(F*F+1)**t;B=comb(F*F+t,t)
  rows.append({'t':t,'F':F,'factorial':T,'V':V,'B':B,'upper_gap_F_B_minus_V':F*B-V,'lower_gap_V_minus_Fminus1_B':V-(F-1)*B,'fixed_point':(F-1)*B<V<=F*B})
 # Independent route, not math.comb: multiply t consecutive factors, divide by t!.
 for r in [r for r in rows if r['t']==t]:
  F=r['F'];V=1;prod=1;Tf=1
  for i in range(1,t+1):V*=F*F+1;prod*=F*F+i;Tf*=i
  if prod%Tf:raise ValueError('nonintegral binomial')
  B=prod//Tf
  if B!=r['B'] or V!=r['V'] or Tf!=T:raise ValueError('independent arithmetic mismatch')
  if (F<T and V<=F*B) or (F==T and not (F-1)*B<V<=F*B):raise ValueError('fixed-point classification failed')
report={'status':'PASS','scope':'Complete finite proof for t=4,5, not a sample: the universal bound F<=t! exhausts all potential positive fixed points.','universal_bound':'H=(F^2+1)^t/binom(F^2+t,t)=t!*product_{i=1}^t (F^2+1)/(F^2+i)<=t!; hence ceil(H)<=t! and a fixed point F has F<=t!.','condition':'(F-1)B<V<=FB is exactly F=ceil(V/B), with positive B.','cases':len(rows),'fixed_points':[(r['t'],r['F']) for r in rows if r['fixed_point']],'rows':rows}
(ROOT/'factorial_small_horizons.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'}))

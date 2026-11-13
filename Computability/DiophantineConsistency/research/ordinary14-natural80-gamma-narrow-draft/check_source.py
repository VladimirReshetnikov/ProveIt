#!/usr/bin/env python3
"""Source and finite arithmetic checks; no Lean invocation."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
def read(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b.decode()
s=read(P/'GammaZeroNarrow.lean','f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7')
orient=read(D/'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean','29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd')
first=read(D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
for x in ('theorem first_ordinate_lower','(hcoord : 2*ycoord n (2*(P-1)+1) = k)',
          'theorem gamma_zero_impossible','(hgap : R+1 < k) (hcX : X < eta+Y*k)',
          'direct_main_orientation U X Y k eta (0:V) R hU hY hk hnorm',
          '#print axioms DiophantineConsistency.GammaZeroNarrowDraft.first_ordinate_lower',
          '#print axioms DiophantineConsistency.GammaZeroNarrowDraft.gamma_zero_impossible'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
assert 'theorem direct_main_orientation (U X Y k eta G R : V)' in orient
assert '(hU : 0<U) (hY : 8≤Y) (hk : 0<k)' in orient
assert 'theorem positive_parameter_solution' in first
# Check the target square-gap and the recurrence's first two ordinates in
# concrete small instances; these do not establish the model propositions.
count=0
for a in range(0,30):
 for c in range(1,30):
  delta=(a+1)*(a+3)
  assert 1+delta*c*c>((a+1)*c)**2
  count+=1
for p in range(1,100):
 B=2*(p-1)+1
 y0,x0=0,1
 y1=x0+(B+2)*y0;x1=(B+2)*x0+(B+1)*(B+3)*y0
 y2=x1+(B+2)*y1
 assert 2*y2==8*p+4
print(json.dumps({'scope':'unelaborated source and finite controls only; no model or iPRA theorem',
                  'explicit_main_norm_and_gap_hypotheses':True,
                  'no_positive_gamma_premise':True,'square_gap_controls':count,
                  'recurrence_controls':99,'axiom_print_commands_not_executed':2},sort_keys=True,indent=2))

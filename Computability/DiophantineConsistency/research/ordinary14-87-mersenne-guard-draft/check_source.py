from pathlib import Path
import json
p=Path(__file__).resolve().parent
s=(p/'MersenneGuard87.lean').read_text()
for x in ['hX : v 6=Exp.exp R','h3 : q beta v∣3*v 6','mersenne_divides_X','Arithmetic.le_of_dvd','strict_of_large_X']:
 assert x in s
checked=0
for t in range(4,9):
 for J in range(1,16):
  q=(2**t-1)*J+1
  for R in range(1,35):
   X=2**R
   if 3*X%q==0:
    assert X%q==0 and q<=X
    checked+=1
assert checked>0
print(json.dumps({'finite_mersenne_controls':checked,'lean_run':False},sort_keys=True,indent=2))

from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent;s=(p/'ParentFourFields.lean').read_text()
for t in ('P88FourSquare.output_shape','fiveSquares_eq_zero_iff','fiveSquares,eval,mul_zero,add_zero','P88FourSquare.graph p'):assert t in s
for a in range(-3,4):
 for b in range(-3,4):
  for c in range(-3,4):
   for d in range(-3,4):
    assert (a*a+b*b+c*c+d*d==0)==(a==b==c==d==0)
print(json.dumps({'four_square_controls':2401,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentFourFields.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))

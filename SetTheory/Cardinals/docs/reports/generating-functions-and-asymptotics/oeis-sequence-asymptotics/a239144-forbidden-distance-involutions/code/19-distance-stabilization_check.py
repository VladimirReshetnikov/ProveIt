# Exact affine-statistic tests immediately above the proven threshold.
import ast,json
from fractions import Fraction as Q
from pathlib import Path
from collections import defaultdict
root=Path(__file__).resolve().parent;src=ast.parse((root/'verify.py').read_text());node=next(x for x in src.body if isinstance(x,ast.FunctionDef) and x.name=='counts');ns={'defaultdict':defaultdict};exec(compile(ast.Module(body=[node],type_ignores=[]),'counts','exec'),ns)
def coeff(n,r,j):
 M=ns['counts'](n,r);c=[Q(0)]
 for h in range(1,j+1):c.append(Q((h*M[h] if h<len(M) else 0)-sum(k*c[k]*(M[h-k] if h-k<len(M) else 0) for k in range(1,h)),h))
 return (-1)**(j+1)*c[j]
import os
out=Path(os.environ.get("OUTPUT_DIR",root.parent/"results")).resolve()
out.mkdir(parents=True, exist_ok=True)
rows=[]
for r in range(1,6):
 for j in range(1,5):
  n=j*r+1;values=[coeff(n+d,r,j) for d in range(5)];alpha=values[1]-values[0];beta=values[0]-alpha*n
  assert all(values[d]==alpha*(n+d)+beta for d in range(5))
  rows.append({'r':r,'j':j,'minimum_tested_n':n,'alpha':str(alpha),'beta':str(beta)})
(out/"stabilization-checks.json").write_text(json.dumps(rows,indent=2));print('Passed 100 exact values across 20 fixed-r,j affine families')

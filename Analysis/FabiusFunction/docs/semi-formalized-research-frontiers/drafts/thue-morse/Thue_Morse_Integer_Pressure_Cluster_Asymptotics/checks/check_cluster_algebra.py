"""Independent exact Lagrange-polynomial regressions with the standard library."""
# ed. (2026-10-01): results are written to <output-dir>/<name>, by default
# rerun/ beside this program, with LF line endings (as delivered the program
# overwrote its recorded result, with CRLF on Windows). Pass --output-dir
# with the recorded file's directory, on a copy, to regenerate the recorded file.
def _ed_write(name, text):
    import argparse
    from pathlib import Path as _EdPath
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output-dir', type=_EdPath,
                        default=_EdPath(__file__).resolve().parent / 'rerun')
    out = parser.parse_known_args()[0].output_dir
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_bytes(text.encode('utf-8'))

from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

def require(c,msg):
 if not c:raise ArithmeticError(msg)
rows=[]
for k in range(1,13):
 zero=(0,)*k;positive={zero:1};signed={zero:1}
 for step in range(k):
  nxt={};neg={}
  for mon,c in positive.items():
   weight=sum(j*mon[j]for j in range(k))
   for j in range(k-weight):
    m=list(mon);m[j]+=1;m=tuple(m);nxt[m]=nxt.get(m,0)+c
  for mon,c in signed.items():
   weight=sum(j*mon[j]for j in range(k))
   for j in range(k-weight):
    m=list(mon);m[j]+=1;m=tuple(m);neg[m]=neg.get(m,0)+(-1)**j*c
  positive=nxt;signed=neg
 C={mon:F((-1)**(k-1-sum(j*mon[j]for j in range(k)))*c,k)for mon,c in signed.items()}
 expected={mon:F((-1)**(k-1)*c,k)for mon,c in positive.items()}
 require(C==expected,'two Lagrange forms differ')
 require(all(sum(mon)==k and sum(j*mon[j]for j in range(k))<=k-1 for mon in C),'degree convention')
 require(all((-1)**(k-1)*c>0 for c in C.values()),'polynomial sign')
 leading=F(0)
 for mon,c in C.items():
  if sum(j*mon[j]for j in range(k))==k-1:
   denom=1
   for j,v in enumerate(mon):denom*=factorial(j)**v
   leading+=c/denom
 target=F((-1)**(k-1)*k**(k-1),factorial(k))
 require(leading==target,'rooted-tree constant')
 if k==2:require(C=={(2,0):F(-1,2),(1,1):F(-1)},'quadratic regression')
 if k==3:require(C=={(3,0,0):F(1,3),(2,1,0):F(1),(2,0,1):F(1),(1,2,0):F(1)},'cubic regression')
 rows.append(dict(k=k,monomials=len(C),before_parity=str(leading),after_parity=str(2*leading)))
 print(k,len(C),2*leading)
out=dict(all_exact_checks_pass=True,finite_regressions_only=True,general_identity_proved_in_article=True,rows=rows)
# ed. (2026-10-01): written by _ed_write (see above).
_ed_write('cluster_algebra_stdlib.json', json.dumps(out,indent=2)+'\n')

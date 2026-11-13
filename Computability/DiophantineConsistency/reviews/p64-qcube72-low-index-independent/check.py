#!/usr/bin/env python3
"""Independent finite controls; universal proof is documented separately."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];TASK=ROOT/'Computability/DiophantineConsistency';P=TASK/'research/p64-qcube72-low-index-analysis'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ycoord(index,b):
 x,y=1,0; a=b+2; d=(b+1)*(b+3)
 for _ in range(index):x,y=a*x+d*y,x+a*y
 return y
cases=0; eligible=0; witness=[]
for q in range(5,13):
 for s in (1,2):
  Y=q**3*s
  for w in range(1,41):
   X=q*w;P0=X*Y*Y;a=(X+1)*Y;B=2*P0-1
   assert a<=B
   for n in range(1,4):
    k=2*ycoord(n,B)
    for m in range(1,5):
     c=ycoord(m,a);eta=c-k*Y
     if 0<eta<k:
      eligible+=1;witness.append((q,s,w,n,m));assert n<m and m>=4
     cases+=1
print(json.dumps({'status':'PASS_FINITE_CONTROLS','tuples':cases,'eligible':eligible,'scope':'Bounded standard q-cube cases only; no Lean, no replacement for universal proof.','packet_readme_sha256':sha(P/'README.md'),'packet_check_sha256':sha(P/'check.py'),'review_script_sha256':sha(__file__)},sort_keys=True))

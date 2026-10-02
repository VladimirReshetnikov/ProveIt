from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
(ROOT / "results").mkdir(exist_ok=True)
import json
N=30
J=N+3
old={(0,2):1}
sp={}
for n in range(1,N+3):
 se={}
 nw={}
 for i in range(n+1):
  for j in range(J+1):
   se[i,j]=old.get((i-1,j+1),0)
 for i in range(n,-1,-1):
  for j in range(J+1):
   nw[i,j]=se.get((i+2,j-2),0)+nw.get((i+2,j-2),0)+nw.get((i+2,j),0)+nw.get((i,j-2),0)
   d=(1,3) if j%2 else (3,1)
   nw[i,j]+=se.get((i+d[0],j-d[1]),0)+nw.get((i+d[0],j-d[1]),0)
 old={k:se.get(k,0)+nw.get(k,0) for k in set(se)|set(nw)}
 sp[n-2]=se.get((2,0),0)
svals=[0,0,3,2]+[sp[n]+2*sp[n-1]+sp[n-2] for n in range(4,N+1)]
ts=[0]*(N+1)
for n in range(2,N+1):
 ts[n]=svals[n]-(3 if n==2 else 1 if n==3 else 0)-sum(c*ts[n-i] for i,c in [(1,3),(2,3),(3,1)] if n>=i)
print('s prime',sp)
print('s',svals[:15]);print('tilde',ts[:15])
assert all(sp[n] == ts[n] + ts[n-1] + (-1)**n for n in range(2,N+1))
json.dump({'sprime':sp,'s':svals,'stilde':ts},open(ROOT / "results" / "schnyder-enumeration.json",'w'),indent=2)

terms=[]
for line in (ROOT / "sources" / "A377920.seq").read_text().splitlines():
 if line.startswith(("%S ","%T ","%U ")):
  terms.extend(int(v) for v in line.split(" ",2)[2].strip().split(",") if v)
assert svals == terms[:N+1]
print("PASS: all A377920 coefficients n=0..30 and exact rigid-series relation")

#!/usr/bin/env python3
"""Independent 88-to-parent fresh-root ring cuts; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-88-parent-ring-client-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'Ring88ToParent.lean','ed123945de04affa263fd5f7cd84053ca362516b5d809b0e9f1d54f676c20534').decode()
pin(A/'check_source.py','f56334a883bde8988c9317446c458137ef4a38c055266cf9f59cb8c434619a57')
receipt=pin(A/'observation.json','6c1b5022105a2de6bdc9b3691591331f0a296cb9feddb82138a4d1eed1f046fe')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-88-parent-ring-client-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='e9c258bf5a49057619c3d917d66c764aebe419c0ef14f6c34a082612ca973e6c'
for f in ('Function.update (fun j : Fin 13 => v j.castSucc) 8 r',
 'theorem main_eval','theorem aux_eval','theorem strong_eval','theorem first_eval',
 '(hY : Y=q3*s) (hr : r+(ell+k+s)=k*(b*t)+t+tau)',
 '(q3*b)*(ell+k+r-k*(b*t))+Y*b-q3*(b*t)=(q3*b)*tau'):
 assert f in s,f
old=json.loads((D/'research/ordinary14-guarded-fold88-26/candidate.json').read_bytes())
parent=json.loads((D/'research/ordinary13-four-square88-30/candidate.json').read_bytes())
def shape(g,field):
 rows={r[0]:r[1:] for r in g['source']};seen={};stack=[field]
 while stack:
  x=stack.pop()
  if x not in rows or x in seen:continue
  op,a,b=rows[x];seen[x]=(op,a,b);stack.extend(z for z in (a,b) if isinstance(z,str))
 return seen
for f in ('A1','Fa','g72'):assert shape(old,f)==shape(parent,f)
assert old['witnesses'][:13]==parent['witnesses']
# Exact substitution in Z[q3,b,ell,k,t,s,tau].
def plus(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {k:v for k,v in c.items() if v}
q,b,ell,k,t,s0,tau=({tuple(int(i==j) for i in range(7)):1} for j in range(7))
root=plus(plus(plus(mul(k,mul(b,t)),t),tau),neg(plus(plus(ell,k),s0)))
Z=plus(plus(mul(mul(q,b),plus(plus(plus(ell,k),root),neg(mul(k,mul(b,t))))),mul(mul(q,s0),b)),neg(mul(q,mul(b,t))))
assert Z==mul(mul(q,b),tau)
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'88-to-parent ring field and fresh-root source review; no Lean','matching_nonfirst_fields':3},sort_keys=True,indent=2))

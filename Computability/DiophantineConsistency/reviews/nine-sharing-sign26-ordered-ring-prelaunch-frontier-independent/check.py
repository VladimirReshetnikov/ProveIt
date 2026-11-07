#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-ordered-ring-check';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9924fd13a40b8db3b127b486692cd7ac0e8ad421ad6fcd902c73dbd36d7f1e00','input-pins.json':'ec3c6f1852cd404f80e5676f80160d4d158a57708be23be2696d2c8a836076ba','src/Sign26OrderedRing.lean':'5f00ccfb2c2f23664ca46cebff1a6e0ca861541bb1f6c7fc524eda32cdc0d390'}.items():assert H(P/n)==h
s=(P/'src/Sign26OrderedRing.lean').read_text();assert H(D/'research/nine-sharing-sign26-ordered-ring-draft/Sign26OrderedRing.lean')==H(P/'src/Sign26OrderedRing.lean')
for x in ['[CommRing R] [LinearOrder R] [IsStrictOrderedRing R]','(ha : 1 ≤ a) (hH : 1 ≤ H) (hn : 1 ≤ n) (ht : 1 ≤ t) (hz : 0 ≤ z)','(hNt : H * (a + 1 - n - t) = n + z * a)','0 ≤ a * (a + 1) + t - a * n','mul_pos_iff_of_pos_left hHpos','theorem congruence','theorem gap_nonneg']:assert x in s
# Exact coefficient arithmetic for the independently transcribed congruence in Z[a,n,t,Q].
def add(x,y):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+v
 return {k:v for k,v in z.items() if v}
def neg(x):return {k:-v for k,v in x.items()}
def sub(x,y):return add(x,neg(y))
def mul(x,y):
 z={}
 for a,u in x.items():
  for b,v in y.items():
   k=tuple(c+d for c,d in zip(a,b));z[k]=z.get(k,0)+u*v
 return {k:v for k,v in z.items() if v}
zero=(0,0,0,0);one={zero:1};a,n,t,Q=[{tuple(int(i==j) for i in range(4)):1} for j in range(4)];q=add(a,one);q2=mul(q,q);q3=mul(q2,q);gap=sub(add(mul(a,q),t),mul(a,n));replacement=add(mul(sub(a,n),Q),mul(add(n,t),q2));assert sub(mul(gap,q2),replacement)==neg(mul(sub(a,n),sub(Q,q3)))
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);j=json.loads(r.stdout);assert not r.stderr and j['status']=='PASS_NO_LEAN_PREFLIGHT' and j['guard_slots']==60
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'generic exact congruence and conditional ordered-ring gap sign only; model hypotheses and representation not discharged; no Lean replay'},sort_keys=True,indent=2))

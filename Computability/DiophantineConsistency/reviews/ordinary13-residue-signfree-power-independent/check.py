#!/usr/bin/env python3
"""Independent sign-free power source and ring certificate audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src','1c6935eda3ce9ae05d257957d7e2d8f5f3786386aaf618d5a480036113c8bb92')
pin('research/ordinary13-residue-signfree-power-model-draft/receipt.json','5cfb6b56d55c9615bc29e58a8730d379b3f4e71b39f3338f8f533d4278f8a922')
pin('reviews/ordinary13-residue-three-projection-independent/result.json','3abf4f8c568e7afc54a435da385db53e32f571d10139e99757bd32c42d3eb597')
p=pin('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390')
for x in ['theorem sixteen_of_three_projection','(hq : 46≤q) (hX : 0<X) (hdvd : q∣3*X)','theorem growth_of_coordinates','(hn : 13≤n) (hR : 2*n=R+1)','(hc : c=ycoord R (Y*(X+1)))','(hfirst : k=2*ycoord n','theorem power_of_oriented_balance','(hx : xcoord R (Y*(X+1))=main)','(hy : ycoord R (Y*(X+1))=c)','(hYq : ∃ s : V, Y=q*(q*q)*s)','projection_quotient a R','mod_cancel hHp hres','mul_left_cancel₀']:
 assert x in s,x
assert 'theorem power_bound' in p and 'theorem projection_quotient' in p and 'Bez' not in s
# Verify proposed 3-times balance algebra in the free integer polynomial ring.
def v(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for t,c in b.items():d[t]=d.get(t,0)+k*c
 return {t:c for t,c in d.items() if c}
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,vv in b.items():
   t=tuple(sorted(x+y));d[t]=d.get(t,0)+u*vv
 return {t:c for t,c in d.items() if c}
def prod(*xs):
 o={():1}
 for x in xs:o=mul(o,x)
 return o
three={():3};H,q,d,main,W,X,a,c,gamma=map(v,['H','q','d','main','W','X','a','c','gamma'])
M=add(main,prod(H,W));Z=add(add(X,prod(a,c)),prod(H,gamma))
bal=add(add(prod(q,M),prod(q,Z),-1),prod(H,X),-1)
hH=add(add(H,three,-1),prod(q,d),-1)
target=add(add(prod(three,add(X,prod(a,c))),prod(H,add(M,prod(three,gamma)))),add(prod(three,main),prod(H,add(add(add(add(prod(three,W),X),prod(a,c)),prod(H,gamma)),prod(d,X)))),-1)
assert target==add(prod(d,bal),prod(add(M,Z,-1),hH))
for q0 in range(46,130):
 for X0 in range(1,30):
  if 3*X0%q0==0:assert X0>=16
assert 3*15%45==0
for n in range(13,100):
 r=n-1;R=2*n-1
 assert r>=2 and R==2*r+1
print(json.dumps({'scope':'conditional sign-free power source, exact ring certificate and finite controls; no Lean','q_divides_three_X_not_q_divides_X':True,'exact_both_Pell_coordinates_explicit':True,'stronger_oriented_q_balance_explicit':True,'three_balance_certificate_correct':True,'graph_witnesses_and_port_bound_open':True,'lean_elaborated':False},sort_keys=True,indent=2))

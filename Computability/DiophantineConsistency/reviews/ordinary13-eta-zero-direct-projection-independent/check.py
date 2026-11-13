#!/usr/bin/env python3
"""Independent source-interface and finite arithmetic review; no Lean."""
from pathlib import Path
import hashlib,json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src':'0984da9ba2037fd39b8898d2cf6e91cfb0f453161dd7fda8cdf139bacda7b222',
'research/ordinary13-eta-zero-direct-projection-model-draft/README.md':'151e06a6406dacb8f37414a165e943059a176da6d64b3a5d18ddd663e9b0b2a6',
'research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src':'7cb45a1766cedf64f1ad6f1a11977ec66990a9c7977f41a9e100a6d36742845e',
'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json':'97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648',
'Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean':'913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956',
'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'}
s={}
for p,h in pins.items():
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p]=b.decode()
d=s['research/ordinary13-eta-zero-direct-projection-model-draft/EtaZeroDirectProjection.lean.src']
for t in ['(hq : 0<q) (hs : 0<s) (hY : Y=q^3*s)',
 '(hindex : k=R+1+4*(X*Y*Y)*w)',
 'U*main+H*k=U*(X+a*c)+H*(U*gamma+R+1)',
 '(hbound : Exp.exp R<Y)',
 '(hx : xcoord R (Y*(X+1))=main)',
 '(hy : ycoord R (Y*(X+1))=c)',
 'DirectMainProjection.direct_projection U X a c H gamma R W main (Exp.exp R) t',
 'projection_quotient a R']:
 assert t in d,t
x=s['Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean']
assert '''theorem direct_projection (U X a c H G R W main P t : V)
    (hU : 0<U) (hH : 0<H) (hX : X<H) (hP : P<H)
    (hroot : U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main)
    (hproj : main=P+a*c+H*t) : X=P''' in x
x=s['Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean']
assert '''theorem projection_quotient (a t : V) :
    ∃ z : V, xcoord t a=Exp.exp t+a*ycoord t a+(4*a+3)*z''' in x
assert 'induction t using ISigma1.sigma1_succ_induction' in x[x.index('theorem projection_quotient'):x.index('theorem power_of_coordinates')]
g=json.loads(s['research/ordinary13-eta-zero-graph-adapter-audit/prototype.json']);rng=random.Random(940214)
for _ in range(250):
 v={n:rng.randrange(0,5) for n in g['witnesses']+g['fixed_numerals']}
 for name,op,l,r in g['source']:
  a=l if isinstance(l,int) else v[l];b=r if isinstance(r,int) else v[r]
  v[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 assert v['Dstar']==v['U']*(v['X']+v['a']*v['c'])+v['H']*(v['U']*v['n_gamma']+v['R']+1-v['k'])
for _ in range(300):
 q=rng.randrange(1,8);s0=rng.randrange(1,7);X=rng.randrange(0,10);Y=q**3*s0
 R,c,gamma,main,w=[rng.randrange(0,10) for j in range(5)]
 a=X*Y+Y;H=3+4*a;U=Y*q*q;W=4*X*q*s0*w;k=R+1+4*X*Y*Y*w
 assert 4*X*Y*Y*w==U*W
 defect=U*main+H*k-(U*(X+a*c)+H*(U*gamma+R+1))
 assert defect==U*(main+H*W-(X+a*c+H*gamma))
 if 2**R<Y:assert 0<U and 0<H and X<H and 2**R<H
pell=0
for a in range(0,9):
 x,y=1,0
 for R in range(0,15):
  z,r=divmod(x-2**R-a*y,4*a+3)
  assert r==0 and z>=0
  x,y=(a+2)*x+(a+1)*(a+3)*y,x+(a+2)*y
  pell+=1
print(json.dumps({'source_sha256':pins,'prototype_carrier_controls':250,'balance_and_bounds_controls':300,'pell_projection_controls':pell,'lean_executed':False,'scope':'source interface and finite arithmetic checks only; no all-model theorem, graph-zero extraction, provider build, or iPRA endpoint'},sort_keys=True,indent=2))

#!/usr/bin/env python3
"""Finite rank, divisibility and graph controls for a boxed-port symbolic zero."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
raw=(D/'research/ordinary13-folded-root86-negated/candidate.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166'
g=json.loads(raw);rows={r[0]:r for r in g['source']}
for n,row in {'qF':['qF','-','q','F'],'C':['C','-','qF','alpha'],'G':['G','+','alpha','g44'],'Bt':['Bt','-','g27','g28'],'R':['R','+','g47','g50'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert rows[n]==row
beta,K,MC,MF,J,F,alpha=31,9,13,55,1,1,45
q=1+J*beta;G=beta*(q-F)+alpha;R=G*(q*q-1)+J*(MC+q*MF);N=(R-1)//2
assert 0<MC<beta<MF<2*beta and G==1006 and R==1030911 and R%4==3
assert N.bit_count()-1==15
xm=pow(2,R,beta);assert xm==2
assert ((q-F-alpha)*(xm+K*q)-F*q)%beta==0
assert q*(q-1)-G==-14
# Every positive scalar pair with this G has C≤−14, tested here on
# finite assignments in addition to the general algebra in the README.
for fp in range(1,100):
 ap=G-beta*(q-fp)
 assert ap>0 and q-fp-ap==q*(q-fp)-G<=-14
print(json.dumps({'toy_ports':{'beta':beta,'K0':K,'MC':MC,'MF':MF},'q':q,'G':G,'R':R,'Y_two_adic_valuation':15,'X_mod_beta':xm,'finite_scalar_controls':99,'scope':'symbolic boxed-port signed-candidate full zero; no actual-port zero, Lean, or unrestricted existential nonequivalence'},sort_keys=True,indent=2))

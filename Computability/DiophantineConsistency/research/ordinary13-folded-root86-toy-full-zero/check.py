#!/usr/bin/env python3
"""Finite controls for a symbolic 88-graph toy-port zero; no Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
p=D/'research/ordinary13-four-square88-30/candidate.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'
g=json.loads(raw);rows=g['source'];e={r[0]:r for r in rows}
for name,row in {'Bt':['Bt','-','g27','g28'],'M':['M','*','q3','qm'],'Z':['Z','-','g34','folded_q3Bt'],'shift':['shift','-','g56','r0'],'Dstar':['Dstar','+','g58','g59'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert e[name]==row
assert [r[0] for r in rows if 'r' in r[2:]]==['g31']
beta,K,MC,MF=31,9,14,46;q=beta+1;J,F,alpha=1,1,14;C=q-F-alpha;gap=beta*(q-F)+alpha
R=gap*(q*q-1)+(MC+q*MF)*J;N=(R-1)//2
assert beta>=31 and K>0 and 0<MC<beta<MF<2*beta and C==17 and R==998911 and R%4==3 and R.bit_count()==17
assert N.bit_count()-1==15==3*5 and N>=3 and R>=20
wm=pow(2,(R-5)%5,beta);assert wm==2 and ((K+wm)*C-F)%beta==0
# For X>=2^20 and q=32: X³/(2q³)>68X>34(X+9).
assert (1<<40)>136*q**3 and 1<<20>9
print(json.dumps({'parent_sha256':hashlib.sha256(raw).hexdigest(),'toy_ports':{'beta':beta,'K0':K,'MC':MC,'MF':MF},'q':q,'C':C,'R':R,'R_popcount':R.bit_count(),'Y_two_adic_valuation':N.bit_count()-1,'w_mod_beta':wm,'s_exceeds_Bt_over_beta_bound':True,'scope':'symbolic toy-port 88 zero; no actual-port zero, Lean, or unrestricted existential nonequivalence'},sort_keys=True,indent=2))

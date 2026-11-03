#!/usr/bin/env python3
"""Finite arbitrary-port probe; explicitly not an equation counterexample."""
from pathlib import Path
from hashlib import sha256
import json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;G=H.parent/'trace74-mask-coordinate-probe/candidate.json'
raw=G.read_bytes();assert sha256(raw).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
d=json.loads(raw)
v={'J':1,'F':1,'C':1,'i':1,'T':1,'w':7,'s':1,'n':1,'eta':1187,'zeta':5985,'beta':1,'K0':0,'MC':0,'MF':0}
assert all(v[x]>0 for x in d['witnesses']) and all(v[x]>=0 for x in d['fixed_numerals'])
for name,op,a,b in d['source']:
 a=a if type(a) is int else v[a];b=b if type(b) is int else v[b]
 v[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
q=v['q'];X=v['X'];Y=v['Y'];k=v['k'];c=v['c'];P=X*Y*Y
assert (q,X,Y,P,k,c,v['R'])==(2,14,8,896,7172,58563,3)
alpha=q-v['F']-v['C'];assert alpha==0 and v['F']+v['C']==q
# First Pell index 2: base A1=2P+1, psi_2=2*A1.
tau=2*(2*P+1)**2-1
assert 2*(2*(2*P+1))==k and tau*tau==v['Dtau']==1+P*(P+1)*k*k
# Main Pell index 3: base A=XY+Y+1, psi_3=4*A²-1.
assert c==4*(X*Y+Y+1)**2-1 and 0<v['eta']<k
assert v['N']!=0
assert not (0<v['MC']<v['beta'])
print(json.dumps({'status':'PASS','graph_sha256':sha256(raw).hexdigest(),'ports':{x:v[x] for x in d['fixed_numerals']},'q':q,'X':X,'Y':Y,'P':P,'k':k,'eta':v['eta'],'zeta':v['zeta'],'c':c,'rank':v['R'],'old_alpha':alpha,'first_index':2,'first_tau':tau,'main_index':3,'trial_i_T_n':[1,1,1],'graph_output_nonzero':True,'graph_output_sha256':sha256(str(v['N']).encode()).hexdigest(),'scope':'arbitrary-port partial-constraint probe; NOT a graph zero or fixed-port counterexample'},sort_keys=True))

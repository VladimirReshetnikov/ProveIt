#!/usr/bin/env python3
"""Finite checks for a symbolic full zero at explicit toy ports; no Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source'];assert rows[34]==['En','*','E','n'] and rows[35]==['tau_partial','+','En','k']
new=[]
for row in rows:
 if row[0]=='En':continue
 if row[0]=='tau_partial':row=['tau_partial','+','n','k']
 new.append(row)
def live(rs):
 e={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in e and x not in seen:seen.add(x);todo.extend(e[x])
 return len(seen)
assert len(rows)==65 and live(rows)==65 and len(new)==64 and live(new)==64 and len(g['witnesses'])==14
beta,K,MC,MF=31,29,30,33;q=beta+1;J,F,alpha=1,30,1;C=q-F-alpha;gap=beta*(q-F)+alpha
R=gap*(q*q-1)+(MC+q*MF)*J;h,t=65280,256
assert 0<MC<beta<MF<2*beta and beta>=31 and K>0 and C==1 and gap==63 and R==65535 and R%4==3
X=1<<R;Y=1<<t;E=X*Y
assert X%q==0 and Y%(q**3)==0 and R+1<E
assert (R-1)*(R+t+1)-1-(h-1)*(R+2*t+2)-t==0
assert (R-1)*Y*Y>h-1 and 4*Y*(R-1)<X
assert (R-(2*h-1))%E==E-65024
# w=2^(R-5), and q-1 has order five for 2.
wmod=pow(2,R-5,beta);assert wmod==1 and (K+wmod+1)%beta==0
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'original_live':live(rows),'candidate_live':live(new),'toy_ports':{'beta':beta,'K':K,'MC':MC,'MF':MF},'R':R,'h':h,'Y_exponent':t,'rank_gap':gap,'En_residue_signed':R-(2*h-1),'w_mod_beta':wmod,'dominant_exponent_identity':True,'scope':'symbolic toy-port zero; no actual-port, Lean or existential-nonequivalence claim'},sort_keys=True,indent=2))

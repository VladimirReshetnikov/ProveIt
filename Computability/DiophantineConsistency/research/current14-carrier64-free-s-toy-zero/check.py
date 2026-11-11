#!/usr/bin/env python3
"""Finite scalar and gate checks for a symbolic toy-port zero; no Lean."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source'];assert rows[51]==['normalized_S','*','i','Dc2'] and rows[52]==['normalized_S2','*','normalized_S','normalized_S']
new=[]
for r in rows:
 if r[0]=='normalized_S':continue
 new.append([r[0],r[1],*['i' if x=='normalized_S' else x for x in r[2:]]])
def live(rs):
 e={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in e and x not in seen:seen.add(x);todo.extend(e[x])
 return len(seen)
assert len(rows)==65 and live(rows)==65 and len(new)==64 and live(new)==64 and len(g['witnesses'])==14
beta,K,MC,MF=31,9,14,46;q=beta+1;J,F,alpha=1,1,14;C=q-F-alpha;gap=beta*(q-F)+alpha
R=gap*(q*q-1)+(MC+q*MF)*J;N=(R-1)//2
assert beta>=31 and K>0 and 0<MC<beta<MF<2*beta and C==17 and gap==975
assert R==998911 and R%4==3 and R.bit_count()==17 and N.bit_count()-1==15
exponent=(R-5)%5;wmod=pow(2,exponent,beta)
assert exponent==1 and wmod==2 and ((K+wmod)*C-F)%beta==0
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'original_live':live(rows),'candidate_live':live(new),'toy_ports':{'beta':beta,'K':K,'MC':MC,'MF':MF},'R':R,'rank_gap':gap,'C':C,'R_popcount':R.bit_count(),'Y_two_adic_valuation':N.bit_count()-1,'w_mod_beta':wmod,'scope':'symbolic toy-port zero; no current-port, Lean or unrestricted existential-nonequivalence claim'},sort_keys=True,indent=2))

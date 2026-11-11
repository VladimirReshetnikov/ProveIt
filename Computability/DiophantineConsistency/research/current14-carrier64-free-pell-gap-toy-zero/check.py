#!/usr/bin/env python3
"""Source and fixed toy scalars for a symbolic free-Pell-gap zero."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source']
assert rows[53:58]==[['V2','*','V','V'],['y2','*','y','y'],['V2minusY2','-','V2','y2'],['aux_product','*','normalized_S2','V2minusY2'],['Na','+','aux_product','y2']]
new=[]
for r in rows:
 if r[0] in ('y2','V2minusY2'):continue
 if r[0]=='aux_product':new.append(['S2minus1','-','normalized_S2',1]);r=['aux_product','*','S2minus1','y']
 if r[0]=='Na':r=['Na','-','V2','aux_product']
 new.append(r)
def live(rs):
 e={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in e and x not in seen:seen.add(x);todo.extend(e[x])
 return len(seen)
assert len(rows)==65 and live(rows)==65 and len(new)==64 and live(new)==64 and len(g['witnesses'])==14
beta,K,MC,MF=31,9,14,46;q=beta+1;F,alpha=1,14;C=q-F-alpha;gap=beta*(q-F)+alpha;R=gap*(q*q-1)+MC+q*MF
assert beta>=31 and K>0 and 0<MC<beta<MF<2*beta and C==17 and R==998911 and R%4==3
assert ((R-1)//2).bit_count()-1==15
wmod=pow(2,(R-5)%5,beta);assert ((K+wmod)*C-F)%beta==0
# Illustrative finite CRT controls: A=4, c=63, an even-index strong Pell unit.
A,c=4,63;Delta=A*A-1
D0,L0=244,63;f,L=1,0
# c-th power makes c²|L, and the additional square makes its index even.
for _ in range(2*c):f,L=D0*f+Delta*L0*L,L0*f+D0*L
assert L%(c*c)==0 and f*f-Delta*L*L==1
S=Delta*L; assert __import__('math').gcd(A,f)==1
assert __import__('math').gcd(S*S-1,c*f*f)==1
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'original_live':live(rows),'candidate_live':live(new),'toy_ports':{'beta':beta,'K':K,'MC':MC,'MF':MF},'R':R,'Y_two_adic_valuation':15,'small_even_unit_control':True,'scope':'symbolic toy-port zero; no actual-port, Lean or unrestricted existential-nonequivalence claim'},sort_keys=True,indent=2))

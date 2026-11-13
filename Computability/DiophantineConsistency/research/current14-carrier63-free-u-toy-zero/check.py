#!/usr/bin/env python3
"""Graph/scalars and exact small modular control for the free-U obstruction."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];p=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);rows=g['source']
assert rows[47:50]==[['cT','*','c','T'],['cTminusR','-','cT','R'],['f2inner','*','f2','cTminusR']]
new=[]
for row in rows:
 if row[0] in ('cT','cTminusR'):continue
 if row[0]=='f2inner':row=['f2inner','*','f2','T']
 new.append(row)
def live(rs):
 e={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in e and x not in seen:seen.add(x);todo.extend(e[x])
 return len(seen)
assert len(rows)==65 and live(rows)==65 and len(new)==63 and live(new)==63 and len(g['witnesses'])==14
beta,K,MC,MF=31,9,14,46;q=beta+1;F,alpha=1,14;C=q-F-alpha;gap=beta*(q-F)+alpha;R=gap*(q*q-1)+MC+q*MF
assert 0<MC<beta<MF<2*beta and C==17 and R==998911 and R%4==3
assert ((R-1)//2).bit_count()-1==15
assert ((K+pow(2,(R-5)%5,beta))*C-F)%beta==0
# Independent small exact modular control of the anti-period construction.
A,r,D0,c=4,3,244,63;delta=A*A-1
f,L=1,0
for _ in range(c):f,L=D0*f+delta*c*L,c*f+D0*L
assert f*f-delta*L*L==1 and L%(c*c)==0 and f%D0==0
j0=f//D0;m=r*c;t=2*m*j0-r;assert j0%2==1 and t%4==3
S=delta*L;mod=f*f*c;x=(4*S*S-2)%mod;Q1=(4*S*S-3)%mod;j=(t-1)//2
def mul(a,b):return ((a[0]*b[0]+a[1]*b[2])%mod,(a[0]*b[1]+a[1]*b[3])%mod,(a[2]*b[0]+a[3]*b[2])%mod,(a[2]*b[1]+a[3]*b[3])%mod)
power=(x,mod-1,1,0);acc=(1,0,0,1);n=j-1
while n:
 if n&1:acc=mul(acc,power)
 power=mul(power,power);n//=2
V=(acc[0]*Q1+acc[1])%mod
assert V%(f*f)==(-c)%(f*f) and V%c==r and (V+r)%c!=0
print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'original_live':live(rows),'candidate_live':live(new),'toy_ports':{'beta':beta,'K':K,'MC':MC,'MF':MF},'R':R,'small_A':A,'small_r':r,'small_c':c,'small_f_bits':f.bit_length(),'small_aux_index_bits':t.bit_length(),'small_modular_control':True,'scope':'symbolic toy-port zero; no current-port, Lean or unrestricted existential-nonequivalence claim'},sort_keys=True,indent=2))

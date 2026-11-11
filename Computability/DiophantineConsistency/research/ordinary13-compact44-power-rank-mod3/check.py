#!/usr/bin/env python3
"""Authenticated compact44 ports and literal rank modulo 3; no Lean."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def readpin(path, digest):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==digest;return b
raw=readpin(D/'research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
rows={r[0]:r for r in json.loads(raw)['source']}
for n,row in {'qm':['qm','*','J','beta'],'q':['q','+',1,'qm'],'qF':['qF','-','q','F'],'g44':['g44','*','qF','qm'],'G':['G','+','alpha','g44'],'g46':['g46','-','q2',1],'g47':['g47','*','G','g46'],'g48':['g48','*','MF','q'],'g49':['g49','+','MC','g48'],'g50':['g50','*','J','g49'],'R':['R','+','g47','g50']}.items():assert rows[n]==row
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'; b=json.loads(readpin(p/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(readpin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
v={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(p/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];v[n]=int.from_bytes(x,'little')
assert v['beta'].bit_length()==590069 and v['beta']==2**590069-1
assert all(v[n]%3==1 for n in ('beta','MC','MF'))
for J in range(3):
 q=(1+J)%3
 for G in range(3):
  rank=(G*(q*q-1)+J*(1+q))%3
  if q in (1,2):assert rank==0
assert ((1+2)%3==0 and (1*(0*0-1)+2*(1+0))%3==1)
# q=0,J=2,G=0 yields R=2 modulo 3, showing the restricted scope.
assert (0*(0*0-1)+2*(1+0))%3==2
print(json.dumps({'beta_bit_length':590069,'beta_mod3':1,'MC_mod3':1,'MF_mod3':1,'power_of_two_q_rank_mod3':0,'q_zero_control_rank_mod3':2,'scope':'external compact44 arithmetic; power-of-two q only; no Lean or zero-existence conclusion'},sort_keys=True,indent=2))

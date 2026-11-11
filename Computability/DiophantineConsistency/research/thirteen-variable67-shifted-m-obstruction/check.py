#!/usr/bin/env python3
"""Finite fixed-port checks for a symbolic 67-gate obstruction; no Lean."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2];src=D/'research/thirteen-variable-independent/polynomial69.json';data=src.read_bytes()
assert hashlib.sha256(data).hexdigest()=='3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f'
g=json.loads(data);rows=g['source'];base=(src.parent/g['coefficient_binding']['path']).resolve();p={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(base/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'];p[name]=int.from_bytes(raw,'big')
def live(rs):
 edges={r[0]:r[2:] for r in rs};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in edges and x not in seen:seen.add(x);todo.extend(edges[x])
 return len(seen)
assert rows[53]==['LB','*','V2','B'] and rows[54]==['mLB','-','m','LB'] and rows[55]==['h_mLB','*','qm','mLB']
new=[]
for row in rows:
 if row[0] in ('LB','mLB'):continue
 if row[0]=='h_mLB':row=['h_mLB','*','qm','m']
 new.append(row)
assert len(rows)==69 and live(rows)==69 and len(new)==67 and live(new)==67 and len(g['witnesses'])==13
b=p['beta'];q=b+1;B=b.bit_length();assert q==1<<B and B==116137
lo=p['MC'];hi=p['MF']-b;assert 0<lo<b and 0<hi<b
M=lo+q*p['MF'];gap=M+1;R=gap*q*q-1
assert R==gap*(q*q-1)+M and R%4==3 and R>B
N=(R-1)//2;v2Y=N.bit_count()-1;assert v2Y>=3*B
exponent=(R-B)%B;wb=pow(2,exponent,b);mb=(p['K0']+wb)%b
assert math.gcd(mb+1,b)==1
F=(mb*(1-gap)*pow(mb+1,-1,b))%b or b
C=q*(q-F)-gap;alpha=q-F-C
assert 0<F<=b and C<0 and alpha>0
assert b*(q-F)+alpha==gap and (mb*C-F)%b==0
# t=4*k*ord-R can be arbitrarily large, positive and 1 mod 4.
assert all((4*k*o-R)%4==1 for o in range(1,8) for k in range(1,8))
print(json.dumps({'source_sha256':hashlib.sha256(data).hexdigest(),'original_live':live(rows),'shifted_live':live(new),'beta_exponent':B,'rank_bitcount':R.bit_count(),'Y_two_adic_valuation':v2Y,'w_mod_beta_exponent':exponent,'F_bits':F.bit_length(),'F_sha256':hashlib.sha256(F.to_bytes((F.bit_length()+7)//8,'big')).hexdigest(),'C_negative':C<0,'alpha_positive':alpha>0,'negative_transport_divisible_by_beta':(mb*C-F)%b==0,'scope':'finite checks on symbolic construction; no Lean or full literal witness evaluation'},sort_keys=True,indent=2))

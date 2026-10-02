"""Compare recomputed check records and assert the advertised numerical tests.
This validates computations, not a formal proof or interval arithmetic.
"""
from pathlib import Path
import argparse, json, re
import mpmath as mp
mp.mp.dps=110
p=argparse.ArgumentParser();p.add_argument('expected',type=Path);p.add_argument('actual',type=Path);a=p.parse_args()
count=0

def number(s):
 s=s.strip()
 if s.startswith('(') and s.endswith(')') and 'j' in s:
  s=s[1:-1]
  # mpmath's str(mpc) format separates the real and imaginary parts with spaces.
  bits=s.split()
  if len(bits)==3 and bits[1] in ['+','-']:
   return mp.mpc(mp.mpf(bits[0]),mp.mpf(bits[2][:-1])*(1 if bits[1]=='+' else -1))
 return mp.mpf(s)

def compare(x,y,path):
 global count
 if isinstance(x,dict):
  assert isinstance(y,dict) and set(x)==set(y),(path,'key mismatch')
  for k in x:compare(x[k],y[k],path+'/'+str(k))
 elif isinstance(x,list):
  assert isinstance(y,list) and len(x)==len(y),(path,'length mismatch')
  for i,(u,v) in enumerate(zip(x,y)):compare(u,v,path+'/'+str(i))
 elif isinstance(x,(int,bool)):
  assert x==y,(path,x,y);count+=1
 elif isinstance(x,str):
  assert isinstance(y,str),(path,'type mismatch')
  if re.fullmatch(r'[+-]?\d+',x):
   assert x==y,(path,'exact integer mismatch')
  else:
   u,v=number(x),number(y)
   assert mp.isfinite(abs(v)),(path,'nonfinite')
   assert abs(u-v)<=mp.mpf('1e-40')*(1+abs(u)),(path,x,y)
  count+=1
 else:
  assert x==y,(path,x,y);count+=1

names=['exact','mellin','coefficient','inverse','reciprocity']
for name in names:
 f=name+'-checks.json'
 compare(json.loads((a.expected/f).read_text()),json.loads((a.actual/f).read_text()),f)
exact=json.loads((a.actual/'exact-checks.json').read_text())
assert all(v['all_equal'] and v['through']==400 for v in exact.values())
counts=json.loads((a.actual/'coefficient-checks.json').read_text())
inverse=json.loads((a.actual/'inverse-checks.json').read_text())
for b in ['4','8']:
 row=next(r for r in counts[b]['checks'] if r['n']==10000)
 assert abs(mp.mpf(row['relative_errors_orders_0_to_4'][4]))<mp.mpf('1e-9')
 inv=next(r for r in inverse[b] if r['n']==10000)
 assert abs(mp.mpf(inv['inverse_index_errors_orders_0_to_4'][4]))<mp.mpf('1e-6')
reciprocity=json.loads((a.actual/'reciprocity-checks.json').read_text())
assert max(abs(mp.mpf(r['identity_error'])) for r in reciprocity)<mp.mpf('1e-80')
print(f'PASS: {count} recorded values agree; exact, count, inverse and reciprocity checks pass')

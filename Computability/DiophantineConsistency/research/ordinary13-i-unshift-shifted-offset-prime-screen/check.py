#!/usr/bin/env python3
"""Exact finite prime screen; symbolic derivation appears in README."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
prev=root/'research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
data=json.loads(r.stdout)
p=data['prime']; R=data['rank_J1_mod_p']; assert (p,R)==(193707721,55801659)
# Compare both sides of the completing-square identity on integer controls.
for h in range(31):
 for L in range(h, h+3*(h+1)+1):
  num=(L-h)*(2*L-h+1)
  if num%(h+1): continue
  n=num//(h+1); rank=2*n-1
  assert (4*L+1-3*h)**2==(h+1)*(h+5+4*rank)
rows=[]
for h in range(1,31):
 if h%9 in (0,2,3,5,6): continue
 discr=((h+1)*(h+5+4*R))%p
 criterion=pow(discr,(p-1)//2,p)
 assert criterion in (0,1,p-1)
 rows.append({'h':h,'reduced_discriminant':discr,
              'euler':criterion,'status':'obstructed' if criterion==p-1 else 'passes_necessary_test'})
assert [r['h'] for r in rows if r['status']=='obstructed']==[1,7,10,16,19,26,28]
assert [r['h'] for r in rows if r['status']=='passes_necessary_test']==[4,8,13,17,22,25]
assert rows[0]['reduced_discriminant']==(8*R+12)%p
print(json.dumps({'p':p,'R_mod_p':R,'range':'1 <= h <= 30, excluding classes already eliminated mod 3',
 'reduced_discriminant':'(h+1)*(h+5+4*R) mod p','results':rows,
 'scope':'fixed compact ports, J=1, q=2^(67*8807), R=2*n-1',
 'passing_means_zero_exists':False,'graph_zero_nonexistence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))

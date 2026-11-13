#!/usr/bin/env python3
"""Check graph wires and small controls for the signed auxiliary Pell condition."""
import hashlib,json,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
prev=root/'research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
g=json.loads((root/'research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text())
rows={x[0]:x[1:] for x in g['source']}
expected={'kbase':['+','n_eta','n_zeta'],'k':['+','kbase',1], 'c':['+','n_eta','kY'],
 'i':['+','n_i',1],'T':['+','n_T',1], 'f2':['*','n_f','n_f'],
 'rho':['-','f2',1], 'Q':['*','Delta','rho'], 'I':['*','c2','i'],
 'g71':['*','I','I'],'g72':['-','g71','Q'],
 'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],
 'V':['-','g76','c'],'y2':['*','n_y','n_y'], 'V2':['*','V','V'],
 'g81':['-','y2','V2'],'g82':['*','Q','g81'],'Fa':['-','y2','g82'],
 'F0':['+',1,'A0'],'F1':['+',1,'A1'],'Fs':['+',1,'g72'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],
 'P0123':['*','P012','Fs'],'out':['-','P0123',1]}
for k,v in expected.items():assert rows[k]==v,(k,rows[k])
# Exhaust all residue classes relevant to the strong unit-factor argument.
strong=[]
for f in range(8):
 for I in range(8):
  fs=(1+I*I-3*(f*f-1))%8
  if fs in (1,7):
   strong.append((f,I,fs))
   assert fs==1
   assert (f%2==1 and I%4==0) or (f%4==2 and I%2==1)
# Check the independent mod-4 exclusions without assuming either norm.
for d in range(4):
 for z in range(4):
  for beta in (1,3):
   for ell in (0,4):
    for k in range(4):
     F1=(1+d*d)%4
     F0=(1+z*z-beta*beta*(1+ell*(ell+k)))%4
     assert F1!=3 and F0!=3
# Finite strong-Pell constructions with y divisible by c^2; each modular
# orbit returns by invertibility. Actual numbers stay small for these controls.
controls=0; cutoff=0
for a in range(1,5):
 D=(a+2)**2-1
 for c in range(2,7):
  mod=c*c; x,y=1,0; states=set(); n=0
  while True:
   assert (x,y) not in states
   states.add((x,y));x,y=((a+2)*x+D*y)%mod,(x+(a+2)*y)%mod;n+=1
   if (x,y)==(1,0):break
  X,Y=1,0
  for _ in range(n):X,Y=(a+2)*X+D*Y,X+(a+2)*Y
  assert Y%mod==0 and Y>0 and X*X-D*Y*Y==1
  # Set i = D*Y/c^2: then c^2*i = D*Y and D*(f^2-1)=I^2.
  i=D*Y//mod; assert i>0 and X*X>c+1
  actual_I=mod*i
  assert D*(X*X-1)==actual_I*actual_I
  z,v=1,0
  for m in range(1,7):
   z,v=actual_I*z+(actual_I*actual_I-1)*v,z+actual_I*v
   assert z*z-(actual_I*actual_I-1)*v*v==1
   assert (z%actual_I==0)==(m%2==1)
   if m%2:
    V=z//actual_I
    assert (actual_I*actual_I-1)*v*v-actual_I*actual_I*V*V==-1
    cutoff+=1
  controls+=1
print(json.dumps({'graph_wires_checked':len(expected),'strong_mod8_unit_cases':len(strong),
 'positive_strong_pell_period_controls':controls,'auxiliary_pell_controls':cutoff,
 'all_factor_units_positive_under_q_power_of_two':True,'auxiliary_y_at_least_2':True,
 'auxiliary_odd_index_congruence':'conditional on chosen strong Pell solution',
 'fixed_port_full_zero_proved':False,'fixed_port_full_zero_excluded':False,
 'Lean_executed':False},indent=2,sort_keys=True))

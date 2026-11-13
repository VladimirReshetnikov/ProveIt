#!/usr/bin/env python3
"""Finite controls for saturated rank gap and current mask prerequisites."""
import gzip
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
pins={'research/current14-carrier64-pell-floor/result.json':'8edbf8c5b59d4ba77d2bea5beb54f380bef1b7c1ddb3df8ef98e79c009b8181a',
      'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json':'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'}
for name,digest in pins.items():
    if hashlib.sha256((D/name).read_bytes()).hexdigest()!=digest:raise RuntimeError('pin mismatch')
source=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
g=json.loads(source.read_bytes());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
    packed=(source.parent/'coefficients'/meta['file']).read_bytes()
    if hashlib.sha256(packed).hexdigest()!=meta['gzip_sha256']:raise RuntimeError('gzip mismatch')
    raw=gzip.decompress(packed)
    if hashlib.sha256(raw).hexdigest()!=meta['raw_sha256']:raise RuntimeError('raw mismatch')
    ports[name]=int.from_bytes(raw,'big')
beta,lo,mf,K=ports['beta'],ports['MC'],ports['MF'],ports['K0'];hi=mf-beta
B=beta.bit_length()
if not (beta==(1<<B)-1 and 0<lo<beta and 0<hi<beta and lo%4==2 and hi%8==4 and
        lo.bit_count()+hi.bit_count()==B and lo+hi>beta):
    raise RuntimeError('current mask hypotheses failed')

cases=saturated=below=0
for width in range(3,8):
 base=1<<width;bb=base-1
 for low in range(2,bb,4):
  for high in range(4,bb,8):
   if low.bit_count()+high.bit_count()!=width or low+high<=bb:continue
   for h in range(1,3):
    t=width*h
    if t>7:continue
    q=1<<t;b=q-1;J=b//bb;A=low*J;Z=high*J
    if not (A.bit_count()+Z.bit_count()==t and A%4==2 and Z%8==4 and A+Z>b):
        raise RuntimeError('mask expansion failed')
    g0=q*(Z-1)+A+1
    if g0.bit_count()!=t+2:raise RuntimeError('base-population failed')
    for G in range(4*q-1,q*q-q):
     R=G*(q*q-1)+A+q*(b+Z)
     if G<g0 and R.bit_count()>=3*t+2:below+=1
     if R.bit_count()>=3*t+2:
        saturated+=1;d=G-g0
        if d<0 or d&g0 or R.bit_count()!=3*t+2:
            raise RuntimeError('saturation/no-carry failed')
        u,r=divmod(G,b)
        if not (2<=u<=b and 1<=r<u):raise RuntimeError('old scalar guard failed')
     cases+=1
if not saturated or below:raise RuntimeError('insufficient/contrary finite controls')

# The strict actual mask-sum hypothesis matters: this smaller port example
# saturates population while its old Euclidean scalar guard fails.
qtoy=32;btoy=31;lotoy=14;hitoy=12;Gtoy=367
Rtoy=Gtoy*(qtoy*qtoy-1)+lotoy+qtoy*(btoy+hitoy)
utoy,rtoy=divmod(Gtoy,btoy)
if not (lotoy%4==2 and hitoy%8==4 and lotoy.bit_count()+hitoy.bit_count()==5 and
        lotoy+hitoy<btoy and Rtoy.bit_count()==3*5+2 and rtoy>=utoy):
    raise RuntimeError('strict mask-sum negative control failed')

# Actual-port obstruction to a blanket transport coprimality argument.
if not (beta%10==1 and lo%10==8 and mf%10==1 and K%11==0 and
        B%20==17 and pow(2,10,11)==1 and pow(2,5,11)==10):
    raise RuntimeError('eleven-divisor premises failed')
for h in (20,40,60):
    t=B*h;q10=pow(2,t,10);J10=(q10-1)%10
    if not (t%20==0 and q10==6 and J10==5 and pow(2,t,11)==1 and
            all(((q10*q10-1)*G+J10*(lo%10+q10*(mf%10)))%10==5 for G in (1,3,5,7,9)) and
            (K%11+pow(2,5,11)+1)%11==0):
        raise RuntimeError('eleven-divisor branch control failed')

actual=[]
for h in (1,2):
 t=B*h;q=1<<t;b=q-1;J=b//beta;A=lo*J;Z=hi*J;G0=q*(Z-1)+A+1
 R=G0*(q*q-1)+A+q*(b+Z)
 u,r=divmod(G0,b)
 if not (A%4==2 and Z%8==4 and A+Z>b and A.bit_count()+Z.bit_count()==t and
         G0.bit_count()==t+2 and R.bit_count()==3*t+2 and 2<=u<=b and 1<=r<u):
    raise RuntimeError('actual repeated-mask base control failed')
 actual.append({'h':h,'mask_populations_match':True,'rank_saturated':True,'old_scalar_guard':True})
result={'pins':pins,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'actual_beta_exponent':B,'actual_low_high_sum_exceeds_beta':True,
        'bounded_cases':cases,'bounded_saturated':saturated,'saturated_below_base':below,
        'mask_sum_negative_control':{'q':qtoy,'MC':lotoy,'MF_native':hitoy,'G':Gtoy},
        'actual_modular_data':{'beta_mod_10':1,'MC_mod_10':8,'MF_mod_10':1,'K_mod_11':0,
                               'if_20_divides_t_then_11_divides_both':True},
        'actual_base_controls':actual,'scope':'external combinatorial proof controls; transport repair and full equivalence open'}
print(json.dumps(result,sort_keys=True,indent=2))

"""Read-only independent audit of the proposed entire coefficient tuple.

This script does not import the proposed builder. It checks the retained
bytes and the arithmetic hypotheses needed by the signed-domain proof.
It does not replace the semantic compiler/padding proofs.
"""
import gzip
import hashlib
import json
import math
from pathlib import Path

def require(condition, message):
    if not condition:
        raise ValueError(message)

ROOT=Path(__file__).resolve().parents[1]
folder=ROOT/'coefficients'
manifest=json.loads((folder/'COEFFICIENT_BINDING.json').read_text())
values={}
for record in manifest['files']:
    compressed=(folder/record['file']).read_bytes()
    raw=gzip.decompress(compressed)
    require(hashlib.sha256(compressed).hexdigest()==record['gzip_sha256'], 'independent coefficient audit failed at original line 20')
    require(hashlib.sha256(raw).hexdigest()==record['sha256'], 'independent coefficient audit failed at original line 21')
    require(len(raw)==record['bytes'] and raw[-1]!=0, 'independent coefficient audit failed at original line 22')
    values[record['port']]=int.from_bytes(raw,'little')
    require(values[record['port']].bit_length()==record['bits'], 'independent coefficient audit failed at original line 24')

d=6364399;ell=452453;b=529;length=12031
require(b*length==d==23**2*53*227, 'independent coefficient audit failed at original line 27')
require(all(ell%j for j in range(2,math.isqrt(ell)+1)), 'independent coefficient audit failed at original line 28')
B=values['beta']+1
require(B==1<<d, 'independent coefficient audit failed at original line 30')
DC=values['K0'] & (B-1)
DR=values['K0'] >> d
require(DR==1<<(b*5497), 'independent coefficient audit failed at original line 33')
MC=values['MC'];MF=values['MF']-values['beta']
require(0<MC<B-1 and 0<MF<B-1, 'independent coefficient audit failed at original line 35')
require(MC%4==2 and MF%8==4, 'independent coefficient audit failed at original line 36')
require(MC.bit_count()+MF.bit_count()==d and MF.bit_count()==989, 'independent coefficient audit failed at original line 37')
moduli=[23,53,227,ell]
rows=[]
for p in moduli:
    br=B%p;dcr=DC%p;drr=DR%p
    factor=(br*br-1)%p
    H0=(1+br*dcr+br*br*(drr+1))%p
    require(factor and H0, 'independent coefficient audit failed at original line 44')
    rows.append(dict(prime=p,B=br,DC=dcr,DR=drr,qfactor=factor,H0=H0))
step=ell-1
require(step==452452 and step%64636==0, 'independent coefficient audit failed at original line 47')
require(pow(2,d*step,d)==1, 'independent coefficient audit failed at original line 48')
require(pow(2,d*step,ell*ell)==155849698116, 'independent coefficient audit failed at original line 49')
require(155849698116%ell==1 and 155849698116!=1, 'independent coefficient audit failed at original line 50')
# Both orders have certified minimality by testing each prime factor.
for modulus,order,prime_factors in [(d,64636,[2,11,13,113]),(ell,452452,[2,7,11,13,113])]:
    require(pow(2,d*order,modulus)==1, 'independent coefficient audit failed at original line 53')
    require(all(pow(2,d*(order//p),modulus)!=1 for p in prime_factors), 'independent coefficient audit failed at original line 54')
require(math.gcd(d,ell)==1, 'independent coefficient audit failed at original line 55')
receipt={'status':'PASS','read_only':True,'imports_builder':False,
 'complete_tuple_sha256s_match':True,'d':d,'raw_total_bytes':sum(x['bytes']for x in manifest['files']),
 'padding_prime':ell,'order_mod_d':64636,'order_mod_ell':452452,
 'valuation_e':1,'native_mask_population':d,'native_high_population':989,
 'materialized_unit_residues':rows,
 'scope':'Exact byte and modular arithmetic audit; ordinary compiler and padding proofs remain required.'}
out=ROOT/'evidence/independent_materialized_coefficient_audit.json'
out.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

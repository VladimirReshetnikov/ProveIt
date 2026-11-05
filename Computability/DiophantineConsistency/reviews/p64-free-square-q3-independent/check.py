#!/usr/bin/env python3
"""Independently verify the q=3 partial norm example by binary powering."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent
source=here.parents[1]/'research/p64-free-square-q3-obstruction/check.py'
record=source.with_name('result.json')
if hashlib.sha256(source.read_bytes()).hexdigest()!='d5abfe97f4a1716bde015d03d41366024e28057239dc4dab12d6a2ec2dc41e6a': raise RuntimeError('author source drift')
if hashlib.sha256(record.read_bytes()).hexdigest()!='a4c258b0884732c708936ddd3220fd8348334493b769ad6820c0a7eaf4f40a0b': raise RuntimeError('author result drift')
original=json.loads(record.read_text())
D=12099
# Binary powering in Z[sqrt(D)], independent of the author's 12,099-step loop.
def mul(a,b):
    x,y=a; u,v=b
    out=(x*u+D*y*v,x*v+y*u)
    if max(n.bit_length() for n in out)>200000: raise RuntimeError('operand limit')
    return out
power=(1,0); base=(110,1); n=D
while n:
    if n&1: power=mul(power,base)
    n//=2
    if n: base=mul(base,base)
g,c=power
if c.bit_length()!=original['c_bits'] or c%27!=original['c_mod_27'] or g*g!=1+D*c*c:
    raise RuntimeError('Pell mismatch')
if c**4%D: raise RuntimeError('nonintegral h')
h=1+c**4//D
if h.bit_length()!=original['h_bits'] or h%7!=original['h_mod_7'] or D*(h-1)!=c**4:
    raise RuntimeError('strong norm mismatch')
floor=math.isqrt(h)
if not floor*floor<h<(floor+1)*(floor+1): raise RuntimeError('h is square')
q=3; beta=2; J=F=alpha=w=s=z=1; K0=2; Y=q**3*s; X=w*q
a=Y*(X+1); eta=15; k=(c-eta)//Y; zeta=k-eta
if min(k,zeta,q-F-alpha)<=0 or q!=beta*J+1 or c!=k*Y+eta or D!=a*a+4*a+3 or (K0+w)*(q-F-alpha)-F-z*(q-1)!=0:
    raise RuntimeError('coordinate or transport mismatch')
raw=h.to_bytes((h.bit_length()+7)//8,'big')
result={'status':'PASS_PARTIAL_INDEPENDENT','method':'binary powering plus integer square root',
        'c_bits':c.bit_length(),'h_bits':h.bit_length(),'h_mod_7':h%7,
        'h_unsigned_big_endian_sha256':hashlib.sha256(raw).hexdigest(),
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope':'Partial coordinates, transport and two norms only; no M, first norm, auxiliary unit or full graph zero.'}
out=here/'result.json'; payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]: raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload: raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))

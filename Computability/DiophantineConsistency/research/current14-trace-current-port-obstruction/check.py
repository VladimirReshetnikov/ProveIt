#!/usr/bin/env python3
"""Pin current β and check the symbolic-prime construction on a toy q."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2];path=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';raw=path.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
g=json.loads(raw);meta=g['coefficient_binding']['ports']['beta'];z=(path.parent/'coefficients'/meta['file']).read_bytes()
assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];b=gzip.decompress(z);assert hashlib.sha256(b).hexdigest()==meta['raw_sha256'];beta=int.from_bytes(b,'big')
B=beta.bit_length();q=beta+1
assert B==94517 and B%2==1 and q==1<<B and (q+1)%3==0
assert q**3*(q-2)//3>B+1
# Exact toy instance of the same construction; the actual prime is symbolic.
qt=8;Bt=3;Dt=4*qt**3*(qt+1)//3;pt=12289
assert (pt-1)%Dt==0 and all(pt%d for d in range(2,math.isqrt(pt)+1)) and pt%8==1
ordt=1;x=2%pt
while x!=1:ordt+=1;x=x*2%pt
kt=math.lcm(2,ordt);h=(pt-1)//Dt;Y=qt**3*h;X=qt;R=Bt+kt;H=4*Y*(X+1)+3
assert H==3*pt and kt%2==0 and kt<=(pt-1)//2 and R%2==1 and R+1<X*Y
assert (1<<R)%H==X and X!=(1<<R)
# Verify the Pell-ordinate congruence by recurrence modulo H.
A=(Y*(X+1)+2)%H;u,v=0,1
for _ in range(R):u,v=v,(2*A*v-u)%H
assert (3*X*u-2*(X*X-1))%H==0
print(json.dumps({'actual_beta_exponent':B,'actual_beta_raw_sha256':meta['raw_sha256'],'actual_q_is_power_two':True,'prime_selection':'p ≡ 1 mod 4q³(q+1)/3; existence by Dirichlet, not numerically constructed','toy_q':qt,'toy_prime':pt,'toy_order':ordt,'toy_R':R,'toy_window':R+1<X*Y,'toy_congruence_checked':True,'scope':'actual-q symbolic local construction; rank and norm equations unproved'},sort_keys=True,indent=2))

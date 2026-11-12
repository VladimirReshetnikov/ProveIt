#!/usr/bin/env python3
"""Finite q=5 scalar/binomial controls for a symbolic direct-X toy zero."""
import hashlib,json
from math import comb
from pathlib import Path
D=Path(__file__).resolve().parents[2]
pins={
 'research/ordinary14-universal-trace-bound/candidate.json':'71073ea15ceeddac9d9bf9324238d03af346b5075eedb78351f29f19079d3862',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'}
for name,sha in pins.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==sha
q=5;beta=4;J=1;F=2;alpha=1;K0=1;MC=2;MF=5;b=J*beta
qF=q-F;C=qF-alpha;G=b*qF+alpha;R=G*(q*q-1)+J*(MC+q*MF)
assert q==b+1 and C==2 and G==13 and R==339
assert beta>0 and K0>=0 and 0<MC<beta and 0<MF<2*beta
assert R>=26 and R%4==3 and R+q**3+q+1<=q**4
N=(R-1)//2;X=2**R
Y=sum(comb(2*N,j)*X**(N-j) for j in range(N+1))//2
assert N==169 and X>144*N and Y%q**3==0 and X%q==3
assert Y>X**N//2 and Y.bit_length()==57291
m=X*Y*Y; U=Y*q*q
assert m%U==0  # This uses q²|Y, not the false claim q²|X.
for ms in range(1,30):
    modulus=2*ms; p=2*ms+1; xx,yy=1,0
    for n in range(1,30):
        xx,yy=(p*xx+(p*p-1)*yy)%modulus,(xx+p*yy)%modulus
        assert yy==n%modulus
digest=hashlib.sha256(Y.to_bytes((Y.bit_length()+7)//8,'little')).hexdigest()
assert digest=='bfc970beead6d20dd6e1b1d0f95025dd1c6d337474f380025c3c0390a0381f3c'
h=1+X//2
assert C*(X+K0)+qF-b*h==1 and all(z>0 for z in (J,F,alpha,h,X,Y))
# The rank residue excludes q|X for any parent at q=5 if its trace replay
# establishes X=2^R: q²−1 is divisible by 4, and MC+q*MF=27=3 mod 4.
assert (q*q-1)%4==0 and (MC+q*MF)%4==3
for Rsmall in range(3,200,4):assert pow(2,Rsmall,q)==3
print(json.dumps({'toy_ports':{'beta':beta,'K0':K0,'MC':MC,'MF':MF},
    'q':q,'R':R,'N':N,'X_mod_q':X%q,'Y_bits':Y.bit_length(),
    'Y_sha256_little_endian':digest,'q_cubed_divides_Y':True,'guard_factor':1,
    'scalar_window_and_box':True,
    'scope':'finite toy controls; unbounded Pell completion and parent-source replay require independent review; no Lean/PDF binding'},sort_keys=True,indent=2))

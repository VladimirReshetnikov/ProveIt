#!/usr/bin/env python3
"""Finite q=10 scalar and modular-binomial checks; no huge Pell evaluation."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
pins={
 'research/ordinary14-universal-trace-bound/candidate.json':'71073ea15ceeddac9d9bf9324238d03af346b5075eedb78351f29f19079d3862',
}
# Pin the actual direct-X graph and the cited natural-arithmetic theorem sources.
pins['Lean/DiophantineConsistency/Compact44/P72Exact.lean']='a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3'
pins['Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean']='636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'
for name,sha in pins.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==sha
beta,K0,MC,MF=3,5,2,2;J,F,alpha=3,1,2;b=beta*J;q=b+1
qF=q-F;C=qF-alpha;G=b*qF+alpha;R=G*(q*q-1)+J*(MC+q*MF)
assert (b,q,qF,C,G,R)==(9,10,9,7,83,8283)
assert beta%2==1 and q%2==0 and q%5==0
assert beta>0 and K0>=0 and 0<MC<beta and 0<MF<2*beta
assert R>=26 and R%4==3 and R+q**3+q+1<=q**4
N=(R-1)//2;X=2**R;assert N==4141 and X>144*N and X%q==8
# Y = (sum_{j=0}^N binom(2N,j)*X^(N-j))/2. The numerator is
# divisible by 2q³ exactly when Y is divisible by q³. Horner evaluation
# uses exact integer binomial updates; Y itself is not materialized.
modulus=2*q**3; residue=0;coefficient=1;x=X%modulus
for j in range(N+1):
    residue=(residue*x+coefficient)%modulus
    if j<N:coefficient=coefficient*(2*N-j)//(j+1)
assert residue==0
Bprime=7*(X+K0)-F;assert Bprime%b==0
h=1+Bprime//b
assert h>0 and C*(X+K0)+qF-b*h==1
print(json.dumps({'toy_ports':{'beta':beta,'K0':K0,'MC':MC,'MF':MF},
    'q':q,'J':J,'F':F,'alpha':alpha,'R':R,'N':N,'X_mod_q':X%q,
    'binomial_numerator_mod_2q_cubed':residue,'q_cubed_divides_Y':True,
    'guard_factor':1,'scalar_window_and_box':True,
    'scope':'finite toy controls; unbounded Pell completion and fixed-q parent exclusion require review; no Lean/PDF binding'},sort_keys=True,indent=2))

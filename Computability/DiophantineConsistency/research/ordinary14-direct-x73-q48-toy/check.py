#!/usr/bin/env python3
"""q=48 scalar, 2-adic and independent exact-binomial modular controls."""
import hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
pins={
 'research/ordinary14-universal-trace-bound/candidate.json':'71073ea15ceeddac9d9bf9324238d03af346b5075eedb78351f29f19079d3862',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'}
for name,sha in pins.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==sha
beta,K0,MC,MF=47,29,6,7;J,F,alpha=1,46,1;b=beta*J;q=b+1
qF=q-F;C=qF-alpha;G=b*qF+alpha;R=G*(q*q-1)+J*(MC+q*MF)
assert (b,q,qF,C,G,R)==(47,48,2,1,95,219127)
assert beta>=46 and beta%2==1 and q%2==0 and q%3==0
assert K0>=0 and 0<MC<beta and 0<MF<2*beta
assert R>=26 and R%4==3 and R+q**3+q+1<=q**4
N=(R-1)//2;X=2**R;assert N==109563 and N.bit_count()==13
assert X>144*N and X%q==32 and X%b==17
Bprime=C*(X+K0)-F;assert Bprime>0 and Bprime%b==0
h=1+Bprime//b;assert C*(X+K0)+qF-b*h==1 and h>0
# Y = S/2, S=sum_{j=0}^N binom(2N,j)*X^(N-j).
# 2 is invertible modulo 27. Compute S modulo 27 by Horner's rule with
# exact binomial coefficients; never materialize the enormously larger Y.
modulus=27;x=X%modulus;residue=0;coefficient=1
for j in range(N+1):
    residue=(residue*x+coefficient)%modulus
    if j<N:coefficient=coefficient*(2*N-j)//(j+1)
assert residue==0 and coefficient.bit_length()==219117
# The reviewed central-binomial valuation gives v2(Y)=popcount(N)-1=12;
# 2^12*27=48^3, and S=0 mod 27 implies Y=0 mod 27.
assert N.bit_count()-1==12 and (2**12)*27==q**3
print(json.dumps({'toy_ports':{'beta':beta,'K0':K0,'MC':MC,'MF':MF},
    'q':q,'J':J,'F':F,'alpha':alpha,'R':R,'N':N,'N_popcount':N.bit_count(),
    'X_mod_q':X%q,'X_mod_beta':X%b,'binomial_numerator_mod_27':residue,
    'central_binomial_bits':coefficient.bit_length(),'guard_factor':1,
    'scalar_window_and_box':True,'beta_at_least_46':True,
    'scope':'finite toy controls; unbounded Pell completion, 2-adic identity and fixed-q parent exclusion require review; no Lean/PDF binding'},sort_keys=True,indent=2))

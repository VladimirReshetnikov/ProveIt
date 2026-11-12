#!/usr/bin/env python3
"""Independent q-cubed quotient source/finite review; no Lean invocation."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-86-quotient-facts-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'QuotientFacts.lean','5e45d7e5e75e6a4a9615a036b27872554f2cdc68af37d6e1ac0617599c86aa74').decode()
pin(A/'check_source.py','4a995d1fc46ba1ca8eaefd5377b71cc1d2cac366eb303547d84ae5e97100537f')
receipt=pin(A/'observation.json','9e2d4a5237316afe4d4d224ccff8397673a983afbfdca7c2cf725d5191c5bb3b')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-86-quotient-facts-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='a9ef9288b42b4424e68e2cd09123f6dfb09ef74c1936bae439c5aaa4e5c86e7a'
for path,h in {
 'ArithmeticAdaptiveFirstDivisibility2011.lean':'b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c',
 'ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',
 'ArithmeticGcdNormalization.lean':'62edfd87c326e7f14a7f14dc11a2076cf203b21c09d9739667f8be3ddbadcd3b',
 'Compact44/P72Root.lean':'066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091',
}.items():pin(D/'Lean/DiophantineConsistency'/path,h)
for f in ('(hb : 0<b) (hY : 0<Y) (hD : 0<D)',
 'let z := (M*P+b*Y,M*r)', 'P72Root.ι_magnitude_sq',
 'scaled_quotient M (magnitude z) D hM hsq',
 'magnitude_mod z Q hQ hQdiv','change (M*P+b*Y)%Q=(M*r)%Q at hmod',
 'refine ⟨q*q+q+1,0,0,1,?_⟩','unit_certificate_cancel hunit hby',
 'exact ⟨s,tau,hspos,hs,htpos,hn⟩'):
 assert f in src,f
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
assert not r.stderr and r.stdout==receipt
cases=positive=negative=0
for b in range(1,6):
 q=1+b;Q=q**3;M=Q*b
 assert math.gcd(b,Q)==1 and 1+b*(q*q+q+1)==Q
 for Y in range(1,3*Q+1):
  for P in range(6):
   for r in range(6):
    z=M*P+b*Y-M*r
    if z==0 or z*z%(M*M):continue
    assert abs(z)%M==0 and Y%Q==0
    tau=abs(z)//M;s=Y//Q;D0=tau*tau
    assert s>0 and tau>0 and Y==Q*s and z*z==M*M*D0
    positive+=z>0;negative+=z<0;cases+=1
assert positive and negative
# With D=0, a zero signed root need not yield a positive tau.
assert (8*0+1*8-8*1)**2==8*8*0
print(json.dumps({'scope':'source and finite signed quotient controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'qualifying_cases':cases,
 'positive_roots':positive,'negative_roots':negative,'zero_D_boundary':True},sort_keys=True,indent=2))

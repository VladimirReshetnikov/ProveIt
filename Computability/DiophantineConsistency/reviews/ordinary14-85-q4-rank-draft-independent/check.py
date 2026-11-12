#!/usr/bin/env python3
"""Independent 85 q⁴ source and finite balances; no Lean invocation."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-q4-rank-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Q4Rank85.lean','40d91f46f65d79aa9c823255f3e92438d5398d8e66ec5c6534da800ac918502f').decode()
pin(A/'check_source.py','0c1d999d73297251cf9324123df4f9fc57a9a29e586c83184046f3091f194b66')
receipt=pin(A/'observation.json','bf8bafb14620d4582cb99a2bd9e61296f646c66ae79e499888c9f5975eb6fb40')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-q4-rank-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='f8ba72ea2be3eab4733903b6b7d19a8f1db5d7adc55f76d2cd5e3883064e0164'
for path,h in {
 'ordinary14-85-main-balance-draft/MainBalance85.lean':'686f10c3ff4d86433d8de75ed4897cda3ab9341824ff70213439eba3dc39d317',
 'ordinary14-shifted-guard87-fact-lemmas-draft/ShiftedGuardFacts.lean':'1d248d6da88193f3eee50135e12464b7e5765ef51f072bd29a32be6709b78f10',
}.items():pin(D/'research'/path,h)
for f in ('(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 '(q beta v)^4∣magnitude (naturalRank beta MC MF v+1,k v)',
 'have hY : qq^3∣yy','have hU : uu=qq^5*v 7',
 'H*(xx*yy*qq+(R+1))+qq^5*(v 7*(xx+aa*cc+H*v 12))',
 'q4_rank_from_balance qq yy xx R kk (v 7*(xx+aa*cc+H*v 12)) (v 7*d)',
 'hq hY hb'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-main-balance-draft-independent','ordinary14-shifted-guard87-fact-lemmas-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=nondiv=below=above=0
for q in range(2,9):
 for X in range(1,7):
  for yslot in range(1,4):
   Y=q**3*yslot;U=Y*q*q;H=3+4*Y*(X+1);g=math.gcd(U,H);step=U//g
   for t in range(4):
    k=X*Y*q+3;R=k-1-X*Y*q+step*t;A0=11;gamma=2;d=A0+H*gamma+(H//g)*t
    assert R>=0 and U*d+H*k==U*A0+H*(U*gamma+X*Y*q+R+1)
    assert abs(R+1-k)%q**4==0
    nondiv+=X%q!=0;below+=R+1<k;above+=R+1>k;cases+=1
assert nondiv and below and above
q=3;X=1;Y=q**3;k=X*Y*q+3;R=2
assert abs(R+1-k)==q**4 and X%q!=0
print(json.dumps({'scope':'source and finite old-carrier controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'balance_cases':cases,
 'X_not_divisible_by_q':nondiv,'rank_below_k':below,'rank_above_k':above,
 'q3_sharp':True},sort_keys=True,indent=2))

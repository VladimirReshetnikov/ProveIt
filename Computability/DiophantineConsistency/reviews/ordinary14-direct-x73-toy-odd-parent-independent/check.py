#!/usr/bin/env python3
"""Independent conditional source-hypothesis review of all-J toy exclusion."""
import hashlib,itertools,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-x73-toy-odd-parent'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
pin(A/'check.py','6c26b1b06a2ef2998d25e4ff13ea30298931c5c814352742f3514032282558e7')
receipt=pin(A/'result.json','1fad4f052b16c434959be5b653d8232140cbb6dfa759730bdf05c6e42c85ede8')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-direct-x73-toy-odd-parent-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='b55c14c0ce9a806fd70da0c47facff1198da25298ab7c392fe44f9d8dc396d00'
rank=pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794').decode()
for f in ('theorem scalar_rank_window (q beta MC MF J F alpha : V)',
 '(hMC : MC<beta) (hMF : MF<2*beta) (hq : q=beta*J+1)',
 '(hgap : F+alpha<q)','+q^3+q+1≤q^4'):
 assert f in rank,f
exact=pin(D/'Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3').decode()
for f in ('theorem indices_ordinary (q X Y k R g c a y0 i\' f T u n s μ m η : V)',
 '(hYq : Y = q * (q * q) * y0)','(hR26 : 26 ≤ R)',
 '(hks : k = 2 * n + 4 * ((X * Y) * Y) * s) (hRμ : R + 1 < μ)',
 '(hnmod : (2 * n) % μ = R + 1)','(hmy : ycoord m a = c)',
 '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1'):
 assert f in exact,f
parent=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_bytes())
rows={name:(op,l,rr) for name,op,l,rr in parent['source']}
assert rows['X']==('*','q','w') and rows['Y']==('*','q3','s')
assert rows['Dstar']==('+','g58','g59')
n=0
for J,s,X in itertools.product(range(1,51),range(1,5),range(1,10)):
 q=4*J+1;H=3+4*q**3*s*(X+1);g=math.gcd(H,q**5)
 assert 3%g==0 and (q**5//g)%q**4==0
 assert q%2==1 and pow(2,2*J+1,q)!=0
 n+=1

def replay(p,expected):
 x=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not x.stderr and x.stdout==expected
replay(A/'check.py',receipt)
for name in ('ordinary14-direct-x73-q5-toy-independent','ordinary14-universal-trace-bound-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'conditional external source-hypothesis review; no Lean or provider replay',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'gcd_and_parity_controls':n},sort_keys=True,indent=2))

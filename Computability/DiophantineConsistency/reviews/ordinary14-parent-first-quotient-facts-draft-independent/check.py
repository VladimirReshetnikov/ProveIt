#!/usr/bin/env python3
"""Independent signed parent quotient facts source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-parent-first-quotient-facts-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ParentQuotientFacts.lean','e7d16c15d24a36ab379c1f462b773782a9c10e41b15c4877d7d9a6e2f945bac7').decode()
pin(A/'check_source.py','8c33d9f77e1e308d82096125369a18258178a3e7960890cdacdc9d712895d3f6')
receipt=pin(A/'observation.json','8e577b5325d8d171c8d688ee0f905036b0c5ab9cc83f93a4453ec95cfbaed5d3')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-parent-first-quotient-facts-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='b9f58b60b9e8a6c1a58c6b152f057d5115d6cae7056ff4a5429f76ef71645e36'
p=D/'reviews/ordinary14-85-86-quotient-facts-draft-independent'
pin(p/'check.py','6aeeeb21574ea3a725d4005aaec53dcf20a8c1395dee814b20aa799e9db633d9')
pin(p/'result.json','bd151a0d0a80540ccb3143d13600716ff859aaee458a228d4336010fed87b0d2')
for f in ('(hb : 0<b) (hY : 0<Y) (hD : 0<D)',
 'let z := (M*(P+r)+b*Y+Bn*(W*Q),Bp*(W*Q))',
 'have hWQ : W*Q=1+b*L','unit_certificate_cancel hunit hby',
 'dvd_magnitude_of_mod hb hbmod.symm',
 'b∣magnitude (Bp,Bn)'):
 assert f in s,f
counts={-1:0,1:0}
for b in range(1,7):
 q=b+1;Q=q**3;M=Q*b
 for k in range(1,6):
  W=1+k*b;L=3+3*b+b*b+k*Q
  assert W*Q==1+b*L
  for ss in range(1,5):
   Y=Q*ss
   for P in range(1,5):
    for r0 in range(1,5):
     for t in range(1,4):
      for sign in (-1,1):
       Bp,Bn=(b*t,0) if sign==1 else (0,b*t)
       plus=M*(P+r0)+b*Y+Bn*W*Q;minus=Bp*W*Q
       Z=plus-minus
       if Z==0:continue
       assert abs(Z)%M==0
       tau=abs(Z)//M;D0=tau*tau
       assert Z*Z==M*M*D0 and D0>0
       assert Y%Q==0 and abs(Bp-Bn)%b==0
       assert (Bp>Bn)==(sign==1);counts[sign]+=1
assert min(counts.values())>0
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'parent signed quotient fact source review; no Lean','positive_Bt_cases':counts[1],
 'negative_Bt_cases':counts[-1],'prior_quotient_review':'pinned, not rerun'},sort_keys=True,indent=2))

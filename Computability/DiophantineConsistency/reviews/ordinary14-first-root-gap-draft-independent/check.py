#!/usr/bin/env python3
"""Independent first-root gap source review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-first-root-gap-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'FirstRootGap.lean','fc27d22f530b14964c0fff12ff7ce0d00fe1656b25a5fc9ad8210b6adfd3df0c').decode()
pin(A/'check_source.py','ec1af8256ddb430b6c6d9585840ef93fcee8825a3816d00e8ca773a436484af3')
receipt=pin(A/'observation.json','b92d9989a0984edb3b3c67af4b6f248fcdbcabeef66853e93bcf245d97464068')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-first-root-gap-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='4284e5deed7599b7b54ddee46cd5d0b335d3cbcc1186092e73aa3148fe3bf84e'
p=D/'reviews/ordinary14-first-main-large-k-draft-independent'
pin(p/'check.py','1515a0f05ac83945725052ec63a519ea74f47e5f6e0b983172cbd24d80fad8b2')
pin(p/'result.json','d8119b4f732bdf2f774f5e9330fffec666f1363fba224192515d8df4f67383e1')
for f in ('(hm : 0<m) (hsm : s≤m) (hk : 8*m+4≤k)',
 '(hn : tau*tau=1+m*(m+1)*k*k)',
 'have hbound : 2*m*k+m≤k*k','mul_le_mul_of_nonneg_left hbound (Arithmetic.zero_le m)',
 'lt_of_mul_self_lt_mul_self₀ (Arithmetic.zero_le _) hsq'):
 assert f in s,f
n=0
for m in range(1,31):
 P=2*m+1;delta=P*P-1;tau,y=1,0
 for index in range(1,6):
  tau,y=P*tau+delta*y,tau+P*y;k=2*y
  if index>=2:
   assert k>=8*m+4 and tau*tau==1+m*(m+1)*k*k
   assert 2*m*k+m<=k*k and (m*k+m)**2<tau*tau
   for s0 in range(m+1):assert m*k+s0<tau;n+=1
rr=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
assert not rr.stderr and rr.stdout==receipt
print(json.dumps({'scope':'first root gap source review; no Lean','finite_pell_cases':n,'prior_large_k_review':'pinned, not rerun'},sort_keys=True,indent=2))

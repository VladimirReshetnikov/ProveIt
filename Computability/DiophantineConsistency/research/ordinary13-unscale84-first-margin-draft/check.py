from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
p=P('research/ordinary13-unscale84-first-margin-draft')
files=[p/'UnscaleFirstMargin.lean.src',P('Lean/DiophantineConsistency/Compact44/P73Converse.lean'),P('Lean/DiophantineConsistency/ModelDifferenceRing.lean'),P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-positive84-to87-unscale-model-audit/README.md')]
s=[f.read_text() for f in files]
for needle in ['theorem margin_of_norm','(hnorm : tau*tau=1+ell*(ell+k)) (hk : 3*s≤k) (hs : s≤ell)',
 'theorem margin_of_first_norm','(hs : s≤m)','(hk : 8*m+4≤k)',
 'theorem qcube_margin','(hq : 1≤q) (hX : 1≤X) (hs : 0<s) (hY : Y=(q*q*q)*s)',
 'ι_lt_ι','ι_le_ι','ι_nonneg','nlinarith']:
 assert needle in s[0],needle
assert 'private theorem tau_gt' in s[1] and '(hk : 3 * s ≤ k) (hs : s ≤ ell)' in s[1]
g=json.loads(s[3]);rows={r[0]:r for r in g['source']}
for row in [['q2','*','q','q'],['q3','*','q','q2'],['Y','*','q3','s'],['E','*','X','Y'],['kY','*','Y','k'],['ell','*','E','kY']]:assert rows[row[0]]==row
# Exact polynomial difference proving the P73 inequality under its hypotheses:
# 1+ell*(ell+k)-(ell+s)^2 = 1+ell*(k-3s)+s*(ell-s).
def add(a,b,sgn=1):
 c=a.copy()
 for k,n in b.items():c[k]=c.get(k,0)+sgn*n
 return {k:n for k,n in c.items() if n}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+i*j
 return {k:n for k,n in c.items() if n}
one={(0,0,0):1};ell={(1,0,0):1};k={(0,1,0):1};s0={(0,0,1):1}
three={(0,0,0):3};left=add(add(one,mul(ell,add(ell,k))),mul(add(ell,s0),add(ell,s0)),-1)
right=add(add(one,mul(ell,add(k,mul(three,s0),-1))),mul(s0,add(ell,s0,-1)))
assert left==right
# Both hypotheses matter for strictness, even with the exact norm.
assert (2**2==1+1*(1+2)) and 2<=1+1 and not 3*1<=2
assert (1**2==1+0*(0+3)) and 1<=0+1 and not 1<=0
# Exact integer Pell-solution controls; bounded checks are not model proofs.
count=0; positive=0
for m in range(21):
 for kk in range(8*m+4,1000):
  n=1+m*(m+1)*kk*kk;t=isqrt(n)
  if t*t==n:
   for ss in range(m+1):assert m*kk+ss<t
   count+=1;positive+=m>0
assert positive>0
q,X,ss=2,1,1;Y=q*q*q*ss;m=X*Y*Y;kk=8*m+4;t=2*(2*m+1)**2-1
assert t*t==1+m*(m+1)*kk*kk and m*kk+ss<t
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'private_P73_statement_shape_pinned':True,'margin_polynomial_identity':True,'missing_hypothesis_boundary_controls':2,'bounded_exact_first_norm_controls':count,'positive_m_controls':positive,'qcube_control':{'q':q,'X':X,'Y':Y,'s':ss,'k':kk,'tau':t},'lean_executed':False,'status':'Unelaborated fact-level draft; no graph-zero extraction, provider closure, target-root map or endpoint.'},sort_keys=True,indent=2))

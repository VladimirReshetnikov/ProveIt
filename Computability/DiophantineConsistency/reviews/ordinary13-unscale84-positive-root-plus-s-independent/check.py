from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-unscale84-positive-root-model-draft')
files=[p/'UnscalePositiveRoot.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-positive81-carrier-data-model-draft/PositiveCarrierData.lean.src'),P('research/ordinary13-unscale84-first-margin-draft/UnscaleFirstMargin.lean.src')]
s=[f.read_text() for f in files]
for n in ['theorem shifted_positive_root','(hP : 0<P) (ht : 0<t) (hPt : P=b*t) (hmarg : ell+s<tau)',
 'let r := k*(P-1)+t+(tau-(ell+s))','ι r+ι s-ι k*ι P','theorem shifted_root_of_source',
 '(hmargin : ∀ tau : V, tau*tau=1+ell*(ell+k) → ell+s<tau)',
 'root_data b ell k rold P z hb hk hz hnorm','theorem shifted_root_of_qcube',
 'qcube_margin q X Y s k tau hq hX hs hY hlarge hnorm\'']:
 assert n in s[0],n
for n in ['theorem root_data','∃ Pn t tau : V, 0<Pn ∧ 0<t ∧ P=ι Pn ∧ Pn=b*t ∧ ell<tau',
 'tau*tau=1+ell*(ell+k)']:assert n in s[4],n
for n in ['theorem qcube_margin','(hq : 1≤q) (hX : 1≤X) (hs : 0<s) (hY : Y=(q*q*q)*s)',
 '(hk : 8*X*Y*Y+4≤k)']:assert n in s[5],n
# Exact ring algebra under the represented P=b*t and delta=tau-ell-s;
# the natural subtraction is only allowed after the stated strict margin.
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
one={(0,)*6:1};b={(1,0,0,0,0,0):1};t={(0,1,0,0,0,0):1};ell={(0,0,1,0,0,0):1};k={(0,0,0,1,0,0):1};s0={(0,0,0,0,1,0):1};tau={(0,0,0,0,0,1):1}
P0=mul(b,t);delta=add(add(tau,ell,-1),s0,-1);r=add(add(mul(k,add(P0,one,-1)),t),delta)
base=add(add(add(add(ell,k),r),s0),mul(k,P0),-1);z=add(mul(b,base),P0,-1)
assert z==mul(b,tau)
# Omitting the shift leaves -b*s; this is a formal identity, not a graph zero.
missing=add(mul(b,add(base,s0,-1)),P0,-1)
assert missing==add(mul(b,tau),mul(b,s0),-1)
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[3].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'plus_s_shift_free_ring_identity':True,'omitting_plus_s_leaves_minus_b_s':True,'same_root_and_margin_interfaces_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated fact-level source review; graph bindings, provider closure and endpoint remain open.'},sort_keys=True,indent=2))

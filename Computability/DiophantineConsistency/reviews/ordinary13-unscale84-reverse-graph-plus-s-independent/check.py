from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-unscale84-reverse-graph-model-draft');u=P('research/ordinary13-positive84-to87-unscale-model-draft')
files=[p/'Unscale84ReverseGraph.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',u/'PositiveUnscale84Graph.lean.src',u/'PositiveUnscale87Graph.lean.src',u/'PositiveUnscale84To87.lean.src',P('research/ordinary13-unscale84-positive-root-model-draft/UnscalePositiveRoot.lean.src'),P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-aux-root87-36/candidate.json'),P('Lean/DiophantineConsistency/Compact44/P72Root.lean')]
s=[f.read_text() for f in files];g84,g87=map(json.loads,s[9:11]);assert len(g84['source'])==84 and len(g87['source'])==87
for g,src in ((g84,s[5]),(g87,s[6])):
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in src,n
assert g84['witnesses'][7]=='s' and g87['witnesses'][7]=='Y' and g84['witnesses'][8]==g87['witnesses'][8]=='r'
assert g84['fixed_numerals']==g87['fixed_numerals']==['beta','K0','MC','MF']
for n in ['def portsInt (p : Fin 4 → ℕ)','def Y (p : Fin 4 → ℕ)','theorem source_root','theorem source_first','theorem target_first',
 'ι r+ι (v 7)-ι (k v)*carrier p v','theorem reverse_root_of_large','shifted_root_of_qcube',
 '(hbeta : 0<(p 0:V)) (hlarge : 8*X v*Y p v*Y p v+4≤k v)','def ReverseInputs (p : Fin 4 → ℕ)',
 'theorem reverse_cut (p : Fin 4 → ℕ) (h : ReverseInputs p) : ReverseRootCut (portsInt p)']:
 assert n in s[0],n
inputs=s[0].split('def ReverseInputs',1)[1].split('theorem reverse_cut',1)[0]
assert '0<(p 0:V)' in inputs and '8*X v*Y p v*Y p v+4≤k v' in inputs
assert '∃ y r : V, 0<y ∧ 0<r' in s[0] and 'ScaledY (portsInt p) (update v y r) (v 7)' in s[0]
assert '(ι b*(ι (X*Y*Y*k)+ι k+ι r+ι s-ι k*P)-P)=ι b*ι tau' in s[8]
assert 'def ReverseRootCut (p : Fin 4 → ℤ)' in s[7] and 'PositiveUnscale84GraphDraft.graph p' in s[7]
# Exact target-scaling identity for q³=h, Y=h*s and fresh r.
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
one={(0,)*7:1};h={(1,0,0,0,0,0,0):1};b={(0,1,0,0,0,0,0):1};ell={(0,0,1,0,0,0,0):1};k={(0,0,0,1,0,0,0):1};r={(0,0,0,0,1,0,0):1};ss={(0,0,0,0,0,1,0):1};B={(0,0,0,0,0,0,1):1}
oldcore=add(add(add(ell,k),r),mul(k,B),-1)
z87=add(add(mul(mul(h,b),oldcore),mul(mul(h,ss),b)),mul(h,B),-1)
shifted=add(mul(b,add(oldcore,ss)),B,-1);assert z87==mul(h,shifted)
rad=add(one,mul(ell,add(ell,k)));old=add(mul(z87,z87),mul(mul(mul(h,b),mul(h,b)),rad),-1)
assert old==mul(mul(h,h),add(mul(shifted,shifted),mul(mul(b,b),rad),-1))
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'plus_s_target_root_and_q6_identity_exact':True,'reverse_inputs_beta_and_large_k_explicit':True,'same_natural_port_tuple_and_fresh_r_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated graph binding; ReverseInputs, provider checks and endpoint remain open.'},sort_keys=True,indent=2))

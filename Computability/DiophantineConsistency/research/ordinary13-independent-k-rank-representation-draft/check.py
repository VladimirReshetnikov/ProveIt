from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-rank-representation-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
u=Path('research/ordinary13-independent-k-unit-norm-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(u/'check.py')])==(u/'receipt.json').read_bytes()
s=(D/'IndependentKRankRepresentation.lean.src').read_text()
for x in ['theorem first_norm_F_lt_q','(hbeta : 0<beta) (hJ : 0<J) (hF : 0<F)',
 'by_cases hc : 0<C','have hrzero : r=0','have hBt_eq : Bt= -B',
 'theorem rank_representation','(hFq : v 1+1≤Residue90GraphNormsDraft.q p v)',
 'Residue90GraphNormsDraft.rank_representation p v hFq',
 'let b := J*beta','let q := 1+b','let G := alpha+(q-F)*b',
 'G*(q*q-1)+J*(MC+MF*q)']:
 assert x in s,x
assert '(hd : 0<d)' not in s and '(hk : 0<k)' not in s
orig=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
for x in ['theorem rank_representation','(hFq : v 1+1≤q p v)','P72Root.ι_tsub hFq','have hq2 : 1≤q p v*q p v']:
 assert x in orig,x
# Reconstruct the exact child expression tree at its actual R row.
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
def node(op,a,b):return (op,a,b)
a={name:('var',i) for i,name in enumerate(g['witnesses'])};a.update({name:('port',i) for i,name in enumerate(g['fixed_numerals'])})
for n,op,l,r in g['source']:
 x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r;a[n]=node(op,x,y)
 if n=='R':break
J=a['n_J'];F=node('+',a['n_F'],1);alpha=node('+',a['n_alpha'],1);beta=a['beta'];MC=a['MC'];MF=a['MF']
b=node('*',J,beta);q=node('+',1,b);G=node('+',alpha,node('*',node('-',q,F),b))
rank=node('+',node('*',G,node('-',node('*',q,q),1)),node('*',J,node('+',MC,node('*',MF,q))))
assert a['R']==rank
pos=nonpos=d0=0
for beta in range(1,8):
 for J in range(1,6):
  q=beta*J+1;b=q-1
  for F in range(1,q+4):
   for alpha in range(0,q+4):
    C=q-F-alpha
    for d in range(0,5):
     Bt=C*d-F
     for r in range(4):
      if (b*r-Bt)**2!=b*b:continue
      assert F<q
      if C>0:pos+=1
      else:
       assert r==0 and Bt==-b and F<=b
       nonpos+=1
       if d==0:d0+=1
print(json.dumps({'child_unit_receipt_reproduced':True,'rank_expr_ordered_graph_tree_exact':True,'old_natural_rank_interface_checked':True,'positive_gap_controls':pos,'nonpositive_gap_controls':nonpos,'zero_d_controls':d0,'lean_executed':False,'model_graph_binding_or_provider_replayed':False},sort_keys=True,indent=2))

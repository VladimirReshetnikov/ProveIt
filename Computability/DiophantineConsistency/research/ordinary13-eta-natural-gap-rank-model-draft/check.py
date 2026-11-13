from pathlib import Path
from hashlib import sha256
import json,random,itertools
p=Path('research/ordinary13-eta-natural-gap-rank-model-draft')
fs=[p/'EtaNaturalGapRank.lean.src',p/'README.md',
Path('research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src'),
Path('research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src'),
Path('research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['theorem first_norm','theorem gap_of_J','theorem gap ','theorem rank_representation',
 'Residue90GraphNormsDraft.rank_representation','theorem compact_rank_window',
 'Residue90CompactPortBoundsDraft.compact_rank_window','have hk1 : 1≤k v',
 'have hr : (0:DiffRing V)≤ι (v 8)','have hsmall :','mul_le_mul_of_nonneg_left']:
 assert x in s[0],x
assert 'by omega' not in s[0]
g=json.loads(s[7]); rows={r[0]:r for r in g['source']}
for row in [['X','*','q','n_w'],['kbase','+','n_eta','n_zeta'],['k','+','kbase',1],
 ['g31','+','g30','n_r'],['Bt','-','g27','F'],['Z','-','g32','Bt']]:assert rows[row[0]]==row
checks=0
for b,m,k,r,F,alpha,K in itertools.product(range(1,5),range(4),range(1,5),range(3),range(1,4),range(1,4),range(3)):
 q=1+b;X=1;C=q-F-alpha
 if C>0:continue
 Bt=C*(X+K)-F;ell=m*k;Z=b*(ell+k+r-k*Bt)-Bt
 assert Bt<0 and Z>b*(ell+k)>=0
 assert (ell+k)**2-(1+m*(m+1)*k*k)==ell*k+k*k-1>=0
 assert Z*Z>b*b*(1+m*(m+1)*k*k)
 checks+=1
assert checks>0
rng=random.Random(8881);graph=rank=0
for t in range(300):
 v={key:rng.randrange(0,5) for key in g['witnesses']+g['fixed_numerals']}
 if t%3==0:v['n_eta']=v['n_zeta']=v['n_r']=0
 e=v.copy()
 for name,op,l,r in g['source']:
  a=l if isinstance(l,int) else e[l];b=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 m=e['X']*e['Y']**2;k=e['k'];Bt=(e['q']-e['F']-e['alpha'])*(e['X']+v['K0'])-e['F']
 assert e['Z']==e['qm']*(m*k+k+v['n_r']-k*Bt)-Bt
 assert e['A0']==e['Z']**2-e['qm']**2*(1+m*(m+1)*k*k)
 graph+=1
 if e['q']>=e['F']:
  R=((e['q']-1)*(e['q']-e['F'])+e['alpha'])*(e['q']**2-1)+(v['MC']+e['q']*v['MF'])*v['n_J']
  assert e['R']==R;rank+=1
assert rank>0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'C_nonpositive_scalar_controls':checks,'actual_graph_controls':graph,'natural_signed_rank_controls':rank,
 'boundary_k1_r0_included':True,'lean_executed':False,
 'status':'unelaborated; graph bridge, compact ports and provider proofs remain open'},sort_keys=True,indent=2))

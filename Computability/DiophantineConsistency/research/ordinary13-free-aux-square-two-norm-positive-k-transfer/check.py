from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-two-norm-positive-k-transfer')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-independent-k-two-norm-kpositive-audit','ordinary13-free-aux-square-first-main-index-boundary'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
ind=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());free=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
assert len(ind['source'])==len(free['source'])==84
assert ind['witnesses'][9:11]==['n_eta','n_k'] and free['witnesses'][9:11]==['n_eta','n_zeta']
assert free['witnesses'][11]=='n_y2' and ind['fixed_numerals']==free['fixed_numerals']
# Hash-consed exact ordered expression trees; k_ind := eta+zeta.
table={}
def node(*x):
 if x not in table:table[x]=len(table)
 return table[x]
def build(G,replace_k):
 d={name:node('v',i) for i,name in enumerate(G['witnesses'])};d.update({name:node('p',i) for i,name in enumerate(G['fixed_numerals'])})
 if replace_k:d['n_k']=node('+',node('v',9),node('v',10))
 for n,op,a,b in G['source']:
  x=d[a] if isinstance(a,str) else node('num',a);y=d[b] if isinstance(b,str) else node('num',b)
  d[n]=node(op,x,y)
 return d
x=build(ind,True);y=build(free,False)
for n in ('qm','q','F','alpha','X','Y','U','C','Bt','ell','Z','G','R','a','H','Delta','Dstar','A0','A1'):
 assert x[n]==y[n],n
# Only first and main factors need negative-unit exclusion: product=1
# makes each integer factor ±1.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for U,a,c,z in itertools.product(range(4),repeat=4):
 assert (1+z*z-U*U*(1+(a*a+4*a+3)*c*c))%4!=3
ports=Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
for s in ('theorem port_bounds','theorem K_pos','CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat'):
 assert s in ports
print(json.dumps({'two_predecessor_receipts_reproduced':True,'exact_A0_A1_trees_under_k_equals_eta_plus_zeta':True,'first_and_main_negative_unit_mod4_controls':1280,'natural_k_zero_implies_eta_and_c_zero':True,'standard_compact_output_zero_forces_k_positive_and_c_positive':True,'all_model_or_Lean_proof':False,'lean_executed':False},sort_keys=True,indent=2))

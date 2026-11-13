from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive84-power-model-draft')
files=[p/'Positive84Power.lean.src',p/'Positive84OrientedPower.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-positive84-division-model-draft/Positive84Division.lean.src'),P('research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src'),P('research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src'),P('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src'),P('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean'),P('research/ordinary13-qcube-unscale84/candidate.json')]
s=[f.read_text() for f in files];g=json.loads(s[10]);assert len(g['source'])==84 and g['witnesses'][6:8]==['X','s']
rows={r[0]:r for r in g['source']}
for row in [['q','+',1,'qm'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['R','+','g47','g50']]:assert rows[row[0]]==row
for n in ['def ExactPowerFacts','R=rank84 p v ∧ 13≤n ∧ 2*n=R+1','xcoord R (Y84 p v*(v 6+1))=main',
 'ycoord R (Y84 p v*(v 6+1))=c84 p v','k84 v=R+1+4*(v 6*Y84 p v*Y84 p v)*w',
 'H*(U*v 12+v 6*Y84 p v*q84 p v+R+1)','theorem power_of_facts',
 'let r := n-1','ResidueQBalanceDraft.q_balance','Positive84OrientedPowerDraft.power_of_oriented_balance',
 'def ExactPowerGraphCut','theorem powerGraphCut','theorem indexGraphCut','theorem divCut']:
 assert n in s[0],n
facts=s[0].split('def ExactPowerFacts',1)[1].split('/--',1)[0]
assert 'q84 p v∣v 6' not in facts and 'zero84_to83' not in s[0] and 'zero83_to84' not in s[0]
assert 'theorem q_balance' in s[6] and 'X*Y*q+R+1' in s[6] and 'theorem q_dvd_threeX' in s[7]
assert 'theorem power_bound' in s[9]
# Check exact copied declaration including proof body, not merely its name.
source=s[8].split('theorem power_of_oriented_balance ',1)[1].split('\nend DiophantineConsistency.ResidueSignFreePowerDraft',1)[0]
copy=s[1].split('theorem power_of_oriented_balance ',1)[1].split('\nend DiophantineConsistency.Positive84OrientedPowerDraft',1)[0]
assert source==copy
# Free-ring calculation of the W identity and full extra-term q-balance.
def add(x,y,sgn=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sgn*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,)*9:1};four={(0,)*9:4}
def variable(i):return {tuple(int(j==i) for j in range(9)):1}
q,X,s0,w,main,H,a,c,gamma=[variable(i) for i in range(9)]
Y=mul(mul(mul(q,q),q),s0);U=mul(Y,mul(q,q));W=mul(mul(mul(mul(four,X),q),s0),w)
assert mul(mul(mul(four,X),mul(Y,Y)),w)==mul(U,W)
core=add(add(X,mul(a,c)),mul(H,gamma))
# Cancel H*(R+1) in the original balance before comparison.
carrier=add(add(mul(U,main),mul(H,mul(U,W))),add(mul(U,core),mul(H,mul(mul(X,Y),q))),-1)
qbalance=add(add(mul(q,add(main,mul(H,W))),mul(q,core),-1),mul(H,X),-1)
assert carrier==mul(mul(q,Y),qbalance)
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[3])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'extra_XYq_graph_rows_pinned':True,'same_index_quotient_main_source_flow_checked':True,'copy_of_oriented_power_verbatim':True,'W_and_balance_exact_polynomial_identities':True,'no_q_divides_X_or_84_to83_in_fact_premises':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Unelaborated conditional fact client; exact graph witness cut, providers and endpoint remain open.'},sort_keys=True,indent=2))

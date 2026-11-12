from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
files=[P('research/ordinary13-qcube-main83/candidate.json'),P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-qcube-main83/README.md'),P('research/ordinary13-qcube-unscale84/README.md'),P('research/ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean'),P('reviews/ordinary14-modified-carrier-gamma-model-draft-independent/README.md'),P('research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean'),P('Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean'),P('Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean'),P('Lean/DiophantineConsistency/Compact44/FreeJPowerProjection.lean'),P('research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src'),P('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),P('Lean/DiophantineConsistency/Compact44/P72Exact.lean'),P('research/ordinary14-84-85-ring-client-draft/RingComparison.lean')]
s=[f.read_text() for f in files];g83,g84=map(json.loads,s[:2]);assert [len(g['source']) for g in (g83,g84)]==[83,84]
assert g83['witnesses'][6]=='w' and g84['witnesses'][6]=='X'
assert g83['witnesses'][:6]+g83['witnesses'][7:]==g84['witnesses'][:6]+g84['witnesses'][7:]
a,b=({row[0]:row for row in g['source']} for g in (g83,g84))
assert set(a)-set(b)=={'X'} and set(b)-set(a)=={'g55','g56'}
assert a['X']==['X','*','q','w']
assert a['shift']==['shift','-','g54','r0'] and b['shift']==['shift','-','g56','r0']
assert b['g55']==['g55','*','E','q'] and b['g56']==['g56','+','g54','g55']
for name in a.keys() & b.keys():
 if name!='shift': assert a[name]==b[name],name
for row in [['E','*','X','Y'],['q2','*','q','q'],['U','*','Y','q2'],['g54','*','U','gamma']]: assert a[row[0]]==row
# Formal polynomial identity in q,w,Y,gamma; this is exact over Z,
# not an inference from sampled values.
def add(a,b,sgn=1):
 c=a.copy()
 for m,n in b.items():c[m]=c.get(m,0)+sgn*n
 return {m:n for m,n in c.items() if n}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   k=tuple(a+b for a,b in zip(x,y));c[k]=c.get(k,0)+i*j
 return {k:n for k,n in c.items() if n}
q={(1,0,0,0):1};w={(0,1,0,0):1};Y={(0,0,1,0):1};gamma={(0,0,0,1):1}
X=mul(q,w);U=mul(Y,mul(q,q));E=mul(X,Y)
assert add(mul(U,add(gamma,w,-1)),mul(E,q))==mul(U,gamma)
for i,terms in {4:['theorem gamma_gt_from_modified_balance','(hU : 0<U) (hY : 0<Y) (hq : 1≤q) (hX : X=q*w)','(hR : 3≤R)','(hc : c=ycoord R a) (hd : d=xcoord R a)','(hk : k=R+1+U*W)','w<gamma'],6:['theorem modified_main_parts_positive','theorem q4_from_modified_balance','theorem compact_beta_divides_X'],7:['theorem cancel_three'],8:['theorem graph_power'],10:['theorem power'],11:['theorem compact_early_index'],12:['theorem indices_ordinary']}.items():
 for t in terms:assert t in s[i],(i,t)
# Controls are isolated arithmetic examples, not graph-zero witnesses.
assert (3*(2**3))%3==0 and (2**3)%3!=0
assert 1-2<0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_graph_delta_checked':True,'carrier_identity_in_free_integer_polynomial_ring':True,'unqualified_three_cancellation_counterexample':{'q':3,'X':8},'gamma_subtraction_control':{'gamma_prime':1,'w':2},'scalar_controls_are_full_graph_zeros':False,'lean_executed':False,'status':'Source/math gap audit; no model graph transfer or internal endpoint established.'},sort_keys=True,indent=2))

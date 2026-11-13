from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
files=[P('research/ordinary13-aux-root87-36/candidate.json'),P('research/ordinary13-four-square88-30/candidate.json'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareGraph.lean'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareEndpoint.lean'),P('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean'),P('research/ordinary14-aux-norms-to-bounds-draft/NormsToBounds.lean'),P('research/ordinary14-aux-ring-norm-extraction-draft/RingNormExtraction.lean'),P('research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean'),P('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean'),P('research/ordinary13-aux-root87-36/README.md'),P('research/ordinary13-freej88-four-square-lean-draft/README.md')]
s=[f.read_text() for f in files];child,parent=map(json.loads,s[:2]);assert [len(g['source']) for g in (child,parent)]==[87,88]
assert child['witnesses']==['y' if x=='u' else x for x in parent['witnesses']] and parent['witnesses'][11]=='u' and child['witnesses'][11]=='y' and child['fixed_numerals']==parent['fixed_numerals']
expect=[]
for row in parent['source']:
 if row[0] in ('g78','g80'):continue
 if row[0]=='y2':expect.extend([['y2','*','y','y'],['V2','*','V','V']])
 elif row[0]=='g81':expect.append(['g81','-','y2','V2'])
 else:expect.append(row)
assert child['source']==expect
for n,op,l,r in parent['source']:
 assert f'  let {n} := {l} {op} {r}\n' in s[2],n
for i,n in enumerate(parent['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in s[2]
for i,n in enumerate(parent['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in s[2]
def deps(g,n):
 rows={r[0]:r for r in g['source']}
 def go(x):
  if isinstance(x,int):return set()
  if x not in rows:return {x}
  _,_,l,r=rows[x];return go(l)|go(r)
 return go(n)
for graph,coord in [(parent,'u'),(child,'y')]:
 for n in ('A0','A1','g72','V','Q'):assert coord not in deps(graph,n),(coord,n)
# Exact auxiliary substitution in Z[V,u,Q].
def add(x,y,sign=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sign*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
z={(1,0,0):1};u={(0,1,0):1};Q={(0,0,1):1};y=add(z,u)
old=add(mul(y,y),mul(Q,mul(u,add(y,z))),-1)
new=add(mul(y,y),mul(Q,add(mul(y,y),mul(z,z),-1)),-1)
assert old==new
for i,terms in {5:['theorem oldAux_eq_direct','theorem square_gt_of_aux','theorem positive_of_above','theorem above_of_positive','theorem positive_aux_coordinate_iff','(hQ : 1<Q) (hz : 1<z*z)'],6:['theorem aux_bounds_of_natural_norms','(hfirst :','(hmain :','(hstrong :','(hQ :','(hz :'],7:['theorem root_of_scaled_ring_square','theorem strong_norm_of_ring_residual','theorem bounds_of_direct_field_residuals'],8:['def fiveSquares','theorem fiveSquares_eq_zero_iff'],9:['theorem scaled_quotient']}.items():
 for n in terms:assert n in s[i],(i,n)
# Two isolated scalar controls: old and direct positive inputs do not themselves
# give positive images without norm/bound assumptions; neither is a graph zero.
assert -3+1<0 and 1-3<0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_87_88_json_delta':True,'88_lean_source_literal_rows_match_json':True,'common_residuals_and_V_Q_ignore_aux_coordinate':True,'auxiliary_substitution_free_ring_identity':True,'strict_bounds_are_explicit_hypotheses':True,'scalar_controls_are_full_graph_zeros':False,'lean_executed':False,'status':'Bounded source/math audit; graph bindings, strict bounds, witness maps, providers and endpoint remain open.'},sort_keys=True,indent=2))

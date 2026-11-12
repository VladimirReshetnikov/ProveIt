from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
files=[P('research/ordinary13-four-square88-30/candidate.json'),P('research/ordinary13-ordinary-pair88-46/freej88.json'),P('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive13_87_degree51.json'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareGraph.lean'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareModel.lean'),P('research/ordinary13-freej88-four-square-lean-draft/P88FourSquareEndpoint.lean'),P('research/ordinary13-freej88-lean-draft/P88PairGraph.lean'),P('research/ordinary13-freej88-lean-draft/P88PairModel.lean'),P('research/ordinary13-freej88-lean-draft/P88PairEndpoint.lean'),P('Lean/DiophantineConsistency/Compact44/FreeJ13.lean'),P('Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean'),P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean'),P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean'),P('Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean'),P('Lean/DiophantineConsistency/Compact44/CompactSymbolicModelIff.lean'),P('research/ordinary13-freej87-endpoint/README.md'),P('research/ordinary13-freej88-provider-survey/README.md')]
s=[f.read_text() for f in files];g30,g46,g51=map(json.loads,s[:3]);assert [len(g['source']) for g in (g30,g46,g51)]==[88,88,87]
assert g30['witnesses']==g46['witnesses']==g51['witnesses'] and g30['fixed_numerals']==g46['fixed_numerals']==g51['fixed_numerals']
for g,src in [(g30,s[3]),(g46,s[6]),(g51,s[9])]:
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in src,(n,op,l,r)
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in src,(n,i)
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in src,(n,i)
a,b,c=({r[0]:r for r in g['source']} for g in (g30,g46,g51))
assert set(b)-set(a)=={'Fs','pair','pairm','pair2'} and set(a)-set(b)=={'Fam','Fam2','Fsm2','sum23'}
for n in a.keys() & b.keys():
 if n!='out':assert a[n]==b[n],n
assert a['out']==['out','+','sum01','sum23'] and b['out']==['out','+','sum01','pair2']
assert set(c)-set(b)=={'F0','F1','g86','g87','g88','P13'}
assert set(b)-set(c)=={'A0sq','A1sq','out','pair','pair2','pairm','sum01'}
for n in b.keys() & c.keys():
 if n not in ('g80','g81'):assert b[n]==c[n],n
assert b['g80']==['g80','+','g78','V'] and b['g81']==['g81','*','u','g80']
assert c['g80']==['g80','*','V','V'] and c['g81']==['g81','-','y2','g80']
# Exact substitution identity in Z[V,u].
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
V={(1,0):1};u={(0,1):1};y=add(V,u)
assert add(mul(y,y),mul(V,V),-1)==mul(u,add(y,V))
for i,needles in {4:['theorem zero_iff','P88PairModel.zero_iff p v','FreeJ13.factor_units p v','def expression','theorem positiveBridge'],5:['theorem native_equivalence','theorem standard_equivalence','theorem reference_equivalence','∼mappedNativeRefutation embedding'],7:['theorem zero_iff','FreeJ13.factor_units p v','FreeJ13Halt.positive_model_iff','def expression'],9:['theorem factor_units','theorem unit_iff_one'],10:['theorem positive_model_iff','CompactSymbolicModelIff.p'],11:['def expression','theorem native_equivalence','∼mappedNativeRefutation embedding'],12:['def PositiveModelBridge','theorem bridge_of_positive'],13:['theorem native_of_positive','theorem standard_of_positive','theorem reference_of_positive']}.items():
 for n in needles:assert n in s[i],(i,n)
# Abstract factor-value control only: the pair residual is zero at two -1
# units but the separate residuals are not. Such factors are excluded by
# FreeJ13.factor_units at actual parent graph zeros.
a0=a1=0;Fa=Fs=-1
assert a0*a0+a1*a1+(Fa*Fs-1)**2==0 and (Fa-1)**2+(Fs-1)**2==8
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'all_three_source_literal_rows_match_json':True,'exact_finalizer_and_aux_row_deltas':True,'auxiliary_factorization_free_ring_identity':True,'model_unit_source_hypotheses_checked':True,'negative_unit_control_is_actual_graph_zero':False,'lean_executed':False,'status':'Bounded source/math audit; new graph clients unelaborated, retained endpoint only author-side, provider and file binding open.'},sort_keys=True,indent=2))

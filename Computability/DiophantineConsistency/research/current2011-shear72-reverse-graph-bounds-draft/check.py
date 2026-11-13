from pathlib import Path
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-reverse-graph-bounds-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/current2011-sheared72-46-candidate/polynomial.json').read_text());rows={r[0]:r for r in g['source']}
expected=[['qm','*','beta','J'],['q','+','qm',1],['q2','*','q','q'],['q3','*','q2','q'],['Y','*','s','q3'],['X','*','w','q'],['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','k','Y'],['c','+','kY','eta'],['a','+','E','Y'],['four_a','*',4,'a'],['H','+','four_a',3],['a2','*','a','a'],['Delta','+','a2','H'],['I','*','i','c2'],['f2m1','-','f2',1],['Aaux','*','Delta','f2m1']]
assert all(rows[x[0]]==x for x in expected)
s=(D/'Shear72ReverseGraphBounds.lean.src').read_text()
for t in ['theorem ring_bounds','(hb : 0 ≤ p 0) (hv : ∀ j, 1 ≤ v j)', '0 ≤ d.delta*(d.f^2-1) ∧ 2 ≤ d.i*d.c^2', 'theorem candidate_zero_positive_ordinate','(hb : (0 : DiffRing V) ≤ (p 0 : DiffRing V))','(expressionAt p).evalRing','(eval_expression p vs).symm.trans hz','positive_parent_of_sphere']:
 assert t in s,t
assert g['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
def evaluate(p,v):
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],p))
 for n,op,a,b in g['source']:
  a=a if isinstance(a,int) else e[a];b=b if isinstance(b,int) else e[b]
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
r=random.Random(724672)
for _ in range(200):
 p=[r.randrange(4),*(r.randrange(-2,3) for _ in range(3))];v=[r.randrange(1,4) for _ in range(14)];e=evaluate(p,v)
 assert e['q']>=1 and e['Y']>=1 and e['c']>=3 and e['Delta']>=0 and e['Aaux']>=0 and e['I']>=2
 z=e['V']+v[12];assert e['Na']==e['Aaux']*(e['V']**2-z**2)+z*z
 assert e['polynomial']==e['N0']**2+e['Na']**2+(e['QW']-1)**2+(e['I']**2-e['Aaux'])**2-2
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'checked_graph_rows':len(expected),'positive_input_graph_controls':200,'beta_nonnegative_explicit':True,'lean_executed':False,'model_graph_bound_proved':False},sort_keys=True,indent=2))

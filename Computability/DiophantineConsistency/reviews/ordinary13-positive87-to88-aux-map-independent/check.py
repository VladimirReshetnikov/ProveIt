from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-aux-root87-36/candidate.json': 'abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51', 'research/ordinary13-four-square88-30/candidate.json': 'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420', 'research/ordinary13-positive87-to88-aux-model-draft/Positive87To88Aux.lean.src': '1b6caa17fe7b127503793ac045db903fdc404443f5a384cd7f648c689ffbf538', 'research/ordinary13-positive84-to87-unscale-model-draft/PositiveUnscale87Graph.lean.src': 'cfb968caa89363a159fd24093d57eca5c80a86839a0798430a7b01fd557f2de8', 'research/ordinary13-freej88-four-square-lean-draft/P88FourSquareGraph.lean': '614cb3ed5a91e919b5e44a5ae7f4fa7210a0a8b41bf5953d99d54c303b4f042e', 'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean': '796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7', 'research/ordinary14-direct-first-root-model-draft/FirstRootBridge.lean': '92ace01321c77730c81eba032d1fdd86778e53399a073258cdbd49f7a621718f', 'research/ordinary13-positive87-to88-aux-model-draft/receipt.json': 'fa6cb099779de6f3d678bb9b6962f67fa1541e9f8a50357775ca5cca11ff30b3'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);g87,g88=(json.loads(Path(p).read_text()) for p in f[:2]);src,s87,s88,helper,five=(Path(p).read_text() for p in f[2:7])
assert (len(g87['source']),len(g88['source']))==(87,88)
assert g87['witnesses'][11]=='y' and g88['witnesses'][11]=='u'
assert g87['witnesses'][:11]+g87['witnesses'][12:]==g88['witnesses'][:11]+g88['witnesses'][12:]
for g,s in [(g87,s87),(g88,s88)]:
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in s
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in s
 for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in s
a,b=({r[0]:r for r in g['source']} for g in (g87,g88))
for n in a.keys() & b.keys():
 if n not in {'y2','g81'}:assert a[n]==b[n],n
assert a['y2']==['y2','*','y','y'] and b['y2']==['y2','*','g78','g78']
assert a['g81']==['g81','-','y2','V2'] and b['g81']==['g81','*','u','g80']
assert b['g78']==['g78','+','V','u'] and b['g80']==['g80','+','g78','V']
for t in ('A0','A1','g72','Q','V'):
 def deps(r,n):
  if n not in r:return {n}
  _,_,x,y=r[n];return (deps(r,x) if isinstance(x,str) else set()) | (deps(r,y) if isinstance(y,str) else set())
 assert 'y' not in deps(a,t) and 'u' not in deps(b,t),t
for row in [['q','+',1,'qm'],['qF','-','q','F'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50'],['g74','*','T','c'],['g75','-','g74','R'],['g76','*','f2','g75'],['V','-','g76','c'],['rho','-','f2',1],['Q','*','Delta','rho']]:assert a[row[0]]==row
for text in ['(∃ u : V, 0<u ∧ fiveSquares first main (oldAux z Q u) strong guard=0) ↔','(∃ y : V, 0<y ∧ fiveSquares first main (directAux z Q (ι y)) strong guard=0)','(hQ : 1<Q) (hz : 1<z*z)']:
 assert text in helper,text
assert '(a*a+b*b)+(c*c+d*d)+e*e' in five
assert 'InternalZero (PositiveUnscale87GraphDraft.graph p).output v ∨' in src
assert 'InternalZero (P88FourSquare.graph p).output v) →\n    1<Q v ∧ 1<z p v*z p v' in src
assert '(strong p v) 0 (z p v) (Q v) hQ hz).mpr' in src
assert '(strong p v) 0 (z p v) (Q v) hQ hz).mp' in src
# Exhaustive scalar checks on both auxiliary witness orientations (not graph zeros).
cases=0;negz=0
for z in range(-35,36):
 for Q in range(2,14):
  if z*z<=1:continue
  for y in range(1,100):
   if y*y-Q*(y*y-z*z)-1:continue
   u=y-z
   assert u>0 and (z+u)**2-Q*u*((z+u)+z)-1==0
   assert (z+u)**2-Q*((z+u)**2-z*z)-1==0
   cases+=1;negz+=z<0
assert cases>0 and negz>0
print(json.dumps({'sha256':PINS,'both_graph_source_rows_checked':True,'common_fields_coordinate11_independent':True,'bound_and_witness_directions_checked':True,'bounded_auxiliary_witness_cases':cases,'negative_z_cases':negz,'lean_executed':False,'status':'Independent source review; strict graph bounds, model provider ancestry and Lean remain open.'},sort_keys=True,indent=2))

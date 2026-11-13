from pathlib import Path
from hashlib import sha256
import json,sys,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-parent-even-index-squarefree-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text())
child=json.loads(Path('research/ordinary9-shifted-free-aux-two-norm64/candidate.json').read_text())
def expressions(g):
 e={v:('var',v) for v in g['witnesses']+g['fixed_numerals']}
 for name,op,a,b in g['source']:e[name]=(op,e[a] if isinstance(a,str) else ('lit',a),e[b] if isinstance(b,str) else ('lit',b))
 return e
p,q=expressions(parent),expressions(child)
for name in ('A0','A1','R','a','c','H','Delta','Dstar'):assert p[name]==q[name]
rows={row[0]:row[1:] for row in parent['source']}
for x,r in {'H':['+',3,'g15'],'g15':['*',4,'a'],'g17':['*','a','a'],
 'Delta':['+','H','g17'],'f2':['*','n_f','n_f'],'rho':['-','f2',1],
 'i':['+','n_i',1],'I':['*','c2','i'],'g71':['*','I','I'],
 'Q':['*','Delta','rho'],'g72':['-','g71','Q'],'Fs':['+',1,'g72'],
 'F0':['+',1,'A0'],'F1':['+',1,'A1'],'P01':['*','F0','F1'],
 'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert rows[x]==r,(x,rows[x])
# Any integer factorization ab=1 forces units; exclude the negative strong unit.
units=[(a,b) for a in range(-5,6) for b in range(-5,6) if a*b==1]
assert set(units)=={(-1,-1),(1,1)}
for a in range(4):
 for f in range(4):
  for I in range(4):assert (1+I*I-(a*a+4*a+3)*(f*f-1))%4 in (0,1,2)
# Independent modular induction test for Q^m modulo Delta and gcd identity.
count=0
for A in range(2,51):
 Delta=A*A-1;x,y=1,0
 for m in range(1,81):
  x,y=(A*x+Delta*y)%Delta,(x+A*y)%Delta
  assert y==m*pow(A,m-1,Delta)%Delta
  assert math.gcd(y,Delta)==math.gcd(m,Delta)
  count+=1
# Exhaust gcd/squarefree reduction on a bounded range including zero I.
def squarefree(n):return all(n%(j*j) for j in range(2,math.isqrt(n)+1))
for delta in range(1,151):
 if squarefree(delta):
  for I in range(300):
   if I*I%delta==0:assert I%delta==0
for c in range(1,31):
 for delta in range(1,31):
  if math.gcd(c,delta)!=1:continue
  for v in range(61):
   if delta*v%(c*c)==0:assert v%(c*c)==0
# Source declaration exists; its compiled/model provider is outside this review.
source=Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean').read_text()
assert 'theorem solution_index (b x y : V) (h : x*x=1+delta b*y*y)' in source
assert '∃ time : V, time≤y ∧ xcoord time b=x ∧ ycoord time b=y' in source
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'shared_graph_fields':8,'literal_factor_rows_checked':True,'all_mod4_cases':64,
 'modular_gcd_identity_controls':count,'squarefree_and_coprimality_controls':True,
 'standard_pell_classification_assumed':True,'same_data_scope_preserved':True,
 'unrestricted_graph_nonequivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))

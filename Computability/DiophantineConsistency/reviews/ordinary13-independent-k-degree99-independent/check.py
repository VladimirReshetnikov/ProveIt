from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-degree99-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-eta-zeta84-independent-k-degree99')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());assert len(g['source'])==84
rows={x[0]:x for x in g['source']}
for row in [['qm','*','n_J','beta'],['ell','*','E','kY'],['g30','+','ell','n_k'],['g31','+','g30','n_r'],['folded_kBt','*','n_k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['g19','*','a','c'],['b0','+','X','g19'],['g17','*','a','a'],['Delta','+','H','g17'],['c2','*','c','c'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65'],['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]:assert rows[row[0]]==row
# Coefficient polynomials in all four symbolic ports, plus a leading-degree
# pair (degree in t, symbolic coefficient). A tie cancellation outside the
# two manually factored residuals is fail-closed rather than guessed.
Z=(0,0,0,0)
def cp(n):return {Z:n} if n else {}
def port(i):
 e=[0]*4;e[i]=1;return {tuple(e):1}
def plus(x,y,sign=1):
 out=x.copy()
 for k,v in y.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def times(x,y):
 out={}
 for a,v in x.items():
  for b,w in y.items():
   k=tuple(i+j for i,j in zip(a,b));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
def add(x,y,sign=1):
 dx,cx=x;dy,cy=y
 if dx>dy:return x
 if dx<dy:return (dy,{k:sign*v for k,v in cy.items()})
 c=plus(cx,cy,sign)
 if not c:raise ValueError('leading cancellation requires a separate identity')
 return dx,c
def mul(x,y):return x[0]+y[0],times(x[1],y[1])
def con(k):return 0,cp(k)
def scale(k,x):return mul(con(k),x)
vals={n:(1,cp(1)) for n in g['witnesses']};vals.update({n:(0,port(i)) for i,n in enumerate(g['fixed_numerals'])})
def operand(x):return vals[x] if isinstance(x,str) else con(x)
for name,op,l,r in g['source']:
 if name=='A0':
  b=vals['qm'];ell=vals['ell'];k=vals['n_k'];Bt=vals['Bt'];rr=vals['n_r']
  # D=b*(k+r-k*Bt)-Bt; cancelling b²ell² yields A0.
  D0=add(mul(b,add(add(k,rr),mul(k,Bt),-1)),Bt,-1)
  vals[name]=add(add(scale(2,mul(mul(b,ell),D0)),mul(D0,D0)),mul(mul(b,b),add(con(1),mul(ell,k))),-1)
 elif name=='A1':
  U=vals['U'];a=vals['a'];c=vals['c'];H=vals['H'];X=vals['X'];shift=vals['shift']
  A0=mul(mul(U,a),c);E=add(mul(U,X),mul(H,shift))
  vals[name]=add(add(scale(2,mul(A0,E)),mul(E,E)),mul(mul(U,U),add(con(1),mul(H,mul(c,c)))),-1)
 else:
  x=operand(l);y=operand(r)
  vals[name]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
assert [vals[n][0] for n in ('A0','A1','Fa','Fs','out')]==[17,30,30,22,99]
assert vals['A0'][1]=={(11,0,0,0):-2,(10,0,0,0):4}
assert vals['A1'][1]=={(21,0,0,0):8}
assert vals['Fa'][1]=={(14,0,0,0):1}
assert vals['Fs'][1]=={(12,0,0,0):1}
assert vals['out'][1]=={(58,0,0,0):-16,(57,0,0,0):32}
# Independent structural bounds after two exact algebraic expansions.
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']})
for n,op,l,r in g['source']:
 x=deg[l] if isinstance(l,str) else 0;y=deg[r] if isinstance(r,str) else 0
 deg[n]=x+y if op=='*' else max(x,y)
assert [deg[n] for n in ['qm','ell','Bt','U','X','H','shift','a','c','Fa','Fs']]==[1,11,3,6,2,6,7,6,5,30,22]
Db=max(1+max(1,1,1+3),3);Eb=max(6+2,6+7)
assert Db==5 and Eb==13
assert max(1+11+Db,2*Db,2+max(0,11+1))==17
assert max(6+6+5+Eb,2*Eb,12+max(0,6+2*5))==30
assert 17+30+30+22==99
# Parent-child graph relation is the exact invertible linear substitution.
p=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert p['witnesses'][9:11]==['n_eta','n_zeta'] and g['witnesses'][9:11]==['n_eta','n_k']
assert [r for r in p['source'] if 'n_zeta' in r]==[['kbase','+','n_eta','n_zeta']]
assert [[('n_k' if z=='kbase' else z) for z in row] for row in p['source'] if row!=['kbase','+','n_eta','n_zeta']]==g['source']
assert 67*8807==590069 and 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduces':True,'global_cancellation_degree_bound':99,
 'independent_leading_form_method':'symbolic four-port leading coefficients with separate first/main cancellations',
 'ray_factor_degrees':[17,30,30,22],'ray_t99':'-16*beta^57*(beta-2)',
 'nonzero_for_integer_beta_at_least_3':True,'parent_invertible_linear_substitution_checked':True,
 'candidate_zero_equivalence_proved':False,'lean_executed':False,
 'scope':'Independent external algebra review only; no graph-zero, Lean, provider, axiom, PDF or minimality claim.'},sort_keys=True,indent=2))

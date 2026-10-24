"""Authored exact checks for the compact residual lists printed in the report."""
import ast,json
from pathlib import Path
import sympy as s
R=Path(__file__).resolve().parent; P=R.parent/'positivity'

def parse(text,e):
 def go(n):
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return s.Integer(n.value)
  if isinstance(n,ast.Name):return e[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=go(n.left),go(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow) and isinstance(b,s.Integer) and 0<=b<=20:return a**b
  raise ValueError('unsupported expression')
 return s.expand(go(ast.parse(text,mode='eval').body))

def inspect(name,mode):
 obj=json.loads((P/(name+'.json')).read_text());e={x:s.Symbol(x) for x in obj['variables']+obj['fixed_numerals']}
 # Printed compact names are aliases, not extra unknowns.
 e['v']=e['v_scale'];e['A']=e['cone_A'];e['B']=e['cone_B']; e['J']=3*e['J3']+1;e['q']=e['beta']*e['J']+1;e['W']=4*(3*e['w3']+1)
 for a,b in [('t1','cone_pos1'),('t2','cone_pos2'),('t3','cone_pos3'),('e1','eta_zeta_pos1'),('e2','eta_zeta_pos2'),('e3','eta_zeta_pos3')]:
  if b in e:e[a]=e[b]
 e['C']=e['q']-e['F']-e['alpha'];e['k']=e['eta']+e['zeta'] if mode!='oct' else 1-e['V']+e['j']*e['c']+e['h']*e['E'];e['H']=4*e['a']+3
 if mode!='quartic':e['X']=e['W']*e['q']
 if mode=='oct':
  e['Delta']=e['a']**2+e['H'];e['D']=e['X']+e['a']*e['c']+e['gamma']*e['H'];e['P']=e['k']+e['E']*(e['c']-e['eta'])
 e['R']=((e['q']-1)*(e['q']-e['F'])+e['alpha'])*(e['q']**2-1 if mode=='oct' else e['L'])+(e['MC']+e['q']*e['MF'])*e['J']
 if mode=='quartic':e['R']=(e['q']-e['F'])*(e['N']-e['q']-e['L'])+e['alpha']*e['L']+(e['MC']+e['q']*e['MF'])*e['J']
 e['T']=e['A']*e['F']*e['B']*e['C']-(e['q']-e['A']*e['F']-e['B']*e['C'])**2
 cone='T-(1+t1**2+t2**2+t3*(t3+1))';sign='eta*zeta-(1+e1**2+e2**2+e3*(e3+1))'
 if mode=='quartic':rows=['L-q**2+1','N-q*(L+1)','a-E-(2*v+1)*N','X-W*q','E+X*(E-a)','c-eta+(E-a)*k','P-k-E*(c-eta)','tau**2-P**2+P*k-1','C2-c**2','D-X-a*c-gamma*H','Delta-a**2-H','D**2-Delta*C2-1','k-1-h*E-R','(K0+W)*C-F-z*(q-1)','F2-f**2','V+c-f*o','V-c*j+k-1-h*E','g+V**2-y**2','I-(2*r+1)*C2','Baux-I**2','Baux-Delta*(F2-1)','y**2-Baux*g-1',cone,sign]
 elif mode=='sextic':rows=['L-q**2+1','a-E-(2*v+1)*q*(L+1)','E+X*(E-a)','c-eta+(E-a)*k','tau**2+(2*tau-k)*E*(c-eta)-1','D-X-gamma*H','D**2+2*a*c*D-H*c**2-1','k-1-h*E-R','(K0+W)*C-F-z*(q-1)','F2-f**2','f*o-c-c*j+k-1-h*E','g+F2*o**2-2*f*o*c+c**2-y**2','I-(2*r+1)*c**2','I**2-(a**2+4*a+3)*(F2-1)','y**2-I**2*g-1',cone,sign]
 else:rows=['a-E-(2*v+1)*q**3','E+X*(E-a)','c-eta+(E-a)*k','tau**2-P*E*(c-eta)-1','D**2-Delta*c**2-1','k-1-h*E-R','(K0+W)*C-F-z*(q-1)','V+c-f*o','I-(2*r+1)*c**2','I**2-Delta*(f**2-1)','I**2*(V**2-y**2)+y**2-1',cone,'eta*(k-eta)-(1+e1**2+e2**2+e3*(e3+1))']
 got=[parse(t,e) for t in rows];raw={x:s.Symbol(x) for x in obj['variables']+obj['fixed_numerals']};want=[parse(t,raw) for t in obj['residuals']]
 # Row ordering may differ, signs are relevant only before squaring but
 # allow both because the displayed object is the sum of squares.
 def canon(p):
  p=s.Poly(p,*raw.values());lc=p.LC();return str(p.as_expr() if lc>=0 else -p.as_expr())
 if sorted(map(canon,got))!=sorted(map(canon,want)):
  print('DISPLAY ONLY',set(map(canon,got))-set(map(canon,want)));print('PACKET ONLY',set(map(canon,want))-set(map(canon,got)));raise RuntimeError(name+' displayed rows differ')
 return {'packet':name,'residuals':len(rows),'status':'PASS'}
result=[inspect('quartic37','quartic'),inspect('sextic30','sextic'),inspect('octic26','oct')]
(R/'DISPLAYED_ROWS_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

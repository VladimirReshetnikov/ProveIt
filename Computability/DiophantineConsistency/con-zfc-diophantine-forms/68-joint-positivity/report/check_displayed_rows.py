"""Independently expand the compact low-degree presentation against source JSON."""
import ast,json
from pathlib import Path
import sympy as s
R=Path(__file__).resolve().parent.parent
src=json.loads((R/'integer_system/inherited/octic30.json').read_text())
names=src['variables']+src['fixed_numerals']
env={n:s.Symbol(n) for n in names}
def parse(t):
 def p(n):
  if isinstance(n,ast.Constant) and type(n.value)==int:return s.Integer(n.value)
  if isinstance(n,ast.Name):return env[n.id]
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -p(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=p(n.left),p(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow) and b.is_Integer and 0<=b<=12:return a**b
  raise ValueError('bad syntax')
 return p(ast.parse(t,mode='eval').body)
env['Q']=parse('J*beta');env['R']=parse('8*rho**2+(3+4*a)*gamma')
compact=['8*rho**2-4*u**2*(1+Q)','a-E-(1+2*v_scale)*(1+Q)**3','E+8*rho**2*(E-a)','c-eta+(a-E)*(V-1-j*c-h*E)','tau**2-1-E*(c-eta)*(1-V+j*c+h*E)-E**2*(c-eta)**2','R**2+2*c*a*R-(3+4*a)*c**2-1','-V+j*c-J*MC-J*MF*(1+Q)+(Q+2)*(F*Q**2-alpha*Q-Q**2*(Q+1))','(1-alpha-F+Q)*(K0+4*u**2)-F-Q*z','V+c-f*o','I-(1+2*r)*c**2','I**2+(1-f**2)*(a**2+4*a+3)','-1+V**2*I**2+y**2-y**2*I**2']
for i,t in enumerate(compact):
 if s.expand(parse(t)-parse(src['residuals'][i]))!=0:raise ValueError('row '+str(i+1))
print('PASS: all 12 compact report residuals equal the exact inherited rows')

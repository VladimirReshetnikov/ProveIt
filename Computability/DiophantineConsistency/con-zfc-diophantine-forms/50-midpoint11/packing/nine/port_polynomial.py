"""Parse fixed coefficient recipes in four named ports, using exact integers."""
import ast
PORTS=['beta','K0','MC','MF']; ZERO=(0,0,0,0)
def add(a,b,sgn=1):
 r=dict(a)
 for e,c in b.items():r[e]=r.get(e,0)+sgn*c
 return {e:c for e,c in r.items() if c}
def mul(a,b):
 r={}
 for e,c in a.items():
  for f,d in b.items():
   ef=tuple(x+y for x,y in zip(e,f));r[ef]=r.get(ef,0)+c*d
 return {e:c for e,c in r.items() if c}
def parse(text):
 def visit(n):
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return {ZERO:n.value} if n.value else {}
  if isinstance(n,ast.Name) and n.id in PORTS:
   e=[0]*4;e[PORTS.index(n.id)]=1;return {tuple(e):1}
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {e:-c for e,c in visit(n.operand).items()}
  if isinstance(n,ast.BinOp):
   a=visit(n.left)
   if isinstance(n.op,ast.Pow):
    assert isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and n.right.value>=0
    r={ZERO:1}
    for _ in range(n.right.value):r=mul(r,a)
    return r
   b=visit(n.right)
   if isinstance(n.op,ast.Add):return add(a,b)
   if isinstance(n.op,ast.Sub):return add(a,b,-1)
   if isinstance(n.op,ast.Mult):return mul(a,b)
  raise ValueError('Unexpected fixed polynomial expression')
 return visit(ast.parse(text,mode='eval').body)

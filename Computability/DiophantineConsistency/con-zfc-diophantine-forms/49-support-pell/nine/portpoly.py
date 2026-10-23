"""Exact polynomial parser for coefficient expressions in four fixed ports."""
import ast
PORTS=('beta','K0','MC','MF')
Z=(0,0,0,0)
def add(a,b,sgn=1):
 r=dict(a)
 for m,c in b.items():
  r[m]=r.get(m,0)+sgn*c
  if not r[m]:del r[m]
 return r
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items() if c}
def parse(expr):
 def rec(n):
  if isinstance(n,ast.Constant) and isinstance(n.value,int):return {Z:n.value} if n.value else {}
  if isinstance(n,ast.Name) and n.id in PORTS:
   m=list(Z);m[PORTS.index(n.id)]=1;return {tuple(m):1}
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return {m:-c for m,c in rec(n.operand).items()}
  if isinstance(n,ast.BinOp):
   if isinstance(n.op,ast.Add):return add(rec(n.left),rec(n.right))
   if isinstance(n.op,ast.Sub):return add(rec(n.left),rec(n.right),-1)
   if isinstance(n.op,ast.Mult):return mul(rec(n.left),rec(n.right))
   if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and isinstance(n.right.value,int) and n.right.value>=0:
    p={Z:1}
    for _ in range(n.right.value):p=mul(p,rec(n.left))
    return p
  raise ValueError(ast.dump(n))
 return rec(ast.parse(str(expr),mode='eval').body)

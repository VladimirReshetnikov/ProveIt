#!/usr/bin/env python3
"""Construct the scaled-sign 20-integer degree-18 candidate.

The exact sparse arithmetic engine is retained verbatim from the pinned
parent checker (parent_ring.py); no parent verifier is executed on import.
"""
import ast, collections, hashlib, json
from pathlib import Path
from parent_ring import Ring, need

ROOT=Path(__file__).resolve().parent
VARS='J3 C z f h r v_scale w3 tau eta y gamma o j c b pair_root pair_pos1 pair_pos2 pair_pos3'.split()
PORTS='beta K0 MC MF cone_A cone_B'.split()
DEFS=[
 ('J','3*J3+1'),('q','beta*J+1'),('W','12*w3+4'),
 ('X','q*W'),('Ytarget','(2*v_scale+1)*q**3'),
 ('F','(K0+W)*C-z*(q-1)'),('alpha','q-F-C'),
 ('E','X*b'),('a','E+b'),('V','f*o-c'),
 ('k','1-V+j*c+h*E'),('H','4*a+3'),('Delta','a*a+H'),
 ('I','(2*r+1)*(c*c)'),
 ('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('d','(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)**2'),
 ('ueta','b*eta'),('tnew','ueta*(c-eta-ueta)'),
 ('Pos','1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)'),
 ('ell','E*(c-eta)'),('p','f*o'),('S','X+gamma*H'),
 ('I2','I*I'),('Q','Delta*(f*f-1)'),
]
ROWS=[
 'b-Ytarget',
 'c-eta-k*b',
 'tau*tau-ell*(k+ell)-1',
 '(X+a*c+gamma*H)**2-Delta*(c*c)-1',
 'c*j-V-R',
 'I2-Q',
 'I2*(V*V-(p+y)**2)+(p+y)**2-1',
 'd*tnew-(pair_root**2-d-tnew+1)**2-Pos',
]

def parse_eval(text, vals, add, sub, mul, const):
 def go(n):
  if isinstance(n,ast.Name): return vals[n.id]
  if isinstance(n,ast.Constant) and type(n.value) is int: return const(n.value)
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub): return sub(const(0),go(n.operand))
  if isinstance(n,ast.BinOp):
   a=go(n.left)
   if isinstance(n.op,ast.Pow):
    need(isinstance(n.right,ast.Constant) and 0<=n.right.value<=8,'small fixed exponent')
    e=n.right.value
    if not e:return const(1)
    out=a
    for _ in range(1,e):out=mul(out,a)
    return out
   b=go(n.right)
   return {ast.Add:add,ast.Sub:sub,ast.Mult:mul}[type(n.op)](a,b)
  raise ValueError(ast.dump(n))
 return go(ast.parse(text,mode='eval').body)

def symbolic():
 ring=Ring(VARS+PORTS)
 vals={n:ring.symbol(n) for n in VARS+PORTS}
 ev=lambda s:parse_eval(s,vals,ring.add,lambda a,b:ring.add(a,b,-1),ring.mul,ring.constant)
 for name,expr in DEFS:vals[name]=ev(expr)
 return ring,vals,[ev(s) for s in ROWS]

def graph():
 source=[]; cache={}
 def gate(op,x,y):
  if op in ('+','*') and str(x)>str(y):x,y=y,x
  if op=='+' and x==0:return y
  if op=='+' and y==0:return x
  if op=='-' and y==0:return x
  if op=='*' and x==1:return y
  if op=='*' and y==1:return x
  key=op,x,y
  if key not in cache:
   out='g'+str(len(source));cache[key]=out;source.append([out,op,x,y])
  return cache[key]
 vals={n:n for n in VARS+PORTS}
 ev=lambda s:parse_eval(s,vals,lambda a,b:gate('+',a,b),lambda a,b:gate('-',a,b),lambda a,b:gate('*',a,b),lambda n:n)
 for n,s in DEFS:vals[n]=ev(s)
 rows=[ev(s) for s in ROWS]
 out=None
 for r in rows:
  sq=gate('*',r,r);out=sq if out is None else gate('+',out,sq)
 needed={out}
 for name,op,a,b in reversed(source):
  if name in needed:needed.update([a,b])
 source=[r for r in source if r[0] in needed]
 need(all(n in needed for n in VARS),'all witnesses live')
 return dict(name='scaled_signs20_degree18',domain='unrestricted integers',witnesses=VARS,
  fixed_numerals=PORTS,source=source,residuals=rows,output=out,operations=len(source),
  operation_breakdown=dict(collections.Counter(r[1] for r in source)))

def main():
 ring,vals,rows=symbolic()
 degrees=[ring.degree(p,VARS) for p in rows]
 need(degrees==[4,5,8,8,5,8,9,8],('degrees',degrees))
 lead=ring.leading(rows[6],VARS,9)
 # Only the centered auxiliary row reaches degree nine. Its leader is
 # -8 r^2 c^4 f o (c+y); beta and all native payloads disappear.
 expected=ring.parse('-8*r*r*c**4*f*o*(c+y)')
 need(lead==expected,'entire degree-nine leading form')
 g=graph()
 packet=dict(name='scaled_signs20_degree18',domain='unrestricted integers',variables=VARS,
  fixed_numerals=PORTS,abbreviations=DEFS,residuals=ROWS,
  single_polynomial='sum of residual squares',variable_count=len(VARS),residual_count=len(ROWS),
  exact_degree=18,residual_degrees=degrees,
  leading_form='64*r**4*c**8*f**2*o**2*(c+y)**2',
  coefficient_binding='parent/coefficients/BINDING.json',
  parent='parent/equation.json',proof='PROOF.md')
 for filename,data in [('equation.json',packet),('circuit.json',g)]:
  (ROOT/filename).write_text(json.dumps(data,indent=2)+'\n')
 receipt=dict(variables=20,residuals=8,degree=18,residual_degrees=degrees,
  operations=g['operations'],operations_breakdown=g['operation_breakdown'],
  leading_form=packet['leading_form'],residual_terms=[len(p) for p in rows],
  parent_equation_sha256=hashlib.sha256((ROOT/'parent/equation.json').read_bytes()).hexdigest())
 (ROOT/'BUILD_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

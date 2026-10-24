#!/usr/bin/env python3
"""Generate literal weak-congruence twelve-integer consistency polynomials."""
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PARENT_SHA='5e85d22284880b36b44d7f50ef1648fbcbff4154cc56ab8ae393611b89fa55dc'
VARS=['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
FORMULAS=[
 ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q2*q'),
 ('W0','12*w+4'),('X','q*W0'),('Y','q*v'),('E','X*Y'),('a','E+Y'),
 ('H','4*a+3'),('Delta','a*a+H'),('F','(K0+W0)*C-z*qm'),
 ('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),('k','R+1+h*E'),
 ('eta','c-Y*k'),('zeta','k-eta'),('coneU','cone_A*F'),('coneV','cone_B*C'),
 ('G','coneU*coneV-(q-coneU-coneV)*(q-coneU-coneV)'),('Peta','eta*zeta'),
 ('err','t*t-G-Peta+1'),('Pair','G*Peta-err*err'),('Dg','(3*Pair-4)*s*s+1'),
 ('c2','c*c'),('sr','s*r'),('I','sr*c2'),('I2','I*I'),('strong','Delta*I2'),('Df','strong+1'),
 ('Q','Delta*strong'),('delta','Q-1'),('b','c-R+4*I*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
 ('ell','X*Y*Y'),('L','ell*k'),('Dt','L*(L+k)+1'),
 ('K','X*(2*X-3*c)-2'),('M','2*q2'),('D','M*H'),('D2','D*D'),('D3','D2*D'),
 ('M2','M*M'),('M4','M2*M2'),('M5','M4*M'),('S','sr*M5*H'),('S2','S*S'),
 ('Ccarrier','M*K+H*(v-q2)'),('zcarrier','D*T+Ccarrier'),('zc2','zcarrier*zcarrier'),
 ('zc3','zc2*zcarrier'),('Acarrier','(zc2+3*D2)*(zc3-19*D3)'),('center','S*n-Acarrier'),
 ('ra','9*S2*Df'),('rb','81*S2*Dt'),('re','729*S2*Dg'),('cn','S2*Cy')]

class DAG:
 def __init__(self):self.nodes=[];self.memo={}
 def emit(self,row):
  key=tuple(row)
  if key not in self.memo:self.memo[key]=len(self.nodes);self.nodes.append(list(row))
  return self.memo[key]
 def op(self,op,a,b):
  left,right=self.nodes[a],self.nodes[b]
  if left[0]==right[0]=='integer':
   x,y=left[1],right[1];return self.emit(['integer',x+y if op=='add'else x-y if op=='sub'else x*y])
  if op=='mul':
   if left==['integer',1]:return b
   if right==['integer',1]:return a
   if left==['integer',0]or right==['integer',0]:return self.emit(['integer',0])
  if op in ['add','mul']and a>b:a,b=b,a
  return self.emit([op,a,b])
 def expression(self,text,env):
  def visit(n):
   if isinstance(n,ast.Name):return env[n.id]
   if isinstance(n,ast.Constant):return self.emit(['integer',n.value])
   if isinstance(n,ast.UnaryOp)and isinstance(n.op,ast.USub):return self.op('sub',self.emit(['integer',0]),visit(n.operand))
   if isinstance(n,ast.BinOp):return self.op({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(n.op)],visit(n.left),visit(n.right))
   raise ValueError('nonpolynomial syntax')
  return visit(ast.parse(text,mode='eval').body)


def circuit(integral=False, centered=True):
 d=DAG();env={v:d.emit(['variable',v])for v in VARS}
 env.update({v:d.emit(['coefficient',v])for v in PORTS})
 for name,text in FORMULAS:env[name]=d.expression(text,env)
 if integral and not centered:env['cn']=d.expression('cn*delta',env)
 env['ndelta']=d.emit(['integer',1])if integral else env['delta']
 # Evaluate the cleared three-root norm in the quadratic algebra u^2=re,
 # at center-u, then take the final quadratic norm. No radical is emitted.
 tail=[('x2','center*center'),('t20','x2+re'),('t21','-2*center'),('ab','ra+rb'),
  ('q0','ndelta*(t20-ab)-cn'),('q1','ndelta*t21'),('tn','ndelta*ndelta*ra*rb'),
  ('rn','ndelta*cn'),('v0','q0*q0+re*q1*q1-4*(tn+rn*ab)'),('v1','2*q0*q1'),
  ('z64','64*tn*rn'),('n0','v0*v0+re*v1*v1-z64*t20'),
  ('n1','2*v0*v1-z64*t21'),('output','n0*n0-re*n1*n1')]
 if centered:
  if integral:
   additions=[('SV','S*V'),('Lc','SV*delta'),('Ns','S2*delta-Lc*SV'),('cn','Lc*Lc-Ns'),('U','center'),('center','center+Lc')]
  else:
   additions=[('SV','S*V'),('Lc','SV*delta'),('Ns','S2-SV*SV'),('U','center'),('center','center+SV')]
  for name,text in additions:env[name]=d.expression(text,env)
  replacement='U*(U+2*Lc)+Ns+re-ab' if integral else 'U*(delta*U+2*Lc)+Ns+delta*(re-ab)'
  tail=[(name, replacement if name=='q0' else text)for name,text in tail]
 for name,text in tail:env[name]=d.expression(text,env)
 live=set();todo=[env['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if d.nodes[i][0]in ['add','sub','mul']:todo.extend(d.nodes[i][1:])
 order=sorted(live);mapping={i:j for j,i in enumerate(order)}
 nodes=[[r[0],mapping[r[1]],mapping[r[2]]]if r[0]in ['add','sub','mul']else r
        for i in order for r in [d.nodes[i]]]
 named={v:mapping[i]for v,i in env.items()if i in live}
 counts=dict(Counter(r[0]for r in nodes if r[0]in ['add','sub','mul']))
 degrees=[]
 for r in nodes:
  if r[0]in ['add','sub','mul']:degrees.append(degrees[r[1]]+degrees[r[2]]if r[0]=='mul'else max(degrees[r[1]],degrees[r[2]]))
  else:degrees.append(1 if r[0]=='variable'else 0)
 return dict(schema='literal_integer_arithmetic_dag_v1',name='weak_carrier12_'+('centered'if centered else 'integral'if integral else'rational'),
  domain='unrestricted integers',variables=VARS,variable_count=12,nodes=nodes,named_registers=named,
  output=mapping[env['output']],operations=sum(counts.values()),operation_counts=counts,
  auxiliary_variant='integral' if integral else 'rational',
  coefficient_binding='coefficients/BINDING.json',exact_degree=784 if integral else 768,
  syntactic_bound=degrees[mapping[env['output']]],variant='centered'if centered else 'integral'if integral else'rational',
  parent_sha256=PARENT_SHA,ordinary_proof='PROOF.md',
  proof_status='Ordinary reduction via weaker fifth-power congruence, actual-coefficient height, signed main folding, guard-first c nonzero, and optional integral auxiliary translation. No new native calibration, Lean or internal-ZFC endpoint.')



def main():
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--check',action='store_true')
 args=parser.parse_args()
 reports={}
 for name,integer,centered in [('rational',False,True),('integral',True,True)]:
  p=circuit(integer,centered)
  data=(json.dumps(p,indent=2,sort_keys=True)+'\n').encode()
  out=HERE/(name+'.json')
  if args.check:
   if out.read_bytes()!=data:raise ValueError('rebuild differs: '+name)
  else:out.write_bytes(data)
  reports[name]={k:p[k]for k in ['operations','operation_counts','exact_degree','syntactic_bound']}
 print(json.dumps(reports,indent=2))

if __name__=='__main__':main()

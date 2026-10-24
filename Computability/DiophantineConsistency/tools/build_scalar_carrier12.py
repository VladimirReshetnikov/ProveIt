#!/usr/bin/env python3
"""Build complete twelve-integer scalar-intersective quadratic-projection equations."""
import argparse
import ast
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PARENT=ROOT/'candidates/valuation-shared-norms'
OUT=ROOT/'candidates/scalar-carrier12'
PARENT_SHA='910533b0f8e55149a0ec0f7057ff15defdf1b911a61e4abc02a51ed009adb49f'
VARS=['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
FORMULAS=[
 ('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q2*q'),
 ('W0','12*w+4'),('X','q*W0'),('Y','(2*v+1)*q3'),('E','X*Y'),('a','E+Y'),
 ('H','4*a+3'),('Delta','a*a+H'),('F','(K0+W0)*C-z*qm'),
 ('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),('k','R+1+h*E'),
 ('eta','c-Y*k'),('zeta','k-eta'),('coneU','cone_A*F'),('coneV','cone_B*C'),
 ('G','coneU*coneV-(q-coneU-coneV)*(q-coneU-coneV)'),('Peta','eta*zeta'),
 ('err','t*t-G-Peta+1'),('Pair','G*Peta-err*err'),('Dg','(3*Pair-4)*s*s+1'),
 ('c2','c*c'),('I','s*r*c2'),('I2','I*I'),('strong','Delta*I2'),('Df','strong+1'),
 ('Q','Delta*strong'),('delta','Q-1'),('b','c-R+4*I*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),
 ('ell','X*Y*Y'),('L','ell*k'),('Dt','L*(L+k)+1'),
 ('K','X*(X+2*a*c)-1'),('H2','H*H'),('H3','H2*H'),('H5','H2*H3'),
 ('S','I*H5'),('S2','S*S'),('zcarrier','H*T+K'),('zc2','zcarrier*zcarrier'),
 ('zc3','zc2*zcarrier'),('Acarrier','(zc2+3*H2)*(zc3-19*H3)'),('center','S*n-Acarrier'),
 ('ra','9*S2*Df'),('rb','81*S2*Dt'),('re','729*S2*Dg'),('cn','S2*Cy')]


def need(ok,message):
 if not ok:raise ValueError(message)


def encoded(value):return(json.dumps(value,indent=2,sort_keys=True)+'\n').encode()
def digest(raw):return sha256(raw).hexdigest()


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


def circuit(integral):
 d=DAG();env={v:d.emit(['variable',v])for v in VARS}
 env.update({v:d.emit(['coefficient',v])for v in PORTS})
 for name,text in FORMULAS:env[name]=d.expression(text,env)
 if integral:env['cn']=d.expression('cn*delta',env)
 env['ndelta']=d.emit(['integer',1])if integral else env['delta']
 # Evaluate the cleared three-root norm in the quadratic algebra u^2=re,
 # at center-u, then take the final quadratic norm. No radical is emitted.
 tail=[('x2','center*center'),('t20','x2+re'),('t21','-2*center'),('ab','ra+rb'),
  ('q0','ndelta*(t20-ab)-cn'),('q1','ndelta*t21'),('tn','ndelta*ndelta*ra*rb'),
  ('rn','ndelta*cn'),('v0','q0*q0+re*q1*q1-4*(tn+rn*ab)'),('v1','2*q0*q1'),
  ('z64','64*tn*rn'),('n0','v0*v0+re*v1*v1-z64*t20'),
  ('n1','2*v0*v1-z64*t21'),('output','n0*n0-re*n1*n1')]
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
 return dict(schema='literal_integer_arithmetic_dag_v1',name='scalar_carrier12_'+('integral'if integral else'rational'),
  domain='unrestricted integers',variables=VARS,variable_count=12,nodes=nodes,named_registers=named,
  output=mapping[env['output']],operations=sum(counts.values()),operation_counts=counts,
  coefficient_binding='coefficients/BINDING.json',exact_degree=1456 if integral else 1200,
  syntactic_bound=degrees[mapping[env['output']]],variant='integral'if integral else'rational',
  parent_sha256=PARENT_SHA,ordinary_proof='PROOF.md',
  proof_status='Reviewed new ordinary zero-existence reduction via scalar intersective carrier, signed main folding and full-residue interpolation. No new native calibration, Lean or internal-ZFC endpoint.')


def build():
 raw=(PARENT/'integer12_degree2400.json').read_bytes();need(digest(raw)==PARENT_SHA,'actual frozen208 parent')
 parent=json.loads(raw);binding_path=PARENT/parent['coefficient_binding'];binding=json.loads(binding_path.read_bytes())
 files={'source/parent-equation.json':raw,'coefficients/BINDING.json':binding_path.read_bytes()}
 for p in binding['payloads'].values():files['coefficients/'+p['file']]=(binding_path.parent/p['file']).read_bytes()
 deps={
  'source/PRIME_TWELVE.md':PARENT/'source/proofs/PRIME_TWELVE.md',
  'source/INTERPOLATION12.md':PARENT/'source/proofs/INTERPOLATION12.md',
  'source/RESIDUE_AND_DETERMINANT.md':ROOT/'candidates/constructive-integer14-quadratic/source/RESIDUE_AND_DETERMINANT.md',
  'source/signed-quadratic-proof.md':ROOT/'candidates/constructive-integer14-quadratic/PROOF.md',
  'source/LICENSE.UPSTREAM':PARENT/'source/LICENSE.UPSTREAM',
  'source/independent_norm_oracle.py':ROOT/'candidates/constructive-integer14-quadratic/source/independent_norm_oracle.py'}
 for n,p in deps.items():files[n]=p.read_bytes()
 reports={}
 for integral in [False,True]:
  packet=circuit(integral);name='integral'if integral else'rational';files[name+'.json']=encoded(packet)
  reports[name]={k:packet[k]for k in ['operations','operation_counts','exact_degree','syntactic_bound']}
 files['SOURCE_PINS.json']=encoded(dict(parent_equation_sha256=PARENT_SHA,
  dependencies={n:{'repository_path':str(p.relative_to(ROOT)),'sha256':digest(files[n])}for n,p in deps.items()},
  parent_manifest_sha256=digest((PARENT/'MANIFEST.json').read_bytes()),
  coefficient_binding_source=str(binding_path.relative_to(ROOT))))
 files['BUILD.json']=encoded(dict(status='PASS',metrics=reports,generator_sha256=digest(Path(__file__).read_bytes()),
  sha256={n:digest(v)for n,v in files.items()}))
 return files,reports


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');args=ap.parse_args()
 files,reports=build()
 for n,data in files.items():
  p=OUT/n
  if args.check:need(p.read_bytes()==data,'exact rebuild '+n)
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 print(json.dumps(dict(status='PASS',check=args.check,metrics=reports),indent=2))


if __name__=='__main__':main()

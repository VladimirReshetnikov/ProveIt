#!/usr/bin/env python3
"""Independent exact audit of the root agent's CRT carrier graphs."""
from pathlib import Path
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json, ast, sys
HERE=Path(__file__).resolve().parent
TARGET=HERE.parent/'crt12'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
O=module('independent_crt_oracle',HERE.parent/'height12/source/independent_norm_oracle.py')
VARS=['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
FORMULAS=[('J','6*j+1'),('qm','beta*J'),('q','beta*J+1'),('W0','12*w+4'),('X','q*W0'),
 ('Y','q*v'),('a','(X+1)*Y'),('H','4*a+3'),('Delta','a*a+H'),
 ('F','(K0+W0)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('k','R+1+h*X*Y'),('eta','c-Y*k'),('zeta','k-eta'),
 ('coneU','cone_A*F'),('coneV','cone_B*C'),('G','coneU*coneV-(q-coneU-coneV)*(q-coneU-coneV)'),
 ('Peta','eta*zeta'),('err','t*t-G-Peta+1'),('Pair','G*Peta-err*err'),('Dg','(3*Pair-4)*s*s+1'),
 ('I','s*r*c*c'),('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),
 ('V','Df*(c-R+4*I*T)-c'),('Cy','Q*V*V-1'),('ell','X*Y*Y'),('Dt','1+ell*(ell+1)*k*k'),
 ('K','X*(2*X-3*c)-2'),('M','2*q*q'),('D','M*H'),('S','s*r*M*M*M*M*M*H'),
 ('Ccarrier','M*K+H*(v-q*q)'),('zcarrier','D*T+Ccarrier'),
 ('Acarrier','(zcarrier*zcarrier+3*D*D)*(zcarrier*zcarrier*zcarrier-19*D*D*D)'),
 ('U','S*n-Acarrier'),('ra','9*S*S*Df'),('rb','81*S*S*Dt'),('re','729*S*S*Dg'),
 ('cn','S*S*Cy'),('SV','S*V'),('Lc','SV*delta')]

def prefix(p,integral):
 defs=[(n,t)for n,t in FORMULAS if not(integral and n in ['Cy','cn'])]
 defs += [('Ns','S*S*delta-Lc*SV'),('cn','Lc*Lc-Ns'),('center','U+Lc')]if integral else [('Ns','S*S-SV*SV'),('center','U+SV')]
 nodes=p['nodes'];nm=p['named_registers'];covered=set();records=[]
 for name,formula in defs:
  tree=ast.parse(formula,mode='eval').body
  refs=sorted({n.id for n in ast.walk(tree)if isinstance(n,ast.Name)})
  need(len(refs)<=6,'local cut width')
  cache={nm[x]:O.variable(i)for i,x in enumerate(refs)}
  symbols={x:O.variable(i)for i,x in enumerate(refs)}
  def actual(i):
   covered.add(i)
   if i in cache:return cache[i]
   row=nodes[i]
   if row[0]=='integer':v=O.Poly(row[1])
   else:
    need(row[0]in['add','sub','mul'],'unbound prefix leaf')
    a,b=actual(row[1]),actual(row[2]);v=a+b if row[0]=='add'else a-b if row[0]=='sub'else a*b
   cache[i]=v;return v
  def expected(n):
   if isinstance(n,ast.Name):return symbols[n.id]
   if isinstance(n,ast.Constant):return O.Poly(n.value)
   a,b=expected(n.left),expected(n.right)
   return a+b if isinstance(n.op,ast.Add)else a-b if isinstance(n.op,ast.Sub)else a*b
  need(actual(nm[name]).t==expected(tree).t,'exact front identity '+name)
  records.append(name)
 missing=[i for i in range(nm['x2'])if nodes[i][0]in['add','sub','mul']and i not in covered]
 need(not missing,'unbound live prefix arithmetic '+str(missing))
 return records

def substitute(poly,replacements):
 result=O.Poly(0);powers={}
 for mon,coefficient in poly.t.items():
  term=O.Poly(coefficient)
  for i,k in enumerate(mon):
   if(i,k)not in powers:powers[i,k]=replacements[i]**k
   term=term*powers[i,k]
  result=result+term
 return result

def norm(p,integral):
 O.ZERO=(0,)*7
 def var(i):
  m=[0]*7;m[i]=1;return O.Poly({tuple(m):1})
 U,V,N,a,b,e,delta=[var(i)for i in range(7)]
 if integral:
  z=U+V;cn=V*V-N;Lc=V
 else:
  z=U+V;cn=delta*V*V-N;Lc=delta*V
 nm=p['named_registers'];nodes=p['nodes'];vals={i:O.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
 for n,v in [('U',U),('SV',V),('Lc',Lc),('Ns',N),('center',z),('ra',a),('rb',b),('re',e),('cn',cn)]:vals[nm[n]]=v
 if not integral:vals[nm['ndelta']]=delta
 for i in range(nm['x2'],len(nodes)):
  r=nodes[i]
  if r[0]=='integer':continue
  need(all(x in vals for x in r[1:]),'all norm operands cut')
  l,rr=vals[r[1]],vals[r[2]];vals[i]=l+rr if r[0]=='add'else l-rr if r[0]=='sub'else l*rr
 x=var(0)
 if integral:generic=O.norm_oracle(x,[var(1),var(2),var(3),var(4)])
 else:
  generic=var(5)**8*O.norm_oracle(x,[var(1),var(2),var(3),O.Poly({(0,0,0,0,1,-1,0):1})])
 want=substitute(generic,[z,a,b,e,cn,delta,O.Poly(0)])
 need(vals[p['output']].t==want.t,'entire generic centered norm identity')
 terms=len(want.t);O.ZERO=(0,)*6
 return terms

def degree(p,integral):
 order=['T','j','w','v','s','r','c','C','z','h','n','t'];vals=[]
 def key(m):return(sum(m),)+m
 for row in p['nodes']:
  if row[0]=='variable':
   m=[0]*12;m[order.index(row[1])]=1;v=(tuple(m),O.Poly(1))
  elif row[0]=='coefficient':v=((0,)*12,O.variable(PORTS.index(row[1])))
  elif row[0]=='integer':v=((0,)*12,O.Poly(row[1]))
  else:
   a,b=vals[row[1]],vals[row[2]]
   if row[0]=='mul':v=(tuple(i+j for i,j in zip(a[0],b[0])),a[1]*b[1])
   elif key(a[0])>key(b[0]):v=a
   elif key(b[0])>key(a[0]):v=(b[0],-b[1]if row[0]=='sub'else b[1])
   else:v=(a[0],a[1]-b[1]if row[0]=='sub'else a[1]+b[1])
   need(v[1].t,'nonzero leading at every gate')
  vals.append(v)
 m,c=vals[p['output']]
 expected={'j':320,'w':80,'v':80,'s':80,'r':80,'c':128,'T':16}if integral else{'j':352,'w':96,'v':96,'s':48,'r':48,'c':80,'T':48}
 coef=O.Poly(2**624*3**400)*O.variable(0)**320 if integral else O.Poly(2**744*3**448)*O.variable(0)**352
 need(m==tuple(expected.get(n,0)for n in order)and c.t==coef.t,'exact claimed actual leading coefficient')
 need(sum(m)==p['exact_degree']==(784 if integral else 768),'exact degree')
 return dict(exact_degree=sum(m),leading_monomial=expected,coefficient='2^624*3^400*beta^320'if integral else'2^744*3^448*beta^352')

def main():
 results={}
 for integral in[False,True]:
  name='integral'if integral else'rational';raw=(TARGET/(name+'.json')).read_bytes();p=json.loads(raw)
  counts=dict(Counter(r[0]for r in p['nodes']if r[0]in['add','sub','mul']))
  need(counts==({'add':29,'mul':97,'sub':28}if integral else{'add':29,'mul':104,'sub':28}),'actual operation count')
  need(p['variables']==VARS and p['variable_count']==12,'twelve named variables')
  result=dict(sha256=sha256(raw).hexdigest(),counts=counts,operations=sum(counts.values()),prefix_registers=prefix(p,integral),free_norm_coefficients=norm(p,integral))
  result.update(degree(p,integral));results[name]=result
 report=dict(status='PASS',optimized=bool(sys.flags.optimize),variants=results,scope='Independent full prefix cut identities, generic centered conjugate product, and every-gate exact leading induction; no builder import.')
 out=HERE/('CRT_CHECK_OPTIMIZED.json'if sys.flags.optimize else'CRT_CHECK.json');out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()

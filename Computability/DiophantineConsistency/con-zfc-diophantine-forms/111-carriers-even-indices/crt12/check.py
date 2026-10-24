#!/usr/bin/env python3
"""Independent whole-formula and free four-root norm check for scalar-carrier12."""
import argparse
import ast
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import gzip
import importlib.util
import json
from pathlib import Path
import random
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=HERE/'source'
VARIABLES=['j','C','z','h','r','v','w','T','c','n','t','s']
COEFFICIENTS=['beta','K0','MC','MF','cone_A','cone_B']
# Separate mathematical transcription, independent of the producer schedule.
FORMULAS=[('J','6*j+1'),('qm','beta*J'),('q','beta*J+1'),('W','12*w+4'),('X','q*W'),
 ('Y','q*v'),('a','(X+1)*Y'),('H','4*a+3'),('Delta','a*a+H'),
 ('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),
 ('k','R+1+h*X*Y'),('eta','c-Y*k'),('zeta','k-eta'),
 ('cu','cone_A*F'),('cv','cone_B*C'),('G','cu*cv-(q-cu-cv)*(q-cu-cv)'),
 ('Pe','eta*zeta'),('err','t*t-G-Pe+1'),('Pair','G*Pe-err*err'),('Dg','(3*Pair-4)*s*s+1'),
 ('I','s*r*c*c'),('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),
 ('V','Df*(c-R+4*I*T)-c'),('Cy','Q*V*V-1'),
 ('ell','X*Y*Y'),('Dt','1+ell*(ell+1)*k*k'),('K','X*(2*X-3*c)-2'),
 ('M','2*q*q'),('D','M*H'),('S','s*r*M*M*M*M*M*H'),
 ('Ccarrier','M*K+H*(v-q*q)'),('zc','D*T+Ccarrier'),
 ('Ac','(zc*zc+3*D*D)*(zc*zc*zc-19*D*D*D)'),('center','S*n-Ac'),
 ('ra','9*S*S*Df'),('rb','81*S*S*Dt'),('re','729*S*S*Dg'),('cn','S*S*Cy')]


def need(ok,text):
 if not ok:raise ValueError(text)
def digest(raw):return sha256(raw).hexdigest()
def load(name):return json.loads((HERE/name).read_bytes())
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def evaluate(packet,inputs,p):
 vals=[]
 for r in packet['nodes']:
  if r[0]=='integer':v=r[1]
  elif r[0]in ['variable','coefficient']:v=inputs[r[1]]
  else:
   a,b=vals[r[1]],vals[r[2]];v=a+b if r[0]=='add'else a-b if r[0]=='sub'else a*b
  vals.append(v%p)
 return vals


def prefix_check(packet,oracle):
 centered=True
 integral=packet['auxiliary_variant']=='integral'
 form=[(n,t)for n,t in FORMULAS[:-1]if n!='Cy'] if integral else FORMULAS
 if integral:form=form+[('SV','S*V'),('Lc','SV*delta'),('Ns','S*S*delta-Lc*SV'),('cn','Lc*Lc-Ns'),('center','U+Lc')]
 else:form=form+[('SV','S*V'),('Lc','SV*delta'),('Ns','S*S-SV*SV'),('center','U+SV')]

 """Prove every mathematical register by an independent local ring cut."""
 aliases={'W':'W0','cu':'coneU','cv':'coneV','Pe':'Peta','Ac':'Acarrier','zc':'zcarrier'}
 nodes=packet['nodes'];nm=packet['named_registers'];covered=set();proofs=[]
 for name,text in form:
  tree=ast.parse(text,mode='eval').body
  refs=sorted({n.id for n in ast.walk(tree)if isinstance(n,ast.Name)})
  need(len(refs)<=6,'independent six-port local cut')
  cuts={nm[aliases.get(v,v)]:oracle.variable(j)for j,v in enumerate(refs)}
  symbols={v:oracle.variable(j)for j,v in enumerate(refs)}
  cache=dict(cuts)
  def actual(i):
   covered.add(i)
   if i in cache:return cache[i]
   r=nodes[i]
   if r[0]=='integer':out=oracle.Poly(r[1])
   else:
    need(r[0]in ['add','sub','mul'],'no unbound prefix leaf '+str(r))
    a,b=actual(r[1]),actual(r[2]);out=a+b if r[0]=='add'else a-b if r[0]=='sub'else a*b
   cache[i]=out;return out
  def expected(n):
   if isinstance(n,ast.Name):return symbols[n.id]
   if isinstance(n,ast.Constant):return oracle.Poly(n.value)
   if isinstance(n,ast.BinOp):
    a,b=expected(n.left),expected(n.right)
    return a+b if isinstance(n.op,ast.Add)else a-b if isinstance(n.op,ast.Sub)else a*b
   raise ValueError('nonpolynomial independent formula')
  target=nm['U']if centered and name=='center'and text=='S*n-Ac'else nm[aliases.get(name,name)]
  # Integral cn includes an additional delta. Check its original product
  # as a local subexpression, then verify that final extra factor below.
  if name=='cn'and packet['variant']=='uncentered_integral':
   row=nodes[target];need(row[0]=='mul'and nm['delta']in row[1:],'integral cn extra delta')
   covered.add(target);target=row[2]if row[1]==nm['delta']else row[1]
  need(actual(target).t==expected(tree).t,'entire mathematical register '+name)
  proofs.append(dict(register=name,free_cuts=refs))
 # Coverage of all live prefix arithmetic is checked in addition to
 # individual register identities; norm constants may be introduced here.
 missing=[i for i in range(nm['x2'])if nodes[i][0]in ['add','sub','mul']and i not in covered]
 need(not missing,'all prefix arithmetic covered '+str(missing))
 return dict(complete_local_ring_cuts=proofs,prefix_arithmetic_covered=True)


def tail_check(packet,oracle,integral):
 nm=packet['named_registers'];nodes=packet['nodes']
 x,a,b,e,c,delta=[oracle.variable(i)for i in range(6)]
 env={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
 for name,value in [('center',x),('ra',a),('rb',b),('re',e),('cn',c)]:env[nm[name]]=value
 if not integral:env[nm['ndelta']]=delta
 for i in range(nm['x2'],len(nodes)):
  row=nodes[i]
  if row[0]=='integer':continue
  need(all(j in env for j in row[1:]),'all four-root norm cut operands bound')
  aa,bb=env[row[1]],env[row[2]]
  env[i]=aa+bb if row[0]=='add'else aa-bb if row[0]=='sub'else aa*bb
 if integral:expected=oracle.norm_oracle(x,[a,b,e,c])
 else:
  fraction=oracle.Poly({(0,0,0,0,1,-1):1})
  expected=delta**8*oracle.norm_oracle(x,[a,b,e,fraction])
 need(env[packet['output']].t==expected.t and len(expected.t)==495,'entire495-term cleared four-root norm')
 return dict(free_norm_coefficients=len(expected.t),all_norm_cuts_bound=True)



def centered_tail_check(packet,oracle):
 """Free U,L,N,a,b,e identity, without importing the producer."""
 nm=packet['named_registers'];nodes=packet['nodes']
 U,L,N,a,b,e=[oracle.variable(i)for i in range(6)]
 z=U+L;d=L*L-N
 env={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
 for name,value in [('U',U),('Lc',L),('Ns',N),('center',z),('ra',a),('rb',b),('re',e),('cn',d)]:env[nm[name]]=value
 for i in range(nm['x2'],len(nodes)):
  row=nodes[i]
  if row[0]=='integer':continue
  need(all(j in env for j in row[1:]),'all centered norm operands bound')
  aa,bb=env[row[1]],env[row[2]]
  env[i]=aa+bb if row[0]=='add'else aa-bb if row[0]=='sub'else aa*bb
 generic=oracle.norm_oracle(oracle.variable(0),[oracle.variable(i)for i in [1,2,3,4]])
 replacements=[z,a,b,e,d,oracle.Poly(0)];expected=oracle.Poly(0);powers={}
 for mon,coefficient in generic.t.items():
  term=oracle.Poly(coefficient)
  for i,k in enumerate(mon):
   if (i,k)not in powers:powers[i,k]=replacements[i]**k
   term=term*powers[i,k]
  expected=expected+term
 need(env[packet['output']].t==expected.t,'complete free centered four-root norm')
 return dict(free_centered_norm_coefficients=len(expected.t),all_norm_cuts_bound=True)

def rational_centered_tail_check(packet,oracle):
 """Prove the centered cut locally, then the entire free495-term norm."""
 nm=packet['named_registers'];nodes=packet['nodes']
 U,P,N,d,e,ab=[oracle.variable(i) for i in range(6)]
 env={i:oracle.Poly(r[1]) for i,r in enumerate(nodes) if r[0]=='integer'}
 for name,value in [('U',U),('SV',P),('Lc',d*P),('Ns',N),('delta',d),('ndelta',d),('re',e),('ab',ab)]:env[nm[name]]=value
 def cut(i):
  if i in env:return env[i]
  row=nodes[i];need(row[0]in ['add','sub','mul'],'centered rational local cut')
  a,b=cut(row[1]),cut(row[2]);out=a+b if row[0]=='add'else a-b if row[0]=='sub'else a*b
  env[i]=out;return out
 expected=d*((U+P)*(U+P)+e-ab)-(d*P*P-N)
 need(cut(nm['q0']).t==expected.t,'rational center identity at all six free cuts')
 # The preceding identity licenses this single q0 cut in the whole norm.
 x,a,b,e,c,d=[oracle.variable(i) for i in range(6)]
 env={i:oracle.Poly(r[1]) for i,r in enumerate(nodes) if r[0]=='integer'}
 for name,value in [('center',x),('ra',a),('rb',b),('re',e),('cn',c),('ndelta',d),('delta',d)]:env[nm[name]]=value
 env[nm['q0']]=d*(x*x+e-a-b)-c
 # Nodes private to the already-proved centered q0 are intentionally
 # hidden behind that exact local identity, rather than used as axioms.
 needed=set();todo=[packet['output']]
 while todo:
  i=todo.pop()
  if i in needed or i in env:continue
  needed.add(i);todo.extend(nodes[i][1:])
 for i in sorted(needed):
  row=nodes[i];need(row[0]in ['add','sub','mul'] and all(j in env for j in row[1:]),'free cleared norm binding')
  aa,bb=env[row[1]],env[row[2]];env[i]=aa+bb if row[0]=='add'else aa-bb if row[0]=='sub'else aa*bb
 fraction=oracle.Poly({(0,0,0,0,1,-1):1})
 original=d**8*oracle.norm_oracle(x,[a,b,e,fraction])
 need(env[packet['output']].t==original.t and len(original.t)==495,'full495-term rational norm after exact center cut')
 return dict(free_norm_coefficients=495,center_cut_universal=True,all_norm_cuts_bound=True)

def topology(packet,integral):
 nodes=packet['nodes'];live=set();todo=[packet['output']];degs=[]
 for i,r in enumerate(nodes):
  if r[0]in ['add','sub','mul']:
   need(len(r)==3 and all(type(j)is int and 0<=j<i for j in r[1:]),'acyclic operation')
   degs.append(degs[r[1]]+degs[r[2]]if r[0]=='mul'else max(degs[r[1]],degs[r[2]]))
  else:degs.append(1 if r[0]=='variable'else 0)
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0]in ['add','sub','mul']:todo.extend(nodes[i][1:])
 need(live==set(range(len(nodes))),'every node live')
 need([r[1]for r in nodes if r[0]=='variable']==VARIABLES,'all twelve variables live')
 need([r[1]for r in nodes if r[0]=='coefficient']==COEFFICIENTS,'all six coefficient ports live')
 counts=dict(Counter(r[0]for r in nodes if r[0]in ['add','sub','mul']))
 expected={'mul':97 if integral else 104,'add':29,'sub':28}
 need(counts==expected==packet['operation_counts']and sum(counts.values())==packet['operations'],'literal full-circuit count')
 need(degs[packet['output']]==packet['syntactic_bound']==(784 if integral else 768),'whole DAG degree upper bound')
 return dict(nodes=len(nodes),operations=sum(counts.values()),operation_counts=counts,degree_upper=degs[packet['output']])


def leading(packet,oracle,integral):
 """Exact graded-lex leading induction in all six formal coefficient ports."""
 order=['T','j','w','v','s','r','c','C','z','h','n','t'];values=[]
 def key(mon):return(sum(mon),)+mon
 for row in packet['nodes']:
  if row[0]=='variable':
   ex=[0]*12;ex[order.index(row[1])]=1;v=(tuple(ex),oracle.Poly(1))
  elif row[0]=='coefficient':v=((0,)*12,oracle.variable(COEFFICIENTS.index(row[1])))
  elif row[0]=='integer':v=((0,)*12,oracle.Poly(row[1]))
  else:
   a,b=values[row[1]],values[row[2]]
   if row[0]=='mul':v=(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
   elif key(a[0])>key(b[0]):v=a
   elif key(b[0])>key(a[0]):v=(b[0],-b[1]if row[0]=='sub'else b[1])
   else:v=(a[0],a[1]-b[1]if row[0]=='sub'else a[1]+b[1])
   need(bool(v[1].t),'noncancelling exact leading coefficient at every gate')
  values.append(v)
 ex,coef=values[packet['output']]
 want_ex={'j':320,'w':80,'v':80,'s':80,'r':80,'c':128,'T':16}if integral else{'j':352,'w':96,'v':96,'s':48,'r':48,'c':80,'T':48}
 want_coef=oracle.Poly((2**624)*(3**400))*oracle.variable(0)**320 if integral else oracle.Poly((2**744)*(3**448))*oracle.variable(0)**352
 need(ex==tuple(want_ex.get(n,0)for n in order)and coef.t==want_coef.t,'exact actual-DAG distinguished leading coefficient')
 need(sum(ex)==(784 if integral else 768),'attained exact degree')
 return dict(exact_degree=sum(ex),graded_lex_variable_order=order,all_node_leading_inductions_nonzero=True,
  monomial=want_ex,coefficient='2^624*3^400*beta^320'if integral else'2^744*3^448*beta^352')


def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
 # The frozen parent and dependency bytes are authenticated separately below.
 binding=load('coefficients/BINDING.json');ports={};auth={}
 for name,pin in binding['payloads'].items():
  blob=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(blob)
  need(digest(raw)==pin['raw_sha256']and len(raw)==pin['raw_bytes'],'whole coefficient '+name)
  ports[name]=int.from_bytes(raw,'little');need(ports[name].bit_length()==pin['bits'],'coefficient bit width')
  auth[name]=dict(raw_sha256=digest(raw),bits=pin['bits'])
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'three closed constants')
 oracle=module('scalar12_independent_free_norm_oracle',HERE/'source/independent_norm_oracle.py')
 results={};rejections=[]
 for name in ['rational','integral']:
  integral=name!='rational';packet=load(name+'.json')
  result=topology(packet,integral);result.update(prefix_check(packet,oracle));result.update(centered_tail_check(packet,oracle)if integral else rational_centered_tail_check(packet,oracle))
  result['actual_dag_leading_certificate']=leading(packet,oracle,integral)
  for target,checker in [('K',lambda p:prefix_check(p,oracle)),('Acarrier',lambda p:prefix_check(p,oracle)),('output',lambda p:centered_tail_check(p,oracle)if integral else rational_centered_tail_check(p,oracle))]:
   bad=deepcopy(packet);idx=packet['named_registers'][target];bad['nodes'][idx][0]='add'
   try:checker(bad)
   except ValueError:rejections.append(name+':'+target)
   else:raise ValueError('false projection/carrier/norm mutation accepted')
  results[name]=result
 report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),variants=results,whole_six_ports=auth,rejected_mutations=rejections,
  ordinary_proof_sha256=digest((HERE/'PROOF.md').read_bytes()),
  scope='Complete prefix free-ring binding, authentic six-port bytes, entire free495-term norm and actual-DAG noncancelling graded-lex leading induction. The separate peer/CRT_PEER_REVIEW.md records an independent ordinary-proof review. This receipt checks finite algebra, not that unbounded proof; no new Lean formalization.')
 text=json.dumps(report,indent=2,sort_keys=True)+'\n'
 if args.output:args.output.write_text(text)
 print(text,end='')


if __name__=='__main__':main()

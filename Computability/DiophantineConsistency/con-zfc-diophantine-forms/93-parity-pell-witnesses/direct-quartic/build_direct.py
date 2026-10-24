#!/usr/bin/env python3
"""Explicit direct-Horn Diophantine compiler. Python standard library only.
All nodes denote nonnegative integer expressions. No upstream code is executed.
Output is a literal finite sparse quartic SOS, not an MRDP oracle or choice recipe.
"""
import json, pathlib, hashlib, collections
ROOT=pathlib.Path(__file__).resolve().parent
class Compiler:
 def __init__(self): self.nodes=[];self.cache={};self.vars=[];self.eqs=[];self.calls=collections.Counter();self.ledger=[]
 def node(self,t):
  t=tuple(t)
  if t not in self.cache:self.cache[t]=len(self.nodes);self.nodes.append(t)
  return self.cache[t]
 def c(self,n): assert n>=0;return self.node(('c',n))
 def var(self,label):
  k=len(self.vars);self.vars.append(label);return self.node(('v',k))
 def fresh(self,label):return self.var(label+'.'+str(len(self.vars)))
 def add(self,a,b):
  if a==self.c(0):return b
  if b==self.c(0):return a
  if self.nodes[a][0]==self.nodes[b][0]=='c':return self.c(self.nodes[a][1]+self.nodes[b][1])
  return self.node(('a',*sorted((a,b))))
 def mul(self,a,b):
  if a==self.c(0) or b==self.c(0):return self.c(0)
  if a==self.c(1):return b
  if b==self.c(1):return a
  if self.nodes[a][0]==self.nodes[b][0]=='c':return self.c(self.nodes[a][1]*self.nodes[b][1])
  return self.node(('m',*sorted((a,b))))
 def addc(self,a,n):return self.add(a,self.c(n))
 def prod(self,xs):
  r=self.c(1)
  for a in xs:r=self.mul(r,a)
  return r
 def sum(self,xs):
  r=self.c(0)
  for a in xs:r=self.add(r,a)
  return r
 def signed(self,a):return (a,self.c(0))
 def diff(self,a,b):return (a,b)
 def iadd(self,p,q):return(self.add(p[0],q[0]),self.add(p[1],q[1]))
 def imul(self,p,q):return(self.add(self.mul(p[0],q[0]),self.mul(p[1],q[1])),self.add(self.mul(p[0],q[1]),self.mul(p[1],q[0])))
 def isum(self,ps):
  r=self.signed(self.c(0))
  for p in ps:r=self.iadd(r,p)
  return r
 def iprod(self,ps):
  r=self.signed(self.c(1))
  for p in ps:r=self.imul(r,p)
  return r
 def sos(self,rs):return self.isum([self.imul(r,r) for r in rs])
 def eq(self,a,b,label):self.eqs.append((a,b,label))
 def assertpoly(self,p,label):self.eq(*p,label)
 def le(self,a,b,label):return self.diff(b,self.add(a,self.fresh(label+'.slack')))
 def lt(self,a,b,label):return self.le(self.addc(a,1),b,label)
 def mod(self,a,b,m,label):return self.diff(self.add(a,self.mul(m,self.fresh(label+'.q0'))),self.add(b,self.mul(m,self.fresh(label+'.q1'))))
 def norm(self,a,x,y):
  return self.diff(self.add(self.mul(x,x),self.mul(y,y)),self.addc(self.prod([a,a,y,y]),1))
 def pell(self,a,n,x,y):
  self.calls['pell']+=1
  u,w,s,t,b=[self.fresh('pell.'+j) for j in ['u','w','s','t','b']]
  rs=[self.norm(a,x,y),self.norm(a,u,w),self.norm(b,s,t),self.lt(self.c(1),b,'pell.b'),self.mod(b,self.c(1),self.mul(self.c(4),y),'pell.by'),self.mod(b,a,u,'pell.ba'),self.lt(self.c(0),w,'pell.w'),self.diff(w,self.prod([y,y,self.fresh('pell.dvd')])),self.mod(s,x,u,'pell.sx'),self.mod(t,n,self.mul(self.c(4),y),'pell.tn')]
  base=self.sos([self.diff(x,self.c(1)),self.diff(y,self.c(0))])
  finite=self.sos(rs)
  return self.iadd(self.sos([self.lt(self.c(1),a,'pell.a'),self.le(n,y,'pell.n')]),self.imul(base,finite))
 def pow(self,n,k):
  self.calls['power']+=1
  m=self.fresh('power.output')
  w,a,t,z,x,y=[self.fresh('power.'+j) for j in ['w','a','t','z','x','y']]
  # Finite-branch descent: a>1 and the final norm force a>w>=n.
  # Thus the inherited truncated difference is exactly a-n. Move y*n
  # across the congruence, eliminating both difference and sign-slack inputs.
  finite=self.isum([self.pell(a,k,x,y),self.sos([
   self.mod(self.add(x,self.mul(y,n)),self.add(self.mul(y,a),m),t,'power.mod'),
   self.diff(self.prod([self.c(2),a,n]),self.addc(self.add(t,self.mul(n,n)),1)),
   self.lt(m,t,'power.mt'),self.le(n,w,'power.nw'),self.le(k,w,'power.kw'),self.norm(self.addc(w,1),a,self.mul(w,z))])])
  zero=self.sos([self.diff(k,self.c(0)),self.diff(m,self.c(1))])
  zero_base=self.sos([self.diff(n,self.c(0)),self.diff(m,self.c(0))])
  posbase=self.iadd(self.sos([self.lt(self.c(0),n,'power.n')]),finite)
  posexp=self.iadd(self.sos([self.lt(self.c(0),k,'power.k')]),self.imul(zero_base,posbase))
  self.assertpoly(self.imul(zero,posexp),'natural power')
  return m
 def divmod(self,n,d):
  self.calls['divmod']+=1
  q,r,s=[self.fresh('division.'+j) for j in ['quotient','remainder','slack']]
  self.eq(n,self.add(self.mul(q,d),r),'division equation')
  self.eq(d,self.addc(self.add(r,s),1),'positive divisor/remainder bound')
  return q,r
 def choose(self,n,k):
  self.calls['binomial']+=1
  q=self.addc(self.pow(self.c(2),n),1)
  num=self.pow(self.addc(q,1),n);den=self.pow(q,k)
  div,_=self.divmod(num,den)
  _,r=self.divmod(div,q)
  return r
 def fact(self,n):
  self.calls['factorial']+=1
  shift=self.addc(n,2);r=self.pow(shift,shift)
  c=self.choose(self.add(r,n),n)
  cm=self.fresh('factorial.choose_minus_one');self.eq(c,self.addc(cm,1),'positive binomial predecessor')
  q,_=self.divmod(self.add(self.pow(self.addc(r,1),n),cm),c)
  return q
 def evalpoly(self,terms,v):
  pos=[];neg=[]
  for t in terms:
   p=self.prod([self.c(abs(t['coefficient']))]+[v[x] for x in t['monomial']])
   (pos if t['coefficient']>0 else neg).append(p)
  return(self.sum(pos),self.sum(neg))
 def evaldag(self,dag,env,root):
  vals=[]
  for n in dag:
   if n[0]=='v':v=env[n[1]]
   elif n[0]=='c':v=self.c(n[1])
   elif n[0]=='a':v=self.add(vals[n[1]],vals[n[2]])
   else:v=self.mul(vals[n[1]],vals[n[2]])
   vals.append(v)
  return vals[root]

def record_method(name, method):
 def wrap(self,*args):
  before=(len(self.vars),len(self.eqs),len(self.nodes)); result=method(self,*args)
  self.ledger.append({'kind':name,'arguments':args,'result':result,'before':before,'after':(len(self.vars),len(self.eqs),len(self.nodes))})
  return result
 return wrap
for method_name in ['pow','pell','divmod','choose','fact']:
 setattr(Compiler,method_name,record_method(method_name,getattr(Compiler,method_name)))

def row_source(horn):
 c=Compiler();outer={s:c.var(s) for s in ['N','x','y','m','M0','i']}
 v={s:c.var(s) for s in ['p','q','v']+horn['base_witnesses']+['q'+str(i) for i in range(horn['common_wire_count'])]}
 rem=[];rs=[]
 for index in ['i','next']:
  r,quo,slack=[c.var('x.'+index+'.'+s) for s in ['remainder','quotient','slack']]
  ix=outer['i'] if index=='i' else c.addc(outer['i'],1)
  modulus=c.addc(c.mul(c.addc(ix,1),outer['y']),1)
  rs += [c.diff(outer['x'],c.add(c.mul(quo,modulus),r)),c.diff(modulus,c.addc(c.add(r,slack),1))]
  rem.append(r)
 for lab in ['p','q','v']:
  rs.append(c.diff(outer['m'],c.add(v[lab],c.var(lab+'.upper_slack'))))
 S,Sp=rem;M=c.addc(outer['M0'],1)
 rs.append(c.diff(c.mul(Sp,c.addc(c.mul(v['v'],M),1)),c.prod([S,c.addc(c.mul(v['p'],M),1),c.addc(c.mul(v['q'],M),1)])))
 branches=[c.sos([c.evalpoly(r,v) for r in b['quadratic_residuals']]) for b in horn['branches']]
 P=c.iadd(c.iprod(branches),c.sos(rs))
 assert len(c.vars)==35 and len(c.eqs)==0
 return c,P

def build():
 horn=json.loads((ROOT/'horn_shared_source.json').read_text())
 row,P=row_source(horn)
 c=Compiler();N,x,y,m,M0=[c.var(s) for s in ['N','x','y','m','M0']]
 D=c.c(2)
 height_exponent=c.addc(c.prod([c.c(2),m,N]),1)
 height_power=c.pow(D,height_exponent)
 c.eq(M0,height_power,'uniform binary height')
 endpoints=[]
 # Endpoints use the same strictly positive beta moduli.
 for code,ix,want in [(x,c.c(0),c.addc(M0,2)),(x,N,c.c(1))]:
  _,r=c.divmod(code,c.addc(c.mul(c.addc(ix,1),y),1));c.eq(r,want,'beta endpoint');endpoints.append({'code':code,'index':ix,'remainder':r,'target':want})
 # One common coordinate bound U replaces 29 separate bounds.
 U=c.var('uniform row witness bound');a=[c.var('encoded row coordinate '+str(j)) for j in range(29)];idx=c.var('encoded row index')
 outer=[N,x,y,m,M0]
 env_upper=outer+[N]+[U]*29
 eu=c.evaldag(row.nodes,env_upper,P[0]);fu=c.evaldag(row.nodes,env_upper,P[1])
 T=c.fact(c.sum([eu,fu,N]))
 Q=c.addc(c.pow(c.addc(c.mul(c.addc(N,1),T),1),N),2)
 tn=c.pow(T,N);nf=c.fact(N);ch=c.choose(c.add(Q,N),N)
 modulus=c.fresh('CRT.product_modulus');c.eq(c.mul(T,Q),c.addc(modulus,1),'CRT positive modulus predecessor')
 _,B=c.divmod(c.prod([tn,nf,ch]),modulus)
 F=c.fact(c.addc(U,1))
 for ai in a:
  choose=c.choose(ai,c.addc(U,1))
  c.eq(c.mul(F,choose),c.mul(B,c.fresh('coordinate divisibility quotient')),'falling-factorial coordinate certificate')
 c.eq(c.addc(c.mul(c.addc(idx,1),T),1),c.mul(B,c.fresh('index divisibility quotient')),'encoded row index')
 env_enc=outer+[idx]+a
 ee=c.evaldag(row.nodes,env_enc,P[0]);fe=c.evaldag(row.nodes,env_enc,P[1])
 c.assertpoly(c.mod(ee,fe,B,'row evaluation'),'encoded row evaluation congruence')
 encoded_coordinates=a
 # Every arithmetic node gets a natural wire; equality residuals and circuit residuals are squared.
 polynomial=[];node_variables={};input_count=len(c.vars);nextvar=input_count
 for i,n in enumerate(c.nodes):
  if n[0]=='v':node_variables[i]=n[1]
  elif n[0] in ('a','m'):node_variables[i]=nextvar;nextvar+=1
 def term(i):
  n=c.nodes[i]
  return ({():n[1]} if n[0]=='c' else {(node_variables[i],):1})
 def plus(a,b,s=1):
  r=dict(a)
  for k,v in b.items():r[k]=r.get(k,0)+s*v
  return{k:v for k,v in r.items() if v}
 def times(a,b):
  r={}
  for ka,va in a.items():
   for kb,vb in b.items():
    k=tuple(sorted(ka+kb));r[k]=r.get(k,0)+va*vb
  return{k:v for k,v in r.items() if v}
 def enc(p):return [[v,list(k)] for k,v in sorted(p.items())]
 for i,n in enumerate(c.nodes):
  if n[0] in ('a','m'):
   rhs=plus(term(n[1]),term(n[2])) if n[0]=='a' else times(term(n[1]),term(n[2]))
   polynomial.append({'label':'gate '+str(i),'terms':enc(plus(term(i),rhs,-1))})
 for a,b,label in c.eqs:polynomial.append({'label':label,'terms':enc(plus(term(a),term(b),-1))})
 sparse={}
 for r in polynomial:
  p={tuple(k):v for v,k in r['terms']}
  for mon,coef in times(p,p).items():sparse[mon]=sparse.get(mon,0)+coef
 sparse={k:v for k,v in sparse.items() if v}
 artifact={'format':'ordinary-polynomial-sparse-v1','domain':'nonnegative integers','variable_count':nextvar,'terms':enc(sparse)}
 recipe={'format':'natural-arithmetic-dag-v1','variable_names':c.vars,'nodes':c.nodes,'equalities':c.eqs,'uniform_bound':True,'call_ledger':c.ledger,'source_binding':{'upper_environment':env_upper,'encoded_environment':env_enc,'upper_e':eu,'upper_f':fu,'encoded_e':ee,'encoded_f':fe,'U':U,'encoded_coordinates':encoded_coordinates,'index':idx,'T':T,'Q':Q,'B':B,'modulus':modulus,'F':F,'endpoints':endpoints,'max_label':m,'geometric_base':D,'height_exponent':height_exponent,'height_power':height_power}}
 summary={'domain':'nonnegative integers','ordinary_polynomial_degree':max(map(len,sparse)),'ordinary_polynomial_variables':nextvar,'ordinary_polynomial_monomials':len(sparse),'SOS_residuals':len(polynomial),'input_existentials':input_count,'arithmetic_wires':nextvar-input_count,'calls':dict(c.calls),'row_witnesses':29,'row_source_nodes':len(row.nodes),'row_degree':50,'max_abs_coefficient':max(map(abs,sparse.values())),'claim':'literal complete direct-Horn ordinary polynomial, mathematical equivalence; not a low-variable record or kernel-checked translation'}
 for n,obj in [('equation.json',artifact),('circuit.json',recipe),('residuals.json',polynomial),('summary.json',summary),('row_source.json',{'nodes':row.nodes,'variables':row.vars,'output':P})]:
  (ROOT/n).write_text(json.dumps(obj,separators=(',',':'))+'\n')
 print(json.dumps(summary,indent=2))
if __name__=='__main__':build()

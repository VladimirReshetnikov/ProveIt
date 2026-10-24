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
  d=self.fresh('power.truncated_difference')
  # d = max(a-n,0), encoded as a disjunction.
  sub=self.imul(self.sos([self.diff(a,self.add(d,n))]),self.sos([self.le(a,n,'power.sub'),self.diff(d,self.c(0))]))
  finite=self.isum([self.pell(a,k,x,y),sub,self.sos([
   self.mod(x,self.add(self.mul(y,d),m),t,'power.mod'),
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
 def evaldag(self,dag,env,root,absolute_majorant=False):
  vals=[]
  for n in dag:
   if n[0]=='v':v=env[n[1]]
   elif n[0]=='c':v=self.c(abs(n[1]) if absolute_majorant else n[1])
   elif n[0]=='a':v=self.add(vals[n[1]],vals[n[2]])
   elif n[0]=='s':v=(self.add if absolute_majorant else self.sub)(vals[n[1]],vals[n[2]])
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

def branch_labels(c,horn,base):
 """Canonical labels and constructor DAG for each parameterized C222 rule.

 Every returned label is a polynomial with nonnegative coefficients in a,b,c,d.
 The bundle's one inequality witness is deliberately NOT removed.
 """
 result=[]
 for branch in horn['branches']:
  name=branch['name']
  env=dict(base)
  env.update({'p':base['a'] if name=='mp' else base['b'] if name=='gen' else c.c(0),
              'q':c.c(0),'v':base['b'] if name=='mp' else c.c(0)})
  for w in branch['wires']:
   if w['name'] in env: raise ValueError('duplicate wire')
   if any(t['coefficient']<=0 for t in w['value']): raise ValueError('nonpositive constructor coefficient')
   pos,neg=c.evalpoly(w['value'],env)
   if neg!=c.c(0): raise ValueError('signed constructor')
   env[w['name']]=pos
  remaining=branch['quadratic_residuals'][len(branch['wires']):]
  target='q' if name=='mp' else 'v'
  defining=remaining[-1]
  target_terms=[t for t in defining if target in t['monomial']]
  if target_terms!=[{'monomial':[target],'coefficient':1}]:
   raise ValueError('conclusion/premise definition is not monic')
  rhs=[{'monomial':t['monomial'],'coefficient':-t['coefficient']}
       for t in defining if target not in t['monomial']]
  if any(t['coefficient']<0 for t in rhs): raise ValueError('negative label coefficient')
  pos,neg=c.evalpoly(rhs,env)
  if neg!=c.c(0): raise ValueError('signed label')
  env[target]=pos
  # All original rows except the bundle side condition are now identities.
  guards=remaining[:1] if name=='bundle' else []
  result.append({'name':name,'p':env['p'],'q':env['q'],'v':env['v'],
                 'guards':guards,'bindings':env})
 return result

def row_source(horn,compiler_class=Compiler):
 """Eight-witness row: four rule parameters, two remainders, two quotients.

 The heterogeneous CRT bounds force each remainder <= y.  This implies
 the needed strict bound remainder < 1+(i+1)y for every natural index.
 """
 c=compiler_class()
 outer={s:c.var(s) for s in ['N','x','y','M0','i']}
 base={s:c.var(s) for s in horn['base_witnesses']}
 rem=[];beta_rows=[]
 for label in ['i','next']:
  r,quo=[c.var('x.'+label+'.'+s) for s in ['remainder','quotient']]
  ix=outer['i'] if label=='i' else c.addc(outer['i'],1)
  modulus=c.addc(c.mul(c.addc(ix,1),outer['y']),1)
  beta_rows.append(c.diff(outer['x'],c.add(c.mul(quo,modulus),r)))
  rem.append(r)
 S,Sp=rem;M=c.addc(outer['M0'],1)
 branches=branch_labels(c,horn,base)
 alternatives=[]
 for branch in branches:
  update=c.diff(c.mul(Sp,c.addc(c.mul(branch['v'],M),1)),
                c.prod([S,c.addc(c.mul(branch['p'],M),1),c.addc(c.mul(branch['q'],M),1)]))
  guards=[c.diff(*c.evalpoly(r,branch['bindings'])) for r in branch['guards']]
  alternatives.append(c.sos(guards+[update]))
 output=c.iadd(c.iprod(alternatives),c.sos(beta_rows))
 if len(c.vars)!=13 or c.eqs: raise ValueError('local interface mismatch')
 c.branches=branches;c.beta_rows=beta_rows
 return c,output

def build_circuit(compiler_class=Compiler):
 horn=json.loads((ROOT/'horn_shared_source.json').read_text())
 row,P=row_source(horn)
 from signed_backend import signed_class
 signed_row,signed_P=row_source(horn,signed_class(Compiler))
 c=compiler_class()
 N,x,y,M0=[c.var(s) for s in ['N','x','y','M0']]
 # Padding by truth(0,0,0) rows makes N a bound for all four rule parameters.
 # Each displayed constructor is monotone, so this explicit sum bounds all labels.
 majorant_branches=branch_labels(c,horn,{s:N for s in horn['base_witnesses']})
 H=c.sum([b[label] for b in majorant_branches for label in ['p','q','v']])
 height_exponent=c.addc(c.prod([c.c(2),H,N]),1)
 height_power=c.pow(c.c(2),height_exponent)
 c.eq(M0,height_power,'padded binary height')
 endpoints=[]
 for code,ix,want in [(x,c.c(0),c.addc(M0,2)),(x,N,c.c(1))]:
  _,r=c.divmod(code,c.addc(c.mul(c.addc(ix,1),y),1))
  c.eq(r,want,'beta endpoint')
  endpoints.append({'code':code,'index':ix,'remainder':r,'target':want})
 U=c.var('uniform beta quotient bound')
 a=[c.var('encoded row coordinate '+str(j)) for j in range(8)]
 idx=c.var('encoded row index')
 outer=[N,x,y,M0]
 bounds=[N]*4+[y,U,y,U]
 env_upper=outer+[N]+bounds
 eu=c.evaldag(signed_row.nodes,env_upper,signed_P,absolute_majorant=True);fu=c.c(0)
 # Each (bound+1)! divides T. Since every CRT modulus is 1 modulo T,
 # these factorials are coprime to B and cancel out of the range tests.
 # Prime-power lifting in the completeness proof removes the requirement
 # that all coordinate-bound factorials divide the CRT scale factorial.
 scale_argument=c.sum([eu,fu,N])
 T=c.fact(scale_argument)
 Q=c.addc(c.pow(c.addc(c.mul(c.addc(N,1),T),1),N),2)
 tn=c.pow(T,N);nf=c.fact(N);ch=c.choose(c.add(Q,N),N)
 modulus=c.fresh('CRT.product_modulus')
 c.eq(c.mul(T,Q),c.addc(modulus,1),'CRT positive modulus predecessor')
 _,B=c.divmod(c.prod([tn,nf,ch]),modulus)
 coordinate_certificates=[]
 for j,ai in enumerate(a):
  bound=bounds[j]
  choose=c.choose(ai,c.addc(bound,1))
  quotient=c.fresh('coordinate divisibility quotient')
  c.eq(choose,c.mul(B,quotient),'cancelled-factorial coordinate certificate')
  coordinate_certificates.append({'encoded':ai,'bound':bound,'choose':choose,'quotient':quotient})
 index_quotient=c.fresh('index divisibility quotient')
 c.eq(c.addc(c.mul(c.addc(idx,1),T),1),c.mul(B,index_quotient),'encoded row index')
 env_enc=outer+[idx]+a
 ee=c.evaldag(signed_row.nodes,env_enc,signed_P);fe=c.c(0)
 c.assertpoly(c.mod(ee,fe,B,'row evaluation'),'encoded row evaluation congruence')
 bindings={'upper_environment':env_upper,'encoded_environment':env_enc,
           'upper_e':eu,'upper_f':fu,'encoded_e':ee,'encoded_f':fe,
           'U':U,'coordinate_bounds':bounds,'encoded_coordinates':a,'index':idx,
           'T':T,'Q':Q,'B':B,'modulus':modulus,'N_factorial':nf,'scale_argument':scale_argument,
           'endpoints':endpoints,'label_majorant':H,'majorant_branches':majorant_branches,
           'height_exponent':height_exponent,'height_power':height_power,
           'coordinate_certificates':coordinate_certificates,'index_quotient':index_quotient,
           'encoded_signed_row':{'variables':signed_row.vars,'nodes':signed_row.nodes,'output':signed_P}}
 return c,row,P,bindings

def emit_circuit(output=None,compiler_class=Compiler):
 output=pathlib.Path(output) if output else ROOT
 output.mkdir(parents=True,exist_ok=True)
 c,row,P,bindings=build_circuit(compiler_class)
 recipe={'format':'natural-arithmetic-dag-v1','variable_names':c.vars,'nodes':c.nodes,
         'equalities':c.eqs,'heterogeneous_bounds':True,'call_ledger':c.ledger,
         'source_binding':bindings}
 degrees=[]
 for node in row.nodes:
  degrees.append(0 if node[0]=='c' else 1 if node[0]=='v' else
                 max(degrees[node[1]],degrees[node[2]]) if node[0]=='a' else
                 degrees[node[1]]+degrees[node[2]])
 summary={'input_existentials':len(c.vars),'arithmetic_nodes':len(c.nodes),
          'calls':dict(c.calls),'local_witnesses':8,'local_source_nodes':len(row.nodes),
          'local_degree_upper_bound':max(degrees[P[0]],degrees[P[1]]),
          'local_parameters':['N','x','y','M0','i'],
          'local_witness_order':row.vars[5:],
          'local_bounds':['N']*4+['y','U','y','U']}
 row_artifact={'nodes':row.nodes,'variables':row.vars,'output':P,
               'branch_projection':row.branches,'beta_rows':row.beta_rows}
 for name,obj in [('circuit.json',recipe),('row_source.json',row_artifact),('summary_circuit.json',summary)]:
  (output/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
 print(json.dumps(summary,indent=2))
 return c,row,P,bindings

if __name__=='__main__': emit_circuit()


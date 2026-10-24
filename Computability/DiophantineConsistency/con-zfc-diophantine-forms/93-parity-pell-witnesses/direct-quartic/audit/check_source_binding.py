#!/usr/bin/env python3
"""Independent exact local-source and global bounded-CRT instance audit."""
import json,pathlib,collections
import check_composition as C
D=pathlib.Path(__file__).resolve().parent;S=D.parent;j=C.J;B=j['source_binding'];row=json.loads((S/'row_source.json').read_text());horn=json.loads((S/'horn_shared_source.json').read_text())
req=C.req
class NaturalTrees:
 def __init__(self):self.pool=[];self.index={}
 def node(self,t):
  t=tuple(t)
  if t not in self.index:self.index[t]=len(self.pool);self.pool.append(t)
  return self.index[t]
 def const(self,n):return self.node(('c',n))
 def var(self,n):return self.node(('v',n))
 def op(self,k,a,b):
  if k=='a':
   if a==self.const(0):return b
   if b==self.const(0):return a
  else:
   if a==self.const(0) or b==self.const(0):return self.const(0)
   if a==self.const(1):return b
   if b==self.const(1):return a
  x,y=self.pool[a],self.pool[b]
  if x[0]==y[0]=='c':return self.const(x[1]+y[1] if k=='a' else x[1]*y[1])
  return self.node((k,*sorted((a,b))))
 def add(self,a,b):return self.op('a',a,b)
 def mul(self,a,b):return self.op('m',a,b)
 def summ(self,xs):
  v=self.const(0)
  for x in xs:v=self.add(v,x)
  return v
 def prod(self,xs):
  v=self.const(1)
  for x in xs:v=self.mul(v,x)
  return v
 def load(self,nodes,env):
  out=[]
  for n in nodes:
   out.append(self.const(n[1]) if n[0]=='c' else env[n[1]] if n[0]=='v' else self.op(n[0],out[n[1]],out[n[2]]))
  return out
T=NaturalTrees();zero=T.const(0);one=T.const(1);rv={s:T.var('row:'+s) for s in row['variables']}
req(len(rv)==35 and row['variables'][:6]==['N','x','y','m','M0','i'],'row variable order')
def sadd(p,q):return(T.add(p[0],q[0]),T.add(p[1],q[1]))
def smul(p,q):return(T.add(T.mul(p[0],q[0]),T.mul(p[1],q[1])),T.add(T.mul(p[0],q[1]),T.mul(p[1],q[0])))
def ssum(ps):
 v=(zero,zero)
 for p in ps:v=sadd(v,p)
 return v
def sprod(ps):
 v=(one,zero)
 for p in ps:v=smul(v,p)
 return v
def sos(ps):return ssum([smul(p,p) for p in ps])
def plus1(a):return T.add(a,one)
def poly(ts):
 pos=[];neg=[]
 for t in ts:
  v=T.prod([T.const(abs(t['coefficient']))]+[rv[a] for a in t['monomial']]);(pos if t['coefficient']>0 else neg).append(v)
 return T.summ(pos),T.summ(neg)
rs=[];remainders=[]
for code,where in [('x','i'),('x','next')]:
 r,q,s=[rv[code+'.'+where+'.'+a] for a in ['remainder','quotient','slack']];ix=rv['i'] if where=='i' else plus1(rv['i']);d=plus1(T.mul(plus1(ix),rv['y']));rs.extend([(rv[code],T.add(T.mul(q,d),r)),(d,plus1(T.add(r,s)))]);remainders.append(r)
s,sp=remainders;m=plus1(rv['M0']);rs.extend([(rv['m'],T.add(rv[k],rv[k+'.upper_slack'])) for k in ['p','q','v']]);rs.append((T.mul(sp,plus1(T.mul(rv['v'],m))),T.prod([s,plus1(T.mul(rv['p'],m)),plus1(T.mul(rv['q'],m))])))
want=sadd(sprod([sos([poly(p) for p in branch['quadratic_residuals']]) for branch in horn['branches']]),sos(rs));actual=T.load(row['nodes'],[rv[x] for x in row['variables']]);req(tuple(actual[x] for x in row['output'])==want,'local source mismatch')
# Compare the two globally instantiated local polynomial sides exactly as arithmetic trees.
globalvalues=T.load(j['nodes'],[T.var('global:'+s) for s in j['variable_names']])
for prefix in ['upper','encoded']:
 env=B[prefix+'_environment'];vals=T.load(row['nodes'],[globalvalues[n] for n in env]);req([vals[x] for x in row['output']]==[globalvalues[B[prefix+'_e']],globalvalues[B[prefix+'_f']]],prefix+' substitution')
req(B['upper_environment']==[0,1,2,3,4,0]+[B['U']]*29,'uniform upper map');req(B['encoded_environment']==[0,1,2,3,4,B['index']]+B['encoded_coordinates'],'encoded map');req(len(B['encoded_coordinates'])==29,'coordinate count')
firstfact=next(x for x in C.L if x['kind']=='fact');bound=T.summ([globalvalues[B['upper_e']],globalvalues[B['upper_f']],globalvalues[0]]);req(globalvalues[firstfact['arguments'][0]]==bound,'factorial scale argument')
# Arithmetic interfaces are already independently checked; use their semantic tags here.
ev=C.evaluator();n,x,y,m,m0=map(ev,range(5));u=ev(B['U']);idx=ev(B['index']);a=list(map(ev,B['encoded_coordinates']));t=C.Fact(('arbitrary_upper_bound',));q=C.A(C.Pow(C.A(C.M(C.A(n,C.c(1)),t),C.c(1)),n),C.c(2));req(ev(B['T'])==t and ev(B['Q'])==q,'TQ formula')
modulus=ev(B['modulus']);b=C.Mod(C.M(C.Pow(t,n),C.Fact(n),C.Choose(C.A(q,n),n)),modulus);req(ev(B['B'])==b,'Bformula');req(ev(B['F'])==C.Fact(C.A(u,C.c(1))),'uniform factorial')
eqs=[e for e in C.E if e[2]=='CRT positive modulus predecessor'];req(len(eqs)==1 and ev(eqs[0][0])==C.M(t,q) and ev(eqs[0][1])==C.A(modulus,C.c(1)),'modulus predecessor')
height=[e for e in C.E if e[2]=='uniform binary height'];req(len(height)==1 and ev(height[0][0])==m0 and ev(height[0][1])==C.Pow(C.c(2),C.A(C.M(C.c(2),m,n),C.c(1))),'global height formula')
ends=[e for e in C.E if e[2]=='beta endpoint'];req(len(ends)==2,'endpointcount')
for e,(code,ix,target) in zip(ends,[(x,C.c(0),C.A(m0,C.c(2))),(x,n,C.c(1))]):req(ev(e[0])==C.Mod(code,C.A(C.M(C.A(ix,C.c(1)),y),C.c(1))) and ev(e[1])==target,'endpoint')
coords=[e for e in C.E if e[2]=='falling-factorial coordinate certificate'];req(len(coords)==29,'coordinateconditions')
for i,(e,ai) in enumerate(zip(coords,a)):
 left,right,_=e;req(ev(left)==C.M(C.Fact(C.A(u,C.c(1))),C.Choose(ai,C.A(u,C.c(1)))),'coordinate lhs');r=C.N[right];req(r[0]=='m','coordinate rhs');parts=list(map(ev,r[1:]));req(b in parts and any(p[0]=='v' for p in parts),'coordinate divisibility')
ixeq=[e for e in C.E if e[2]=='encoded row index'];req(len(ixeq)==1,'indexconditioncount');left,right,_=ixeq[0];req(ev(left)==C.A(C.M(C.A(idx,C.c(1)),t),C.c(1)),'indexlhs');req(C.N[right][0]=='m' and b in list(map(ev,C.N[right][1:])),'indexdivisibility')
# Last row is precisely the congruence between the two checked instantiated polynomials.
C.over[B['encoded_e']]=('row_e',);C.over[B['encoded_f']]=('row_f',);ev=C.evaluator();e=[x for x in C.E if x[2]=='encoded row evaluation congruence'];req(len(e)==1,'evaluationcount')
for side,tag in zip(e[0][:2],[('row_e',),('row_f',)]):
 nnode=C.N[side];req(nnode[0]=='a','evaluation addition');parts=list(map(ev,nnode[1:]));req(tag in parts,'evaluationpolynomial');other=next(p for p in parts if p!=tag);req(other[0]=='mul' and b in other[1:] and any(p[0]=='v' for p in other[1:]),'evaluationmultiple')
out={'status':'PASS','local_witnesses':29,'global_outer_parameters':5,'uniform_bounds':1,'encoded_coordinates':29,'encoded_indices':1,'checked':'Exact local Horn/beta/accumulator source, both source instantiations, factorial bound, CRTproduct,29fallingfactorial conditions,indexcondition,evaluationcongruence,2endpoints andglobalbinaryheight. All arithmetic identities interpreted through independently audited primitives.'}
(D/'SOURCE_BINDING_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

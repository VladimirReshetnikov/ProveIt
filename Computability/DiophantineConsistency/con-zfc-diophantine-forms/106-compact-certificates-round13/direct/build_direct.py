#!/usr/bin/env python3
"""Independent finite natural-quartic materializer, round 13.
No imported or executed upstream Python. Implements literal C222 constructors,
positive Pell powers, prime-lift CRT, short-beta rows, and shared signed offsets.
Python standard library only. All polynomial coefficients are materialized.
"""
import argparse, collections, hashlib, json, pathlib
ROOT=pathlib.Path(__file__).resolve().parent

def must(x,msg):
 if not x: raise ValueError(msg)
def C(n):
 must(isinstance(n,int) and n>=0,'natural constant required');return ('c',n)
Z,O,TWO,FOUR=map(C,(0,1,2,4))
class Circuit:
 def __init__(self,shared=True,oriented=False):
  self.vars=[];self.rows=[];self.cache={};self.defs={};self.powers={};self.choices={};self.facts={};self.macros=[];self.serial=collections.Counter();self.shared=shared;self.offset=None;self.oriented=oriented;self.bindings={}
 def v(self,name,kind='witness'):
  i=len(self.vars);self.vars.append({'name':name,'kind':kind});return ('v',i)
 def fresh(self,name):
  self.serial[name]+=1;return self.v(name+'.'+str(self.serial[name]))
 def row(self,terms,label,gate=None):
  p=collections.defaultdict(int)
  for coeff,atoms in terms:
   ids=[]
   for a in atoms:
    if a[0]=='c':coeff*=a[1]
    else:ids.append(a[1])
   p[tuple(sorted(ids))]+=coeff
  p={m:c for m,c in p.items() if c};must(all(len(m)<=2 for m in p),'nonquadratic residual')
  if not p:return
  if gate is not None:self.defs[gate]=len(self.rows)
  self.rows.append({'label':label,'terms':[[c,list(m)] for m,c in sorted(p.items())],'gate':gate})
 def eq(self,a,b,label):self.row([(1,[a]),(-1,[b])],label)
 def op(self,typ,a,b):
  if typ=='add':
   if a==Z:return b
   if b==Z:return a
  else:
   if a==Z or b==Z:return Z
   if a==O:return b
   if b==O:return a
  if a[0]==b[0]=='c':return C(a[1]+b[1] if typ=='add' else a[1]*b[1])
  a,b=sorted((a,b));key=(typ,a,b)
  if key not in self.cache:
   v=self.v(typ+'.'+str(len(self.cache)),'gate');self.cache[key]=v
   self.row([(1,[v]),(-1,[a]),(-1,[b])] if typ=='add' else [(1,[v]),(-1,[a,b])],typ,v[1])
  return self.cache[key]
 def add(self,a,b):return self.op('add',a,b)
 def mul(self,a,b):return self.op('mul',a,b)
 def sum(self,aa):
  v=Z
  for a in aa:v=self.add(v,a)
  return v
 def prod(self,aa):
  v=O
  for a in aa:v=self.mul(v,a)
  return v
 def sq(self,a):return self.mul(a,a)
 def p_add(self,a,b):return(self.add(a[0],b[0]),self.add(a[1],b[1]))
 def p_mul(self,a,b):return(self.sum([self.mul(a[0],b[0]),self.mul(a[1],b[1])]),self.sum([self.mul(a[0],b[1]),self.mul(a[1],b[0])]))
 def p_sq(self,a):return(self.add(self.sq(a[0]),self.sq(a[1])),self.prod([TWO,a[0],a[1]]))
 def congruent(self,a,b,m,label):
  if self.shared:
   if self.offset is None:self.offset=self.v('global.signed_quotient_offset')
   qp=self.offset;qm=self.fresh(label+'.translated_quotient')
  else:qp=self.fresh(label+'.qp');qm=self.fresh(label+'.qm')
  self.eq(self.add(a,self.mul(m,qp)),self.add(b,self.mul(m,qm)),label)
  self.macros.append({'kind':'congruence','label':label,'left':a,'right':b,'modulus':m,'positive_left_quotient':qp,'positive_right_quotient':qm})
 def norm(self,a,x,y,label):
  yy=self.sq(y);self.eq(self.add(self.sq(x),yy),self.add(O,self.mul(self.sq(a),yy)),label)
 def power(self,n,k):
  key=(n,k)
  if key in self.powers:return self.powers[key]
  tag='power'+str(len(self.powers));start=len(self.vars);m=self.v(tag+'.output');self.powers[key]=m
  W=self.add(n,k)
  A,T,Zv,X,Y,U,V,S,R,B=[self.v(tag+'.'+s) for s in ['A','T','Z','X','Y','U','V','S','R','B']]
  a2,yk,b2=[self.v(tag+'.'+s) for s in ['a2','yk','b2']]
  self.eq(A,self.add(a2,TWO),tag+'.A_ge_2');self.eq(Y,self.add(k,yk),tag+'.Y_ge_k');self.eq(B,self.add(b2,TWO),tag+'.B_ge_2')
  self.norm(A,X,Y,tag+'.norm_AXY');self.norm(A,U,V,tag+'.norm_AUV');self.norm(B,S,R,tag+'.norm_BSR')
  q4,vd=self.v(tag+'.q4'),self.v(tag+'.vd');fourY=self.mul(FOUR,Y)
  self.eq(B,self.add(O,self.mul(fourY,q4)),tag+'.B_mod_4Y');self.eq(V,self.mul(self.sq(Y),self.add(vd,O)),tag+'.V_positive_multiple')
  self.congruent(B,A,U,tag+'.B_mod_U');self.congruent(S,X,U,tag+'.S_mod_U');self.congruent(R,k,fourY,tag+'.R_mod_4Y')
  left=self.add(X,self.mul(Y,n));right=self.add(self.mul(Y,A),m)
  if self.oriented:
   quot=self.v(tag+'.power_nonnegative_quotient');self.eq(left,self.add(right,self.mul(T,quot)),tag+'.power_oriented')
  else:self.congruent(left,right,T,tag+'.power_mod_T')
  self.eq(self.prod([TWO,A,n]),self.sum([T,self.sq(n),O]),tag+'.T_definition')
  gap=self.v(tag+'.gap');self.eq(T,self.sum([m,gap,O]),tag+'.output_bound')
  self.norm(self.add(W,O),A,self.mul(W,Zv),tag+'.last_norm')
  self.macros.append({'kind':'power','base':n,'exponent':k,'output':m,'start_variable':start,'end_variable':len(self.vars),'tag':tag})
  return m
 def choose(self,n,k):
  key=n,k
  if key in self.choices:return self.choices[key]
  tag='binomial'+str(len(self.choices));out=self.v(tag+'.output');self.choices[key]=out
  q=self.add(self.power(TWO,n),O);num=self.power(self.add(q,O),n);den=self.power(q,k)
  hi,r,rs,os=[self.v(tag+'.'+x) for x in ['high','remainder','rslack','oslack']]
  quot=self.add(self.mul(q,hi),out)
  self.eq(num,self.add(self.mul(den,quot),r),tag+'.digit_division');self.eq(den,self.sum([r,rs,O]),tag+'.remainder_bound');self.eq(q,self.sum([out,os,O]),tag+'.digit_bound')
  self.macros.append({'kind':'binomial','n':n,'k':k,'output':out});return out
 def fact(self,n):
  if n in self.facts:return self.facts[n]
  tag='factorial'+str(len(self.facts));out=self.v(tag+'.output');self.facts[n]=out
  shift=self.add(n,TWO);r=self.power(shift,shift);choose=self.choose(self.add(r,n),n);num=self.power(self.add(r,O),n)
  rem,slack=self.v(tag+'.remainder'),self.v(tag+'.slack')
  self.eq(self.add(num,choose),self.sum([self.mul(choose,out),rem,O]),tag+'.ceiling');self.eq(choose,self.sum([rem,slack,O]),tag+'.remainder_bound')
  self.macros.append({'kind':'factorial','n':n,'output':out});return out
 def moduli_product(self,N,T):
  Q=self.add(self.power(self.add(self.mul(self.add(N,O),T),O),N),TWO)
  numerator=self.prod([self.power(T,N),self.fact(N),self.choose(self.add(Q,N),N)])
  mod=self.v('CRT.product.modulus');self.eq(self.add(mod,O),self.mul(T,Q),'CRT.product.modulus_definition')
  B,q,s=[self.v('CRT.product.'+j) for j in ['B','quotient','slack']]
  self.eq(numerator,self.add(self.mul(mod,q),B),'CRT.product.division');self.eq(mod,self.sum([B,s,O]),'CRT.product.remainder_bound')
  return B
 def source(self,e,index,short_beta=True):
  ad,mu,sq=self.add,self.mul,self.sq
  def I(a,b):
   s=ad(a,b);return ad(mu(TWO,mu(s,ad(s,O))),mu(FOUR,b))
  def A(a,b):return ad(I(a,b),TWO)
  def M(a,b):return ad(I(a,b),O)
  def E(a,b):return ad(I(a,b),C(3))
  def neg(a):return I(a,O)
  def X(a,b):return neg(A(a,neg(b)))
  def req(x,k,f):return A(x,I(f,neg(A(x,I(f,neg(M(x,k)))))))
  def clos(x,y,k,f):
   subset=A(k,I(M(k,x),M(k,y)));tail=I(subset,req(y,k,f));tail=neg(A(x,tail));tail=neg(A(x,I(f,tail)));return A(y,I(M(y,k),tail))
  def bundle(x,y,z):
   nks=A(z,I(clos(x,y,z,z),neg(req(y,z,z))));vrel=I(M(x,y),A(z,M(x,y)));return neg(I(vrel,nks))
  a,b,c,d,p,q,v=[e[n] for n in ['a','b','c','d','p','q','v']]
  axioms=[X(a,E(a,b)),I(A(a,I(b,c)),I(A(a,b),A(a,c))),I(E(a,b),I(M(c,a),M(c,b))),I(A(a,A(b,c)),A(b,A(a,c))),I(E(c,a),I(M(c,b),M(a,b))),I(X(a,A(a,b)),b),I(E(c,a),I(E(c,b),A(M(a,b),E(a,b)))),I(I(I(c,d),a),I(I(a,c),I(b,c))),bundle(a,b,c)]
  pq=ad(sq(p),sq(q));branches=[(ad(pq,sq(v)),Z)]
  branches += [self.p_add((pq,Z),self.p_sq((v,f))) for f in axioms]
  gp,gn=self.p_sq((ad(sq(c),mu(a,b)),mu(c,ad(a,b))))
  branches[-1]=self.p_add(branches[-1],self.p_sq((gp,ad(gn,sq(ad(d,O))))))
  branches.append(self.p_sq((q,I(p,v))));branches.append(self.p_add((sq(q),Z),self.p_sq((v,A(a,p)))))
  total=O,Z
  for r in branches:total=self.p_mul(total,r)
  carrier=ad(e['M0'],O)
  def weight(name):return ad(O,mu(e[name],carrier))
  D=ad(mu(ad(index,O),e['y']),O);Dp=ad(D,e['y'])
  rows=[(mu(e['Sp'],weight('v')),self.prod([e['S'],weight('p'),weight('q')])),(e['x'],ad(e['S'],mu(D,e['u']))),(e['x'],ad(e['Sp'],mu(Dp,e['vq'])))]
  if not short_beta:rows += [(D,self.sum([e['S'],e['r'],O])),(Dp,self.sum([e['Sp'],e['rp'],O]))]
  for r in rows:total=self.p_add(total,self.p_sq(r))
  return total
 def export(self,affine=True):
  replacement={};deleted=set()
  for i in range(len(self.vars)):
   rid=self.defs.get(i)
   if affine and rid is not None and all(len(m)<=1 for c,m in self.rows[rid]['terms']):
    value=collections.defaultdict(int);own=0
    for c,m in self.rows[rid]['terms']:
     if m==[i]:own+=c
     elif not m:value[()]-=c
     else:
      must(m[0]<i,'nontriangular gate')
      for mon,coef in replacement[m[0]].items():value[mon]-=c*coef
    value={m:c for m,c in value.items() if c};must(own==1 and all(c>=0 for c in value.values()),'invalid natural affine restoration')
    if len(value)<=4:replacement[i]=value;deleted.add(rid);continue
   replacement[i]={(i,):1}
  restored=[]
  for rid,row in enumerate(self.rows):
   if rid in deleted:continue
   poly=collections.defaultdict(int)
   for c,m in row['terms']:
    val={():c}
    for i in m:
     res=collections.defaultdict(int)
     for m1,c1 in val.items():
      for m2,c2 in replacement[i].items():res[tuple(sorted(m1+m2))]+=c1*c2
     val=res
    for mon,coef in val.items():poly[mon]+=coef
   terms=[[c,list(m)] for m,c in sorted(poly.items()) if c]
   if terms:restored.append({'label':row['label'],'terms':terms,'gate':row['gate']})
  gates={r['gate']:i for i,r in enumerate(restored) if r['gate'] is not None}
  needed={i for i,r in enumerate(restored) if r['gate'] is None};used={v for i in needed for c,m in restored[i]['terms'] for v in m};todo=list(used)
  while todo:
   i=todo.pop();r=gates.get(i)
   if r is None or r in needed:continue
   needed.add(r)
   for c,mon in restored[r]['terms']:
    for j in mon:
     if j not in used:used.add(j);todo.append(j)
  order=sorted(used);remap={old:new for new,old in enumerate(order)}
  rows=[{'label':r['label'],'terms':[[c,[remap[j] for j in m]] for c,m in r['terms']]} for i,r in enumerate(restored) if i in needed]
  P=collections.defaultdict(int)
  for r in rows:
   for ca,ma in r['terms']:
    for cb,mb in r['terms']:P[tuple(sorted(ma+mb))]+=ca*cb
  P={m:c for m,c in P.items() if c}
  metrics={'natural_variables':len(order),'quadratic_residuals':len(rows),'degree':max(map(len,P)),'monomials':len(P),'coefficient_height':max(map(abs,P.values())),'max_residual_height':max(abs(c) for r in rows for c,m in r['terms']),'power_graphs':len(self.powers),'binomial_graphs':len(self.choices),'factorial_graphs':len(self.facts),'signed_congruences':sum(m['kind']=='congruence' for m in self.macros),'variable_kinds':dict(collections.Counter(self.vars[i]['kind'] for i in order)),'affine_gates_eliminated':len(deleted),'unused_variables_removed':len(self.vars)-len(order)-len(deleted)}
  return {'format':'explicit_quadratic_residuals_v1','domain':'nonnegative integers','variables':[self.vars[i] for i in order],'residuals':rows,'metrics':metrics},{'format':'ordinary_sparse_polynomial_v1','domain':'nonnegative integers','variable_count':len(order),'terms':[[c,list(m)] for m,c in sorted(P.items())]}, {'old_to_new':remap,'affine_expressions':{str(i):[[c,list(m)] for m,c in sorted(p.items())] for i,p in replacement.items() if p!={(i,):1}},'metrics':metrics}

def build(short_beta=True,shared=True,oriented=False):
 b=Circuit(shared=shared,oriented=oriented)
 N=b.add(b.v('N0','outer'),O);x=b.v('x','outer');y0=b.v('y0' if short_beta else 'y','outer');m=b.add(b.v('m0','outer'),O);M0=b.v('M0','outer')
 y=b.sum([M0,TWO,y0]) if short_beta else y0
 pars={'t':N,'x':x,'y':y,'m':m,'M0':M0}
 b.eq(b.power(b.add(m,O),N),b.add(M0,O),'carrier_power')
 if short_beta:
  u0,ut=b.v('endpoint.u0'),b.v('endpoint.ut')
 else:u0,r0,ut,rt=[b.v('endpoint.'+s) for s in ['u0','r0','ut','rt']]
 Dn=b.add(b.mul(b.add(N,O),y),O)
 b.eq(x,b.add(b.add(M0,TWO),b.mul(b.add(y,O),u0)),'endpoint.initial')
 b.eq(x,b.add(O,b.mul(Dn,ut)),'endpoint.final')
 if not short_beta:
  b.eq(y,b.sum([M0,r0,TWO]),'endpoint.initial_bound');b.eq(Dn,b.add(rt,TWO),'endpoint.final_bound')
 names=['p','q','v','a','b','c','d','S','Sp','u','vq']
 if not short_beta:names+=['r','rp']
 U=b.v('CRT.private_bound')
 upper={n:m if n in ['p','q','v'] else (y if short_beta and n in ['S','Sp'] else U) for n in names}
 range_k={n:y if short_beta and n in ['S','Sp'] else b.add(upper[n],O) for n in names}
 encoded={n:b.add(b.v('CRT.column.'+n),O) for n in names};idx=b.v('CRT.index')
 ep,fp=b.source(pars|upper,N,short_beta=short_beta)
 H=b.add(ep,fp) if short_beta else b.sum([ep,fp,N])
 T=b.fact(H);B=b.moduli_product(N,T)
 for n in names:
  out=b.choose(encoded[n],range_k[n]);q=b.v('CRT.range_quotient.'+n);b.eq(out,b.mul(B,q),'CRT.range.'+n)
 qi=b.v('CRT.index_quotient');b.eq(b.add(O,b.mul(b.add(idx,O),T)),b.mul(B,qi),'CRT.index_constraint')
 ee,ff=b.source(pars|encoded,idx,short_beta=short_beta);b.congruent(ee,ff,B,'CRT.evaluation')
 b.bindings={'parameters':pars,'private_bound':U,'upper':upper,'range_lower_arguments':range_k,'encoded_columns':encoded,'encoded_index':idx,'upper_E':ep,'upper_F':fp,'H':H,'factorial':T,'CRT_product':B,'encoded_E':ee,'encoded_F':ff,'row_coordinate_count':len(names),'short_beta':short_beta}
 return b

def write(p,obj):
 data=(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode();p.write_bytes(data);return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,default=ROOT/'candidate');p.add_argument('--baseline',action='store_true');p.add_argument('--no-shared-offset',action='store_true');p.add_argument('--oriented-power',action='store_true');p.add_argument('--keep-affine',action='store_true');args=p.parse_args()
 b=build(short_beta=not args.baseline,shared=not args.no_shared_offset,oriented=args.oriented_power);e,q,a=b.export(affine=not args.keep_affine);args.output.mkdir(parents=True,exist_ok=True)
 hashes={}
 for name,obj in [('equation.json',e),('expanded_polynomial.json',q),('affine_restoration.json',a),('circuit.json',{'variables':b.vars,'residuals':b.rows,'macros':b.macros,'bindings':b.bindings})]:hashes[name]=write(args.output/name,obj)
 receipt={'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'metrics':e['metrics'],'sha256':hashes,'short_beta':not args.baseline,'shared_offset':not args.no_shared_offset,'oriented_power':args.oriented_power,'affine_elimination':not args.keep_affine,'scope':'literal polynomial construction; mathematical proof separate; not kernel certification'}
 write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

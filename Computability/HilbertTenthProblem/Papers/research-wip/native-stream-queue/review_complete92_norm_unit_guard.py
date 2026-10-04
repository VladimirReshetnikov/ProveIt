"""Fresh independent full92 audit. Frozen programs are read only as bytes/data."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
PINS={'complete92_norm_unit_guard.py':'cce493645c8935b25f9805d9bd588db5d1aa55b2f9c571d2492fe5138852447b','complete92_norm_unit_guard.json':'ae1f1564cbf8266a621cbcbbe5db9201d94483fe54441f289af245581e065cb3','complete92_norm_unit_guard.md':'db07def77dd005c79fa6b63fe3c03641b7238f5a96fa151377f07e9c4b681851'}
TAIL=[['ng_ic2', '*', 'i', 'c2'], ['ng_Dminus1', '*', 'ng_ic2', 'aux_coefficient_root'], ['ng_D', '+', 'ng_Dminus1', 1], ['ng_RD', '*', 'r_lhs', 'ng_D'], ['ng_b', '+', 'R10a', 'ng_RD'], ['ng_u', '*', 'R10a', 'auxiliary_quotient'], ['ng_u2', '*', 'ng_u', 'ng_u'], ['ng_p', '*', 'ng_D', 'ng_u2'], ['ng_b2', '*', 'ng_b', 'ng_b'], ['ng_P5a', '*', 'norm_triple', 'norm_index'], ['ng_P5', '*', 'ng_P5a', 'norm_transport'], ['ng_sum', '+', 'ng_p', 'ng_b2'], ['ng_gap', '-', 'ng_sum', 'aux_y2'], ['ng_Qgap', '*', 'R16', 'ng_gap'], ['ng_Aplus1', '+', 'ng_Qgap', 'aux_y2'], ['ng_A', '-', 'ng_Aplus1', 1], ['ng_Qp', '*', 'R16', 'ng_p'], ['ng_Qb2', '*', 'R16', 'ng_b2'], ['ng_cross', '*', 'ng_Qp', 'ng_Qb2'], ['ng_four', '*', 4, 'ng_cross'], ['ng_A2', '*', 'ng_A', 'ng_A'], ['ng_K', '-', 'ng_A2', 'ng_four'], ['ng_unit', '+', 'ng_K', 1], ['ng_product', '*', 'ng_P5', 'ng_unit'], ['polynomial92', '-', 'ng_product', 1]]
PARENT='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
def check(ok,message):
 if not ok:raise ValueError(message)
def H(b):return hashlib.sha256(b).hexdigest()
def J(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def object_pairs(xs):
 d={}
 for k,v in xs:
  check(k not in d,'duplicate key');d[k]=v
 return d
def bad(x):raise ValueError('nonintegral JSON '+x)
def decode(b):return json.loads(b,object_pairs_hook=object_pairs,parse_float=bad,parse_constant=bad)
def equal(a,b):
 if type(a)!=type(b):return False
 if type(a)==dict:return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if type(a)==list:return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b
class Algebra:
 def __init__(self,names):self.names=tuple(sorted(set(names)));self.unit=(0,)*len(self.names)
 def const(self,n):return Polynomial(self,{self.unit:n} if n else {})
 def var(self,n):
  e=list(self.unit);e[self.names.index(n)]=1;return Polynomial(self,{tuple(e):1})
class Polynomial:
 def __init__(self,ring,coeff):self.ring=ring;self.c={e:a for e,a in coeff.items() if a}
 def lift(self,x):return self.ring.const(x) if type(x)==int else x
 def __add__(self,other):
  other=self.lift(other);d=dict(self.c)
  for e,c in other.c.items():d[e]=d.get(e,0)+c
  return Polynomial(self.ring,d)
 __radd__=__add__
 def __neg__(self):return Polynomial(self.ring,{e:-a for e,a in self.c.items()})
 def __sub__(self,other):return self+-self.lift(other)
 def __rsub__(self,other):return self.lift(other)+-self
 def __mul__(self,other):
  other=self.lift(other);d={}
  for e,a in self.c.items():
   for f,b in other.c.items():
    g=tuple(x+y for x,y in zip(e,f));d[g]=d.get(g,0)+a*b
  return Polynomial(self.ring,d)
 __rmul__=__mul__
 def __pow__(self,n):
  out=self.ring.const(1);p=self
  while n:
   if n&1:out=out*p
   n//=2
   if n:p=p*p
  return out
 def __eq__(self,other):return self.c==self.lift(other).c
 def report(self):return {'terms':len(self.c),'sha256':H(J([[list(e),a] for e,a in sorted(self.c.items())]))}
def traced(rows,leaves):
 defs={r[0]:r for r in rows};memo=dict(leaves);alg=next(iter(leaves.values())).ring
 def at(n):
  if type(n)==int:return alg.const(n)
  if n not in memo:
   check(n in defs,'unbound cut '+n);_,op,a,b=defs[n];aa,bb=at(a),at(b)
   memo[n]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
  return memo[n]
 return at

def live_source(packet):
 rows=packet['source'];free=packet['free'];known=set(free);defs={}
 check(len(free)==len(known),'duplicate supplied port')
 for r in rows:
  check(type(r)==list and len(r)==4,'row shape');n,op,a,b=r
  check(n not in known and op in ['+','-','*'],'SSA/primitive')
  check(all(type(t)==int or (type(t)==str and t in known) for t in [a,b]),'topology')
  defs[n]=r;known.add(n)
 live=set();ports=set();todo=[packet['output']]
 while todo:
  n=todo.pop()
  if type(n)==int or n in live or n in ports:continue
  if n in defs:live.add(n);todo.extend(defs[n][2:])
  else:ports.add(n)
 check(live==set(defs) and ports==set(free),'dead row or supplied value')
 counts=Counter(r[1] for r in rows);return {'total':len(rows),'M':counts['*'],'A':counts['+']+counts['-']}
def reduce_f(poly,D):
 r=poly.ring;idx=r.names.index('f');out=r.const(0);powers={0:r.const(1)}
 for e,a in poly.c.items():
  n=e[idx]//2
  if n not in powers:powers[n]=D**n
  ee=list(e);ee[idx]%=2;out=out+Polynomial(r,{tuple(ee):a})*powers[n]
 return out

def exact_algebra(old,new,ninety):
 ring=Algebra(['Delta','c','i','R','T','y','f','N0','Nk','Nt']);v=ring.var
 Delta,c,i,R,T,y,f=[v(n) for n in ['Delta','c','i','R','T','y','f']];P5=v('N0')*v('Nk')*v('Nt')
 Q=Delta**2*i**2*c**4;D=1+Delta*i**2*c**4;b=c+R*D;u=c*T
 A=Q*(D*u**2+b**2)-(Q-1)*y**2-1;B=2*Q*u*b;K=A**2-D*B**2
 cuts={'A':Delta,'R10a':c,'i':i,'r_lhs':R,'auxiliary_quotient':T,'y_aux':y,'f':f,'norm_triple':v('N0'),'norm_index':v('Nk'),'norm_transport':v('Nt')}
 p84=traced(old['source'],cuts)(old['output']);child=traced(new['source'],cuts);p92=child(new['output']);p90=traced(ninety['source'],cuts)(ninety['output'])
 for name,want in [('ng_D',D),('ng_b',b),('ng_P5',P5),('ng_A',A),('ng_four',D*B**2),('ng_K',K)]:check(child(name)==want,'actual new producer '+name)
 fi=ring.names.index('f');ti=ring.names.index('T');check(all((e[fi]+e[ti])%2==0 for e in p84.c),'complete parent f/T sign symmetry')
 check(p92==P5*(K+1)-1,'whole92 unit-guard formula')
 check(p90==(P5*(A+1)-1)**2-D*(P5*B)**2,'whole90 comparison norm')
 check(p90==P5*p92+(P5-1)*(2*P5*A-1),'complete90/92 correction identity')
 check(reduce_f(p84,D)==Delta*(P5*(A-B*f+1)-1),'whole84 reduced auxiliary identity')
 zcuts=dict(cuts);zcuts['norm_triple']=ring.const(0);check(traced(new['source'],zcuts)(new['output'])==-1,'P5 zero case')
 return {'basis':list(ring.names),'whole92':p92.report(),'whole90':p90.report(),'whole84_mod_f2_minus_D':reduce_f(p84,D).report(),'complete_correction_identity':True,'P5_zero_output':-1,'new_producer_bindings':['ng_D','ng_b','ng_P5','ng_A','ng_four','ng_K'],'full_parent_sign_symmetry':True}

def exact_degree(packet):
 rows=packet['source'];free=packet['free'];fixed=packet['fixed_numerals'];ring=Algebra(free);v=ring.var
 # First independently expand both actual cancellation cones.
 small=Algebra(['x','a','z','g','h']);x,a,z,g,h=[small.var(n) for n in ['x','a','z','g','h']]
 six=x*x+2*x*g+g*g+2*a*z*x+2*a*z*g-h*z*z
 check(six==(x+a*z+g)**2-(a*a+h)*z*z,'six-term polynomial identity')
 for name,xc,zc,gc in [('norm_main','wn2','R10a','gam'),('norm_input','W','index_rhs','modulus_multiple')]:
  check(traced(rows,{xc:x,'R12':a,zc:z,gc:g,'a4m5':h})(name)==six,'actual norm cone '+name)
 leaders={n:(0 if n in fixed else 1,v(n)) for n in free};naive={n:t[0] for n,t in leaders.items()}
 def const(n):return (0,ring.const(n)) if n else (-1,ring.const(0))
 def get(n):return const(n) if type(n)==int else leaders[n]
 def add(a,b,sign=1):
  m=max(a[0],b[0]);p=(a[1] if a[0]==m else ring.const(0))+sign*(b[1] if b[0]==m else ring.const(0))
  check(bool(p.c) or m==-1,'unaccounted leading cancellation');return m,p
 def mul(a,b):return (a[0]+b[0],a[1]*b[1]) if a[1].c and b[1].c else const(0)
 def prod(*args):
  value=const(1)
  for arg in args:value=mul(value,arg)
  return value
 for name,op,left,right in rows:
  a0=0 if type(left)==int else naive[left];b0=0 if type(right)==int else naive[right];naive[name]=a0+b0 if op=='*' else max(a0,b0)
  if name in ['norm_main','norm_input']:
   xc,zc,gc=('wn2','R10a','gam') if name=='norm_main' else ('W','index_rhs','modulus_multiple')
   x,a,z,g,h=[get(n) for n in [xc,'R12',zc,gc,'a4m5']]
   terms=[prod(x,x),prod(const(2),x,g),prod(g,g),prod(const(2),a,z,x),prod(const(2),a,z,g),prod(const(-1),h,z,z)]
   top=const(0)
   for t in terms:top=add(top,t)
   leaders[name]=top
  else:leaders[name]=mul(get(left),get(right)) if op=='*' else add(get(left),get(right),1 if op=='+' else -1)
 q=v('Bm1')*v('Jrep');k=v('eta')+v('zeta');gamma=v('rho')+v('sigma');C1=q-v('F')-v('Z')-v('alpha')-v('twice_cell_bits')*v('x');tr=v('w')*C1-v('transport_quotient')*q
 expected=-32*v('h')*gamma*v('delta')**2*v('i')**12*k**27*v('w')**26*v('s')**53*q**197*(q-v('F'))**4*tr
 check(leaders[packet['output']][0]==325 and leaders[packet['output']][1]==expected,'uniform exact325 leader')
 exps={'Bm1':202,'Jrep':202,'h':1,'rho':1,'delta':2,'i':12,'eta':27,'w':26,'s':53,'transport_quotient':1};mon=tuple(exps.get(n,0) for n in ring.names)
 check(expected.c.get(mon)==32,'uniform nonzero32 coefficient');check(sum(e for n,e in exps.items() if n not in fixed)==325,'degree-zero fixed coefficients')
 return {'per_row':{n:leaders[n][0] for n,_,_,_ in rows},'exact_degree':325,'naive':naive[packet['output']],'leader':expected.report(),'basis':list(ring.names),'distinguished_monomial':exps,'distinguished_coefficient':32,'both_actual_norm_cones_expanded':True}

def run(root,staged):
 check(len(PINS)==3,'final frozen pins absent');auth={}
 def find(name):return staged/name if (staged/name).exists() else root/name
 for name,pin in PINS.items():check(H(find(name).read_bytes())==pin,'author '+name);auth[name]=pin
 author=decode(find('complete92_norm_unit_guard.json').read_bytes());check(author['source_sha256']==PINS['complete92_norm_unit_guard.py'],'author helper binding')
 for name,pin in author['pins'].items():check(H(find(name).read_bytes())==pin,'dependency '+name);auth[name]=pin
 raw=(root/'complete84_scaled_strong_output.json').read_bytes();check(H(raw)==PARENT,'actual84 source');old=decode(raw)['packet'];child=author['packet'];snapshot=J(old)
 ninety_raw=find('complete90_signed_root_elimination.json').read_bytes();check(H(ninety_raw)=='ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22','actual90 source');ninety=decode(ninety_raw)['packet'];snapshots=[J(old),J(child),J(ninety)]
 live_source(old);cost=live_source(child);check(cost=={'total':92,'M':52,'A':40},'complete92 ledger')
 deps={n:{n} for n in old['free']};retained=[];removed=[]
 for row in old['source']:
  n,op,a,b=row;deps[n]=set().union(*(deps[t] for t in [a,b] if type(t)==str));(removed if 'f' in deps[n] else retained).append(list(row))
 check(len(retained)==67 and len(removed)==17 and child['source']==retained+TAIL,'complete92 literal reconstruction')
 check(retained==ninety['source'][:67],'literal shared67 prefix with90')
 check(child['free']==[n for n in old['free'] if n!='f'],'all24 supplied values');check(child['witnesses']==[n for n in old['witnesses'] if n!='f'] and len(child['witnesses'])==17,'17 positive witnesses')
 for key in ['ordinary_input','fixed_numerals']:check(child[key]==old[key],'inherited '+key)
 check(old['witness_domain']=='strictly positive integers' and child['witness_domain']=='strictly positive integers; inherited valid fixed-program recipe','unchanged positive domain with explicit recipe clarification')
 check(child['ledger']==cost and child['exact_degree']==325 and child['universal_polynomial_claimed'] is True and child['same_positive_zero_tuples_as90'] is True,'author complete ledger/degree/domain metadata')
 algebra=exact_algebra(old,child,ninety);degree=exact_degree(child);check(J(old)==snapshot and snapshots==[J(old),J(child),J(ninety)],'untouched parents and author packet')
 squares={x*x%4 for x in range(4)};possible={(a*a-d*b*b)%4 for a in range(4) for b in [0,2] for d in range(4)};check(possible==squares and 2 not in possible,'K modulo4 excludes -2')
 return {'status':'PASS','source_sha256':H(Path(__file__).read_bytes()),'pins':auth,'source':{'ledger':cost,'retained_rows':retained,'removed_f_dependent_rows':removed,'appended_rows':child['source'][67:],'complete_source_sha256':H(J(child['source'])),'live_supplied_ports':len(child['free']),'parent_immutable':True},'algebra':algebra,'degree':degree,'mod4_K_residues':sorted(possible),'scope':{'only_new_reviewer_executed':True,'no_native_fixture':True,'proof':'Integer-domain/positive reconstruction reviewed separately in companion MD; exact source identities do not substitute for that proof.'}}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--artifacts',type=Path);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=p.parse_args();result=run(args.root,args.artifacts or args.root)
 if args.output:
  with args.output.open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
 else:check(equal(result,decode(args.expect.read_bytes())),'exact receipt comparison')
 print('PASS independent complete92:52M40A,17w,whole unit guard/correction/integer interface,uniform degree325')

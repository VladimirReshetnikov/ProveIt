"""Independent complete90 source, quotient-ring and homogeneous-degree audit.
Only this fresh reviewer executes. All author/predecessor files are inert.
"""
from pathlib import Path
import argparse, hashlib, json
from collections import Counter
AUTHOR_PINS = {'complete90_signed_root_elimination.py': '5f41f627ef6649b7dc975f3500f99ede576b156fd787423408b2433a1cd0170c', 'complete90_signed_root_elimination.json': 'ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22', 'complete90_signed_root_elimination.md': '52211f6ab29781ea23a1fe07d8644f4012ca4740658b4e1f42b618a5fc0fb8ec'}
PARENT_PIN='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf'
def require(ok,msg):
 if not ok: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def unique(p):
 d={}
 for k,v in p:
  require(k not in d,'duplicate key');d[k]=v
 return d
def reject(x):raise ValueError('noninteger JSON '+x)
def read(b):return json.loads(b,object_pairs_hook=unique,parse_float=reject,parse_constant=reject)
def typed(a,b):
 if type(a)!=type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
class Ring:
 def __init__(self,names):self.names=sorted(set(names));self.n=len(self.names);self.zero=(0,)*self.n
 def c(self,n):return {self.zero:n} if n else {}
 def v(self,name):
  e=list(self.zero);e[self.names.index(name)]=1;return {tuple(e):1}
 def add(self,a,b,sign=1):
  z=dict(a)
  for e,c in b.items():z[e]=z.get(e,0)+sign*c
  return {e:c for e,c in z.items() if c}
 def mul(self,a,b):
  z={}
  for u,c in a.items():
   for v,d in b.items():
    e=tuple(x+y for x,y in zip(u,v));z[e]=z.get(e,0)+c*d
  return {e:c for e,c in z.items() if c}
 def prod(self,*a):
  z=self.c(1)
  for p in a:z=self.mul(z,p)
  return z
 def pow(self,a,n):
  z=self.c(1)
  for _ in range(n):z=self.mul(z,a)
  return z
 def record(self,p):
  e=[[list(v),c] for v,c in sorted(p.items())];return {'terms':len(p),'sha256':digest(canonical(e))}
def closure(rows,free,output):
 defs={};known=set(free)
 for row in rows:
  require(type(row)==list and len(row)==4,'row schema');n,op,a,b=row
  require(n not in known and op in ['+','-','*'],'SSA/op')
  require(all(type(v)==int or(type(v)==str and v in known) for v in [a,b]),'topology')
  known.add(n);defs[n]=row
 live=set();leaves=set();todo=[output]
 while todo:
  v=todo.pop()
  if type(v)==int:continue
  if v in live or v in leaves:continue
  if v in defs:live.add(v);todo.extend(defs[v][2:])
  else:leaves.add(v)
 require(live==set(defs) and leaves==set(free),'full paid/free liveness')
 c=Counter(r[1] for r in rows);return {'M':c['*'],'A':c['+']+c['-'],'total':len(rows),'live_ports':len(leaves)}
def expand(ring,rows,cuts,output):
 defs={r[0]:r for r in rows};memo=dict(cuts)
 def at(n):
  if type(n)==int:return ring.c(n)
  if n not in memo:
   require(n in defs,'uncut free value '+n);_,op,a,b=defs[n];a,b=at(a),at(b)
   memo[n]=ring.mul(a,b) if op=='*' else ring.add(a,b,1 if op=='+' else -1)
  return memo[n]
 return at(output)
def reduce_square(ring,p,name,D):
 idx=ring.names.index(name);out={};cache={0:ring.c(1)}
 for e,c in p.items():
  n=e[idx]//2
  if n not in cache:cache[n]=ring.pow(D,n)
  v=list(e);v[idx]%=2;out=ring.add(out,ring.mul({tuple(v):c},cache[n]))
 return out
APPEND=[
 ['er_ic2','*','i','c2'],['er_kS','*','er_ic2','aux_coefficient_root'],['er_D','+','er_kS',1],
 ['er_RD','*','r_lhs','er_D'],['er_b','+','R10a','er_RD'],['er_u','*','R10a','auxiliary_quotient'],
 ['er_u2','*','er_u','er_u'],['er_p','*','er_D','er_u2'],['er_b2','*','er_b','er_b'],
 ['er_P5a','*','norm_triple','norm_index'],['er_P5','*','er_P5a','norm_transport'],
 ['er_C','*','er_P5','R16'],['er_L','*','er_C','er_p'],['er_M','*','er_C','er_b2'],
 ['er_Pc','-','er_P5','er_C'],['er_Z','*','er_Pc','aux_y2'],['er_LM','+','er_L','er_M'],
 ['er_LMZ','+','er_LM','er_Z'],['er_alpha','-','er_LMZ',1],['er_alpha2','*','er_alpha','er_alpha'],
 ['er_prod','*','er_L','er_M'],['er_four','*',4,'er_prod'],['elimination_polynomial','-','er_alpha2','er_four']]
def algebra(old,new):
 r=Ring(['d','c','R','i','T','y','f','N0','Nk','Nt']);v=r.v;one=r.c(1)
 d,c,R,i,T,y,f=[v(n) for n in ['d','c','R','i','T','y','f']];P=r.prod(v('N0'),v('Nk'),v('Nt'))
 Q=r.prod(r.pow(d,2),r.pow(i,2),r.pow(c,4));D=r.add(one,r.prod(d,r.pow(i,2),r.pow(c,4)))
 b=r.add(c,r.mul(R,D));u=r.mul(c,T)
 A=r.add(r.mul(Q,r.add(r.prod(D,r.pow(u,2)),r.pow(b,2))),r.mul(r.add(Q,one,-1),r.pow(y,2)),-1)
 alpha=r.add(r.mul(P,A),one,-1);beta=r.prod(r.c(2),P,Q,u,b);result=r.add(r.pow(alpha,2),r.prod(D,r.pow(beta,2)),-1)
 cuts=dict(zip(['A','R10a','r_lhs','i','auxiliary_quotient','y_aux','f','norm_triple','norm_index','norm_transport'],[d,c,R,i,T,y,f,v('N0'),v('Nk'),v('Nt')]))
 child=expand(r,new,cuts,'elimination_polynomial');require(child==result,'entire90 field norm')
 parent=expand(r,old,cuts,'polynomial');reduced=reduce_square(r,parent,'f',D)
 target=r.mul(d,r.add(alpha,r.mul(beta,f),-1));require(reduced==target,'entire84 quotient-ring identity')
 require(expand(r,new,cuts,'er_D')==D,'integer D actual cone')
 require(expand(r,new,cuts,'er_b')==b,'denominator b actual cone')
 # Exact P5=0 case, without evaluating a purported native tuple.
 pzero=dict(cuts);pzero['norm_triple']={};require(expand(r,new,pzero,'elimination_polynomial')==one,'zero denominator P5 case')
 return {'whole90_norm':r.record(result),'whole84_reduced_mod_f2_minus_D':r.record(reduced),'integer_D':r.record(D),'b':r.record(b),'P5_zero_output':1,'formal_basis':r.names}
def degree(rows,free,fixed):
 r=Ring(free);v=r.v;defs={x[0]:x for x in rows}
 # Expand the two ACTUAL norm cones independently before using the six-term formula.
 rr=Ring(['xx','aa','zz','gg','HH']);xx,aa,zz,gg,HH=[rr.v(n) for n in ['xx','aa','zz','gg','HH']]
 expected=rr.add(rr.pow(rr.add(rr.add(xx,rr.mul(aa,zz)),gg),2),rr.mul(rr.add(rr.pow(aa,2),HH),rr.pow(zz,2)),-1)
 six=rr.add(rr.add(rr.add(rr.pow(xx,2),rr.prod(rr.c(2),xx,gg)),rr.pow(gg,2)),rr.mul(HH,rr.pow(zz,2)),-1)
 six=rr.add(six,rr.add(rr.prod(rr.c(2),aa,zz,xx),rr.prod(rr.c(2),aa,zz,gg)));require(six==expected,'independent six-term identity')
 for norm,x,z,g in [('norm_main','wn2','R10a','gam'),('norm_input','W','index_rhs','modulus_multiple')]:
  cuts={x:xx,'R12':aa,z:zz,g:gg,'a4m5':HH}
  require(expand(rr,rows,cuts,norm)==six,'literal norm-cone cancellation '+norm)
 env={n:(0 if n in fixed else 1,v(n)) for n in free};naive={n:d for n,(d,p) in env.items()}
 def const(n):return (0,r.c(n)) if n else (-1,{})
 def val(n):return const(n) if type(n)==int else env[n]
 def plus(a,b,sign=1):
  d=max(a[0],b[0]);p=r.add(a[1] if a[0]==d else {},b[1] if b[0]==d else {},sign)
  require(bool(p) or d<0,'unexpected highest cancellation');return d,p
 def times(a,b):return (a[0]+b[0],r.mul(a[1],b[1])) if a[1] and b[1] else (-1,{})
 def prod(*vs):
  out=const(1)
  for x in vs:out=times(out,x)
  return out
 for n,op,a,b in rows:
  da=0 if type(a)==int else naive[a];db=0 if type(b)==int else naive[b];naive[n]=da+db if op=='*' else max(da,db)
  if n in ['norm_main','norm_input']:
   x,z,g=('wn2','R10a','gam') if n=='norm_main' else ('W','index_rhs','modulus_multiple')
   x,a0,z,g,H=[val(k) for k in [x,'R12',z,g,'a4m5']]
   terms=[prod(x,x),prod(const(2),x,g),prod(g,g),prod(const(2),a0,z,x),prod(const(2),a0,z,g),prod(const(-1),H,z,z)]
   got=const(0)
   for term in terms:got=plus(got,term)
   env[n]=got
  else:env[n]=times(val(a),val(b)) if op=='*' else plus(val(a),val(b),1 if op=='+' else -1)
 q=r.mul(v('Bm1'),v('Jrep'));k=r.add(v('eta'),v('zeta'));gamma=r.add(v('rho'),v('sigma'))
 cc=q
 for p in [v('F'),v('Z'),v('alpha'),r.mul(v('twice_cell_bits'),v('x'))]:cc=r.add(cc,p,-1)
 tt=r.add(r.mul(v('w'),cc),r.mul(v('transport_quotient'),q),-1)
 want=r.prod(r.c(1024),r.pow(v('h'),2),r.pow(gamma,2),r.pow(v('delta'),4),r.pow(v('i'),12),r.pow(k,30),r.pow(v('w'),36),r.pow(v('s'),66),r.pow(q,246),r.pow(r.add(q,v('F'),-1),4),r.pow(tt,2))
 require(env['elimination_polynomial']==(406,want),'uniform full highest polynomial')
 exps={'Bm1':252,'Jrep':252,'h':2,'rho':2,'delta':4,'i':12,'eta':30,'w':36,'s':66,'transport_quotient':2}
 mon=tuple(exps.get(n,0) for n in r.names);require(want.get(mon)==1024,'uniform nonzero coefficient')
 require(sum(e for n,e in exps.items() if n not in fixed)==406,'weighted degree')
 return {'per_row':{n:env[n][0] for n,_,_,_ in rows},'naive':naive['elimination_polynomial'],'exact':406,'leading_polynomial':r.record(want),'leading_basis':r.names,'distinguished_monomial':exps,'distinguished_coefficient':1024,'actual_norm_cones_expanded':True}
def run(root,artifacts):
 require(len(AUTHOR_PINS)==3,'final author pins absent');authenticated={}
 def locate(name):return artifacts/name if (artifacts/name).exists() else root/name
 for n,pin in AUTHOR_PINS.items():
  b=locate(n).read_bytes();require(digest(b)==pin,'author '+n);authenticated[n]=pin
 author=read(locate('complete90_signed_root_elimination.json').read_bytes())
 require(author['source_sha256']==AUTHOR_PINS['complete90_signed_root_elimination.py'],'author helper/receipt byte binding')
 for n,pin in author['parent_pins'].items():
  b=locate(n).read_bytes();require(digest(b)==pin,'dependency '+n);authenticated[n]=pin
 pb=(root/'complete84_scaled_strong_output.json').read_bytes();require(digest(pb)==PARENT_PIN,'parent source')
 parent=read(pb)['packet'];child=author['packet'];old=parent['source'];new=child['source'];snapshot=canonical(parent)
 require(child['universal_polynomial_claimed'] is True and child['same_retained_positive_zero_projection'] is True and child['restored_positive_f_unique'] is True,'reviewed positive-domain metadata')
 require([r for r in old if 'f' in r[2:]]==[['L16','*','f','f'],['auxiliary_Tf','*','auxiliary_quotient','f']],'literal f sign symmetry')
 require([r for r in old if 'auxiliary_quotient' in r[2:]]==[['auxiliary_Tf','*','auxiliary_quotient','f']],'literal T sign symmetry')
 closure(old,parent['free'],parent['output']);d={n:{n} for n in parent['free']};keep=[];drop=[]
 for row in old:
  n,op,a,b=row;d[n]=set().union(*(d[x] for x in [a,b] if type(x)==str));(drop if 'f' in d[n] else keep).append(list(row))
 require(len(keep)==67 and len(drop)==17,'source dependence census');require(new==keep+APPEND,'all90 reconstructed rows')
 require(child['free']==[n for n in parent['free'] if n!='f'],'24 supplied values')
 require(child['witnesses']==[n for n in parent['witnesses'] if n!='f'] and len(child['witnesses'])==17,'17 witnesses')
 for k in ['ordinary_input','fixed_numerals','witness_domain']:require(child[k]==parent[k],'unchanged interface '+k)
 cost=closure(new,child['free'],child['output']);require(cost=={'M':52,'A':38,'total':90,'live_ports':24},'paid cost')
 require(child['ledger']=={k:cost[k] for k in ['M','A','total']} and child['exact_degree']==406,'author full ledger and degree metadata')
 require(author['structural']['retained_literal_rows']==keep and author['structural']['removed_f_dependent_rows']==drop and author['structural']['appended_rows']==APPEND,'author closure records')
 identities=algebra(old,new);degrees=degree(new,child['free'],child['fixed_numerals'])
 require(canonical(parent)==snapshot,'parent immutability')
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'pins':authenticated,'source':{'retained_rows':67,'removed_f_dependent_rows':drop,'appended_rows':APPEND,'ledger':cost,'whole_array_sha256':digest(canonical(new)),'unchanged_retained_interface':True},'algebra':identities,'degree':degrees,'scope':{'predecessor_or_author_program_executed':False,'new_reviewer_only':True,'native_fixture_computed':False,'semantic_argument':'Proof review is in the companion MD; no finite arithmetic sample substitutes for it.'}}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=ap.parse_args()
 result=run(args.root,args.artifacts or args.root)
 if args.output:
  with args.output.open('x') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
 else:require(typed(result,read(args.expect.read_bytes())),'receipt exactness')
 print('PASS independent complete90: full90 source/52M38A/17w; complete field norm; uniform degree406')

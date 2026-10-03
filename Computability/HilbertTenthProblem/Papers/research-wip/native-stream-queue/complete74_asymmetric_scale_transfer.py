#!/usr/bin/env python3
"""Literal asymmetric-X transfer of three complete74 sources.
Source/receipt/proof pins only; no historical module is imported.
"""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'review_asymmetric_retained109_math.md': '0f9ff2fc994d54af9221e604cd9ec32890539e53a5fae3d951ad064fd64c04c5', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_signed_projection_elimination101.md': '55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b'}
MODES=('raw30','positive22','signed20')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs,fixed=()):
 known=set(free);defs={};degree={x:0 if x in fixed else 1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e



def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 name='square_0'
 for i in range(1,len(pairs)):
  n=f'sum_{i}';out.append([n,'+',name,f'square_{i}']);name=n
 return out,name

def consumers(p,n):
 return {'source':[r[0]for r in p['source']if n in r[2:]],'comparisons':[i for i,pair in enumerate(p['comparisons'])if n in pair]}

def check_parent(p):
 rows=p['source'];pairs=p['comparisons'];d={n:(o,a,b)for n,o,a,b in rows};mode=p['mode']
 c='c'if mode=='raw30'else'R10a';k='k'if mode=='raw30'else'R10b'
 need(d['r1']==('+','r',1)and d['hpm1']==('*','h','UM')and d['R11']==('+','r1','hpm1'),'actual index cone')
 need(d['jc']==('*','j',c)and d['H17']==('-','jc','r')and d['aux_u_rhs']==('-','of',c)and d['of']==('*','o','f'),'actual auxiliary cone')
 need(d['H2']==('*','H17','H17')and ['H17','aux_u_rhs']in pairs,'norm and auxiliary comparison both retained')
 need(d['ksn2']==('*',k,'sn2')and d['first_next']==('+','first_root_base',k),'actual supplied or computed k is retained')
 need(consumers(p,'r')=={'source':['r1','H17'],'comparisons':[pairs.index(['r','r_lhs'])]},'all three r consumers')
 need(consumers(p,'j')=={'source':['jc'],'comparisons':[]}and consumers(p,'h')=={'source':['hpm1'],'comparisons':[]},'literal single j/h consumers')
 need(consumers(p,'zquot')=={'source':['local_rhs'],'comparisons':[]}and consumers(p,'r1')=={'source':['R11'],'comparisons':[]},'literal quotient and r1 privacy')
 need(consumers(p,'jc')=={'source':['H17'],'comparisons':[]}and consumers(p,'aux_u_rhs')=={'source':[],'comparisons':[pairs.index(['H17','aux_u_rhs'])]},'private auxiliary row outputs')
 need(d['local_rhs']==('*','zquot','qm1'if mode=='raw30'else'repunit'),'actual transport quotient product')
 need(d['rproduct']==('*','gap','Lm1')and d['r_lhs']==('+','rproduct','mask')and d['mask']==('*','mask_factor','Jrep')and d['mask_factor']==('+','MC','qMF')and d['qMF']==('*','q','MF'),'actual packing mask cone')
 poly,out=finalize(rows,pairs);need(poly==p['polynomial_source']and out==p['output'],'complete literal parent finalizer')
 free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
 need(ledger(rows,free,[v for pair in pairs for v in pair],p['fixed_numerals'])[:2]==(40,34),'actual 74 parent ledger')
 return c

def authenticated(root=None):
 root=Path(root)if root is not None else Path(__file__).resolve().parent;blobs={}
 for n,h in PINS.items():
  paths=[root/n,root/Path(n).name,Path(__file__).resolve().parent/n,Path(__file__).resolve().parent/Path(n).name]
  path=next((p for p in paths if p.exists()),paths[0]);data=path.read_bytes()
  need(sha(data)==h,'Pinned blob '+n);blobs[n]=data
 return blobs

def canonical_parent(mode='signed20',*,root=None):
 need(type(mode)is str and mode in MODES,'exact selected mode')
 receipt=json.loads(authenticated(root)['complete74_factored_first_norm.json'])
 forms=receipt['forms'];need(tuple(f['mode']for f in forms)==MODES,'literal three-form parent boundary')
 p=next(f['packet']for f in forms if f['mode']==mode);check_parent(p)
 return p

def _build(parent):
 p=copy.deepcopy(parent);rows=p['source'];definitions={r[0]:r[1:]for r in rows}
 need(definitions['wn2']==['*','w','n2']and definitions['sn2']==['*','s','n2'],'literal two scale ports')
 need(definitions['n2']==['*','Lbig','q']and definitions['Lbig']==['*','q','q'],'literal paid cube')
 need(consumers(p,'w')=={'source':['wn2'],'comparisons':[]},'w has exactly one source consumer')
 for row in rows:
  if row[0]=='wn2':row[3]='q'
 p['polynomial_source'],p['output']=finalize(rows,p['comparisons'])
 free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']]
 m,a,d=ledger(rows,free,[v for pair in p['comparisons']for v in pair],p['fixed_numerals'])
 pm,pa,pd=ledger(p['polynomial_source'],free,[p['output']],p['fixed_numerals'])
 need((m,a)==(40,34)and(pm+pa)=={'raw30':130,'positive22':106,'signed20':100}[p['mode']],'complete unchanged costs')
 p['certificate_ledger']=dict(operations=m+a,M=m,A=a,free=sorted(free),all_gates_live=True,literal_degree_upper_bound=d)
 p['polynomial_ledger']=dict(operations=pm+pa,M=pm,A=pa,free=sorted(free),all_gates_live=True,literal_degree_upper_bound=pd)
 p['exact_polynomial_degree']=44 if p['mode']=='raw30'else 68
 p['historical_parent_transformation']=p.pop('transformation')
 p['asymmetric_scale']={
  'old_X':'w*q^3','new_X':'w*q','unchanged_Y':'s*q^3','sole_changed_instruction':['wn2','*','w','q'],
  'forward_assignment':'w_new=q^2*w_old; every other supplied coordinate fixed',
  'rational_pullback':'w_old=w_new/q^2, requiring q!=0',
  'positive_zero_bijection_proved':True,'all_value_forward_polynomial_identity':True,
  'unconditional_integer_inverse':False,'no_change_to_ordinary_input_or_compiler_numerals':True,
  'parent_exact_polynomial_degree':parent['exact_polynomial_degree'],
  'parent_comparison_map':list(range(len(p['comparisons'])))}
 return p

def build(mode='signed20',*,root=None):return _build(canonical_parent(mode,root=root))
def rewrite(parent,mode='signed20',*,root=None):
 p=canonical_parent(mode,root=root);need(exact(parent,p),'only exact complete selected symmetric parent');return _build(p)
def checked(packet,*,root=None):
 need(type(packet)is dict and type(packet.get('mode'))is str,'exact packet/mode')
 p=build(packet['mode'],root=root);need(exact(packet,p),'only exact complete asymmetric packet');return p
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def _values(p,values,signed,*,rational=False):
 need(type(signed)is bool,'exact signed flag')
 need(type(values)is dict and set(values)==set(p['polynomial_ledger']['free']),'exact complete supplied dictionary')
 types=(int,Fraction)if rational else(int,)
 need(all(type(k)is str and type(v)in types for k,v in values.items()),'exact supplied number types')
 if not signed:need(all(v>0 for v in values.values()),'strict positive supplied entries')
 return dict(values)
def _q(p,v):return v['q']if p['mode']=='raw30'else v['Bm1']*v['Jrep']+1
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);return numeric(p['polynomial_source'],_values(p,values,signed))[p['output']]
def forward_assignment(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);v=_values(p,values,signed);q=_q(p,v);v['w']*=q*q;return v
def rational_pullback(packet,values,*,root=None):
 p=checked(packet,root=root);v=_values(p,values,True,rational=True);q=_q(p,v);need(q!=0,'rational inverse requires q!=0');v['w']=Fraction(v['w'])/(q*q);return v
def restore_assignment(packet,values,*,root=None):
 p=checked(packet,root=root);v=_values(p,values,False);q=_q(p,v)
 need(v['w']%(q*q)==0,'positive integer inverse needs q^2 dividing w; proved at positive zeros on valid compiler slices')
 v['w']//=q*q;return v

# Small exact coefficient engine for local source identities and uniform leaders.
def padd(a,b,s=1):
 d=dict(a)
 for k,v in b.items():d[k]=d.get(k,0)+s*v
 return{k:v for k,v in d.items()if v}
def pmul(a,b):
 d={}
 for u,x in a.items():
  for v,y in b.items():
   k=tuple(i+j for i,j in zip(u,v));d[k]=d.get(k,0)+x*y
 return{k:v for k,v in d.items()if v}

def local_proofs():
 one={(0,0):1};w={(1,0):1};q={(0,1):1};q2=pmul(q,q)
 need(pmul(pmul(w,q2),q)==pmul(w,pmul(q2,q)),'literal first-scale forward coefficient identity')
 one={(0,)*5:1};W,a,k,rho,H=[{tuple(int(i==j)for i in range(5)):1}for j in range(5)];sq=lambda x:pmul(x,x)
 mu=padd(padd(W,pmul(a,k)),pmul(rho,H));delta=padd(sq(a),H)
 left=padd(padd(sq(mu),pmul(delta,sq(k)),-1),one,-1)
 terms=[(sq(W),1),(pmul(pmul(a,W),k),2),(pmul(pmul(rho,W),H),2),
  (pmul(pmul(pmul(a,rho),k),H),2),(pmul(sq(rho),sq(H)),1),(pmul(H,sq(k)),-1),(one,-1)]
 right={}
 for t,c in terms:right=padd(right,{m:c*v for m,v in t.items()})
 need(left==right,'exact full input cancellation in independent atoms')
 return {'scale_forward_expansion':[[[1,3],1]],'input_atom_order':['W','a','kappa','rho','H'],
  'input_residual_expansion':[[list(m),c]for m,c in sorted(left.items())]}

def structural(parent,child):
 need(parent['comparisons']==child['comparisons']and parent['witnesses']==child['witnesses'],'unchanged entire interface')
 differences=[(a,b)for a,b in zip(parent['source'],child['source'])if a!=b]
 need(differences==[(['wn2','*','w','n2'],['wn2','*','w','q'])],'exactly one changed instruction')
 need(len(parent['source'])==len(child['source'])and len(parent['polynomial_source'])==len(child['polynomial_source']),'entire source lengths unchanged')
 ring=RingDAG();free=parent['polynomial_ledger']['free']
 def run(rows):
  e={n:ring.val(n)for n in free}
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else ring.val(a);b=e[b]if type(b)is str else ring.val(b)
   e[n]=ring.mul(a,b)if o=='*'else ring.add(a,b,1 if o=='+'else-1)
   if n=='wn2':e[n]=ring.val('proved_common_X')
  return e
 old,new=run(parent['polynomial_source']),run(child['polynomial_source'])
 for row in parent['polynomial_source']:need(old[row[0]]==new[row[0]],'every computed gate after the proved scale cut')
 for i in range(len(parent['comparisons'])):need(old[f'residual_{i}']==new[f'residual_{i}'],'every residual after scale cut')
 need(old[parent['output']]==new[child['output']],'complete polynomial identity after proved scale cut')
 return dict(all_computed_gates=len(parent['polynomial_source']),residuals=len(parent['comparisons']),whole_polynomial_identity=True,
  cut='The exact local w*q^3=(q^2*w)*q expansion proves wn2 equality; literal sole-w-consumer check permits the common-X substitution.')

def _degree(p):
 definitions={n:(o,a,b)for n,o,a,b in p['source']};free=p['polynomial_ledger']['free'];d={n:0 if n in p['fixed_numerals']else 1 for n in free}
 for n,o,a,b in p['source']:
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0;d[n]=da+db if o=='*'else max(da,db)
 need(d['wn2']==2 and d['sn2']==4 and d['UM']==6,'actual asymmetric scale degrees')
 bounds=[max(d[a]if type(a)is str else 0,d[b]if type(b)is str else 0)for a,b in p['comparisons']]
 if p['mode']=='raw30':
  top=p['comparisons'].index(['L9','R9']);degree=44
  need(d['first_root_base']==11 and bounds[top]==22,'raw actual first coefficient leader')
  leader=[{'coefficient':1,'powers':{'w':4,'s':8,'k':4,'q':28}}]
  leader_formula='w^4*s^8*k^4*q^28';fixed=[];input_degrees=None
 else:
  want={'A':('+','a_square','a4m5'),'a_square':('*','R12','R12'),'a4m5':('+','a4',3),'a4':('*',4,'R12'),
   'index_product':('*','delta','A'),'index_rhs':('+','odd_index','index_product'),
   'difference_multiple':('*','index_rhs','R12'),'exponent_partial':('+','W','difference_multiple'),
   'modulus_multiple':('*','rho','a4m5'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),
   'mu2':('*','exponent_rhs','exponent_rhs'),'kappa2':('*','index_rhs','index_rhs'),
   'scaled_kappa2':('*','A','kappa2'),'norm_rhs':('+','scaled_kappa2',1)}
  for n,r in want.items():need(definitions[n]==r,'literal input cone '+n)
  need([d[n]for n in('W','R12','index_rhs','rho','a4m5')]==[1,6,13,1,6],'actual input weights')
  input_degrees=[2,20,8,26,14,32,0];bounds[p['comparisons'].index(['mu2','norm_rhs'])]=32
  # Check the unique auxiliary leader from its literal actual coefficient.
  want={'R10b':('+','eta','zeta'),'R10a':('+','ksn2','eta'),'ksn2':('*','R10b','sn2'),
   'c2':('*','R10a','R10a'),'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),
   'jc':('*','j','R10a'),'H17':('-','jc','r'),'H2':('*','H17','H17'),
   'aux_y2':('*','y_aux','y_aux'),'aux_square_gap':('-','H2','aux_y2'),
   'L17':('*','ic22','aux_square_gap'),'P17':('-',1,'aux_y2')}
  for n,r in want.items():need(definitions[n]==r,'literal auxiliary cone '+n)
  need([d[n]for n in('R10a','ic22','H17','L17')]==[5,22,6,34],'actual auxiliary unique leading degrees')
  top=p['comparisons'].index(['L17','P17']);degree=68
  # Exact binomial leader with coefficients, not an all-one specialization.
  k={(1,0):1,(0,1):1};poly={(0,0):1}
  for _ in range(12):poly=pmul(poly,k)
  leader=[{'coefficient':c,'powers':{**{'Bm1':36,'Jrep':36,'s':12,'i':4,'j':4},**({"eta":m[0]}if m[0]else{}),**({"zeta":m[1]}if m[1]else{})}}for m,c in sorted(poly.items())]
  leader_formula='Bm1^36*Jrep^36*s^12*i^4*j^4*(eta+zeta)^12';fixed=['Bm1']
 need(bounds[top]*2==degree and all(v<degree//2 for i,v in enumerate(bounds)if i!=top),'unique highest residual in full source')
 need(degree==p['exact_polynomial_degree'],'current exact degree metadata')
 return dict(exact_degree=degree,residual_degree_upper_bounds=bounds,unique_top_residual=top,whole_polynomial_leader=leader,
  leader_formula=leader_formula,fixed_parameter_dependencies=fixed,projected_input_expanded_term_degrees=input_degrees,
  uniformity='All supplied witnesses and ordinary input have degree one; fixed numeral ports degree zero. The displayed nonzero leader survives every admissible Bm1>0.')
def degree_certificate(packet,*,root=None):
 p=checked(packet,root=root);local_proofs();return _degree(p)

def uadd(a,b,s=1):
 r=[0]*max(len(a),len(b))
 for i,v in enumerate(a):r[i]+=v
 for i,v in enumerate(b):r[i]+=s*v
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def umul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):r[i+j]+=x*y
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def dense(p,b):
 e={n:[b if n=='Bm1'else 3]for n in p['fixed_numerals']};e.update({n:[0,1]for n in p['witnesses']+[p['ordinary_input']]})
 for n,o,a,c in p['polynomial_source']:
  aa=e[a]if type(a)is str else[a];cc=e[c]if type(c)is str else[c]
  e[n]=umul(aa,cc)if o=='*'else uadd(aa,cc,1 if o=='+'else-1)
 result=e[p['output']];degree=p['exact_polynomial_degree'];leader=1 if p['mode']=='raw30'else 4096*b**36
 need((len(result)-1,result[-1])==(degree,leader),'exact complete dense degree/coefficient attainment')
 return dict(Bm1=b,exact_degree=degree,top_coefficient=leader,full_coefficients_sha256=sha(json.dumps(result,separators=(',',':')).encode()))

def verify(root=None):
 blobs=authenticated(root);rng=random.Random(744468);counts=Counter();forms=[];local=local_proofs()
 def rejects(call):
  try:call()
  except(ValueError,TypeError,KeyError):counts['guard_rejections']+=1
  else:raise AssertionError('invalid request accepted')
 for mode in MODES:
  parent=canonical_parent(mode,root=root);p=build(mode,root=root);need(exact(rewrite(parent,mode,root=root),p),'canonical rewrite')
  proof=structural(parent,p);degree=degree_certificate(p,root=root)
  counts['complete_structural_identities']+=1;counts['computed_gate_identities']+=proof['all_computed_gates'];counts['residual_identities']+=proof['residuals'];counts['paid_live_gates']+=p['polynomial_ledger']['operations']
  free=p['polynomial_ledger']['free']
  for case in range(48):
   v={n:rng.randint(1,4)if case<24 else rng.randint(-3,5)for n in free}
   q=_q(p,v);nv=dict(v);nv['w']*=q*q
   old=numeric(parent['polynomial_source'],v);new=numeric(p['polynomial_source'],nv)
   for n,o,a,b in p['polynomial_source']:need(old[n]==new[n],'every evaluated computed register');counts['numeric_gate_identities']+=1
   need(old[parent['output']]==new[p['output']],'entire polynomial forward identity');counts['whole_forward_identities']+=1
   counts['signed_forward_cases']+=case>=24
   if q and case%3==0:
    inv=rational_pullback(p,v,root=root);back=numeric(parent['polynomial_source'],inv);direct=numeric(p['polynomial_source'],v)
    need(back[parent['output']]==direct[p['output']],'entire rational inverse identity');counts['whole_rational_inverse_identities']+=1
   if case in(0,1,24,25):
    public=forward_assignment(p,v,signed=case>=24,root=root);need(public==nv,'public polynomial forward map')
    need(evaluate(p,nv,signed=case>=24,root=root)==old[parent['output']],'public complete evaluator');counts['public_evaluations']+=1
    if case<2:need(restore_assignment(p,public,root=root)==v,'public positive integer roundtrip');counts['positive_coordinate_roundtrips']+=1
  # q=0 is allowed in the polynomial forward direction, never in the rational inverse.
  v={n:1 for n in free}
  if mode=='raw30':v['q']=0
  else:v['Bm1']=-1
  nv=forward_assignment(p,v,signed=True,root=root)
  need(numeric(parent['polynomial_source'],v)[parent['output']]==evaluate(p,nv,signed=True,root=root),'q=0 complete forward identity');counts['zero_q_forward_identities']+=1
  rejects(lambda:rational_pullback(p,v,root=root))
  one={n:1 for n in free}
  for key,value in [('w',0),('w',-1),('eta',True),('eta',1.0)]:
   bad=dict(one);bad[key]=value;rejects(lambda bad=bad:evaluate(p,bad,root=root))
  rejects(lambda:evaluate(p,one,signed=1,root=root))
  nonintegral=dict(one)
  if mode=='raw30':nonintegral['q']=2
  rejects(lambda:restore_assignment(p,nonintegral,root=root))
  bad=dict(one);bad['extra']=1;rejects(lambda:evaluate(p,bad,root=root))
  for field in('source','polynomial_source','comparisons','witnesses','original_comparison_indices','fixed_numerals'):
   bad=copy.deepcopy(p);bad[field]=tuple(bad[field]);rejects(lambda bad=bad:checked(bad,root=root))
  for field in('source','polynomial_source'):
   for i,row in enumerate(p[field]):
    for j in(2,3):
     if type(row[j])is int:
      for value in(bool(row[j]),float(row[j])):
       bad=copy.deepcopy(p);bad[field][i][j]=value;rejects(lambda bad=bad:checked(bad,root=root))
  for key,value in [('exact_polynomial_degree',float(p['exact_polynomial_degree'])),('mode',True),('output','wrong')]:
   bad=copy.deepcopy(p);bad[key]=value;rejects(lambda bad=bad:checked(bad,root=root))
  bad=copy.deepcopy(p);bad['asymmetric_scale']['unconditional_integer_inverse']=True;rejects(lambda:checked(bad,root=root))
  bad=copy.deepcopy(p);bad['source'].append(['dead','+',1,0]);rejects(lambda:checked(bad,root=root))
  rejects(lambda:rewrite(p,mode,root=root))
  for field in('source','comparisons','witnesses','exact_polynomial_degree'):
   bad=copy.deepcopy(parent);bad[field]=None;rejects(lambda bad=bad:rewrite(bad,mode,root=root))
  for field in('source','polynomial_source','comparisons','asymmetric_scale','historical_parent_transformation'):
   x=build(mode,root=root);x[field].clear();need(exact(build(mode,root=root),p),'fresh defensive packet copy');counts['defensive_copy_checks']+=1
  x=canonical_parent(mode,root=root);x['source'].clear();need(exact(canonical_parent(mode,root=root),parent),'fresh parent copy');counts['defensive_copy_checks']+=1
  x=polynomial_source(p,root=root);x.clear();need(polynomial_source(p,root=root)==p['polynomial_source'],'fresh source copy');counts['defensive_copy_checks']+=1
  forms.append(dict(packet=p,full_source_identity=proof,degree_certificate=degree,dense_degree_checks=[dense(p,b)for b in(15,31)]))
 for mode in(None,True,1,'unknown'):rejects(lambda mode=mode:build(mode,root=root))
 # Every public entry authenticates warm changed dependencies; no cache may
 # hide either an ordinary blob mismatch or a real relative proof mismatch.
 with tempfile.TemporaryDirectory(prefix='asymmetric74_')as tmp:
  base=Path(tmp)/'a'/'b';base.mkdir(parents=True)
  for name,data in blobs.items():(base/Path(name).name).write_bytes(data)
  p=build(root=base);parent=canonical_parent(root=base);one={n:1 for n in p['polynomial_ledger']['free']}
  calls=[lambda:canonical_parent(root=base),lambda:build(root=base),lambda:rewrite(parent,root=base),lambda:checked(p,root=base),
   lambda:polynomial_source(p,root=base),lambda:degree_certificate(p,root=base),lambda:evaluate(p,one,root=base),
   lambda:forward_assignment(p,one,root=base),lambda:rational_pullback(p,one,root=base),lambda:restore_assignment(p,one,root=base)]
  for name,data in blobs.items():
   path=base/Path(name).name;path.write_bytes(data+b'\n')
   for call in calls:
    try:call()
    except ValueError as e:need('Pinned blob' in str(e),'authentication precedes subsequent API/domain checks');counts['strict_warm_pin_rejections']+=1
    else:raise AssertionError('mutated dependency accepted')
   path.write_bytes(data)
  for name,data in blobs.items():
   if name.startswith('../'):
    path=base/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data+b'\n')
    try:build(root=base)
    except ValueError as e:need('Pinned blob' in str(e),'canonical proof mismatch rejected despite matching fallback');counts['relative_proof_pin_rejections']+=1
    else:raise AssertionError('canonical mismatch bypassed')
    path.unlink()
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve()),'--root',str(root)],capture_output=True,text=True)
 need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'explicit -O rejection');counts['optimized_mode_rejections']=1
 return dict(status='PASS_COMPLETE74_ASYMMETRIC_SCALE_TRANSFER',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),
  scope=dict(complete_forms=list(MODES),positive_zero_bijections=True,certificate_bound_unchanged=74,universal_polynomial_operation_bound_unchanged=86,
   no_general_optimality_claim=True,no_historical_modules_imported=True,proof='General native bootstrap/inverse integrality is in the companion note with pinned proof dependencies; finite checks below are not full Pell-zero constructions.'),
  local_coefficient_proofs=local,counts=dict(sorted(counts.items())),forms=forms)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();result=verify(a.root)
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=result['status'],counts=result['counts'],forms=[dict(mode=f['packet']['mode'],operations=f['packet']['polynomial_ledger']['operations'],exact_degree=f['packet']['exact_polynomial_degree'])for f in result['forms']]),sort_keys=True))
if __name__=='__main__':main()


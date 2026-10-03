#!/usr/bin/env python3
"""Nonlinear first-index projection scout for three actual complete74 sources.
No parent module is imported. Public scope is the source-pinned CLI receipt.
"""
import argparse,copy,hashlib,itertools,json,random,sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
 'complete75_signed_projection_elimination101.md':'55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}
MODES=('raw30','positive22','signed20')
PORTS=('r','j','h','zquot')
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
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

def build(p):
 check_parent(p);k='k'if p['mode']=='raw30'else'R10b'
 index=p['comparisons'].index([k,'R11']);rows=[]
 for n,o,a,b in p['source']:
  if n in('r1','R11'):continue
  rows.append([n,o,'restored_r'if a=='r'else a,'restored_r'if b=='r'else b])
  if n=='hpm1':rows.extend([['index_partial','-',k,'hpm1'],['restored_r','-','index_partial',1]])
 pairs=[['restored_r'if a=='r'else a,'restored_r'if b=='r'else b]for i,(a,b)in enumerate(p['comparisons'])if i!=index]
 poly,out=finalize(rows,pairs)
 return dict(mode=p['mode'],source=rows,comparisons=pairs,polynomial_source=poly,output=out,
  witnesses=[v for v in p['witnesses']if v!='r'],fixed_numerals=p['fixed_numerals'][:],ordinary_input=p['ordinary_input'],
  parent_comparison_indices=[i for i in range(len(p['comparisons']))if i!=index],removed_parent_comparison_index=index,
  actual_k_port=k,coordinate_pullback='old r = actual k - h*UM - 1',
  all_value_graph_identity=True,positive_zero_equivalence_certified=False,
  positive_parent_slice_condition='actual k > h*UM + 1',
  completeness_from_parent_positive_zeros=True)

def symbolic(p,q):
 ring=RingDAG();free=q['fixed_numerals']+q['witnesses']+[q['ordinary_input']]
 new=ring.run(q['polynomial_source'],free)
 old=ring.run(p['polynomial_source'],free+['r'],{'r':new['restored_r']})
 need(old[f'residual_{q["removed_parent_comparison_index"]}']==(),'deleted index residual vanishes on the graph')
 for j,i in enumerate(q['parent_comparison_indices']):need(old[f'residual_{i}']==new[f'residual_{j}'],'each retained residual agrees exactly')
 common=[r[0]for r in p['source']if r[0]not in('r1','R11')]
 for n in common:need(old[n]==new[n],'each actual computed common register agrees')
 need(old[p['output']]==new[q['output']],'complete SOS graph identity, without imposing equations')
 return dict(common_computed_registers=len(common),retained_residuals=len(q['comparisons']),vanishing_residuals=1,complete_polynomial_identities=1)

# Small exact sparse expansion for the only degree cancellation required.
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
def input_cut():
 # Independent atoms (W,a,kappa,rho,H), with Delta=a^2+H.
 one={(0,)*5:1};W,a,k,rho,H=[{tuple(int(i==j)for i in range(5)):1}for j in range(5)]
 sq=lambda x:pmul(x,x)
 mu=padd(padd(W,pmul(a,k)),pmul(rho,H));delta=padd(sq(a),H)
 lhs=padd(padd(sq(mu),pmul(delta,sq(k)),-1),one,-1)
 terms=[(sq(W),1),(pmul(pmul(a,W),k),2),(pmul(pmul(rho,W),H),2),
  (pmul(pmul(pmul(a,rho),k),H),2),(pmul(sq(rho),sq(H)),1),(pmul(H,sq(k)),-1),(one,-1)]
 rhs={}
 for t,c in terms:rhs=padd(rhs,{m:c*v for m,v in t.items()})
 need(lhs==rhs,'full exact expanded input norm identity')
 weights=(1,8,17,1,8)
 degrees=[max(sum(u*v for u,v in zip(m,weights))for m in t)for t,c in terms]
 need(degrees==[2,26,10,34,18,42,0],'actual projected input term degrees')
 return dict(identity='(W+a*kappa+rho*H)^2-(a^2+H)*kappa^2-1 = W^2+2*a*W*kappa+2*rho*W*H+2*a*rho*kappa*H+rho^2*H^2-H*kappa^2-1',expanded_terms=len(lhs),projected_term_degrees=degrees)

def source_degrees(q):
 e={n:0 for n in q['fixed_numerals']};e.update({n:1 for n in q['witnesses']+[q['ordinary_input']]})
 for n,o,a,b in q['source']:
  da=e[a]if type(a)is str else 0;db=e[b]if type(b)is str else 0;e[n]=da+db if o=='*'else max(da,db)
 bounds=[max(e[a]if type(a)is str else 0,e[b]if type(b)is str else 0)for a,b in q['comparisons']]
 need(e['restored_r']==9 and e['H17']==9,'restored index/auxiliary port degrees')
 if q['mode']=='raw30':
  top=q['comparisons'].index(['L9','R9']);D=52;leader='w^4*s^8*k^4*q^36';need(bounds[top]==26,'raw first norm degree')
 else:
  d={n:(o,a,b)for n,o,a,b in q['source']}
  want={'A':('+','a_square','a4m5'),'a_square':('*','R12','R12'),'a4m5':('+','a4',3),'a4':('*',4,'R12'),
   'index_product':('*','delta','A'),'index_rhs':('+','odd_index','index_product'),
   'difference_multiple':('*','index_rhs','R12'),'exponent_partial':('+','W','difference_multiple'),
   'modulus_multiple':('*','rho','a4m5'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),
   'mu2':('*','exponent_rhs','exponent_rhs'),'kappa2':('*','index_rhs','index_rhs'),
   'scaled_kappa2':('*','A','kappa2'),'norm_rhs':('+','scaled_kappa2',1)}
  for n,row in want.items():need(d[n]==row,'literal local input degree identity '+n)
  top=q['comparisons'].index(['mu2','norm_rhs']);need(bounds[top]==50,'honest naive upper before cancellation');bounds[top]=42;D=84
  leader='16*Bm1^60*delta^4*w^10*s^10*Jrep^60'
 need(all(x<D//2 for i,x in enumerate(bounds)if i!=top),'unique top residual after the explicit input cancellation')
 return dict(exact_degree=D,residual_degree_upper_bounds=bounds,unique_top_residual=top,whole_polynomial_leader=leader,
  uniform_scope='ordinary input and every supplied witness have degree one; actual fixed compiler numeral ports have degree zero; Bm1>0')

# Exact dense univariate execution of the ENTIRE source: a check of the
# uniform symbolic argument above, not a substitute for that argument.
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
def dense(q,b):
 e={n:[b if n=='Bm1'else 3]for n in q['fixed_numerals']};e.update({n:[0,1]for n in q['witnesses']+[q['ordinary_input']]})
 for n,o,a,c in q['polynomial_source']:
  aa=e[a]if type(a)is str else[a];cc=e[c]if type(c)is str else[c]
  e[n]=umul(aa,cc)if o=='*'else uadd(aa,cc,1 if o=='+'else-1)
 result=e[q['output']];D=q['degree_certificate']['exact_degree'];lead=1 if q['mode']=='raw30'else 16*b**60
 need((len(result)-1,result[-1])==(D,lead),'entire univariate expansion attains the proven top degree/coefficient')
 return dict(Bm1=b,exact_degree=D,top_coefficient=lead,all_coefficients_sha256=sha(json.dumps(result,separators=(',',':')).encode()))

def verify(root):
 blobs=pins(root,PINS);parents=json.loads(blobs['complete74_factored_first_norm.json'])
 need(tuple(f['mode']for f in parents['forms'])==MODES,'exact selected three-form boundary')
 cut=input_cut();rng=random.Random(740031);forms=[];totals=Counter();privacy={}
 for f in parents['forms']:
  p=f['packet'];q=build(p);free=q['fixed_numerals']+q['witnesses']+[q['ordinary_input']];eq=len(q['comparisons'])
  M,A,_=ledger(q['source'],free,[v for pair in q['comparisons']for v in pair],q['fixed_numerals']);PM,PA,PD=ledger(q['polynomial_source'],free,[q['output']],q['fixed_numerals'])
  need((M,A)==(40,34)and(PM,PA)==(40+eq,34+2*eq-1),'complete paid source/finalizer ledgers')
  need((len(q['witnesses']),eq,PM+PA)=={'raw30':(29,18,127),'positive22':(21,10,103),'signed20':(19,8,97)}[p['mode']],'complete candidate census')
  q['certificate_ledger']=dict(M=M,A=A,operations=M+A,all_gates_live=True)
  q['polynomial_ledger']=dict(M=PM,A=PA,operations=PM+PA,all_gates_live=True)
  q['degree_certificate']=source_degrees(q);q['naive_degree_upper']=PD
  proof=symbolic(p,q)
  for n,v in proof.items():totals[n]+=v
  totals['live_paid_polynomial_gates']+=PM+PA
  for case in range(32):
   v={n:rng.randrange(1,5)if case<8 else rng.randrange(-3,5)for n in free}
   if case>=24:v={n:Fraction(z,3)for n,z in v.items()};totals['rational_cases']+=1
   new=numeric(q['polynomial_source'],v);vo=dict(v,r=new['restored_r']);old=numeric(p['polynomial_source'],vo)
   need(old[p['output']]==new[q['output']],'complete rational graph identity')
   need(old[f'residual_{q["removed_parent_comparison_index"]}']==0,'actual removed residual zero')
   for j,i in enumerate(q['parent_comparison_indices']):need(old[f'residual_{i}']==new[f'residual_{j}'],'every numeric retained residual');totals['numeric_residual_identities']+=1
   totals['numeric_whole_identities']+=1
  # This is only an off-zero inverse diagnostic, deliberately not a claimed
  # full zero or a valid compiled-program counterexample.
  v={n:1 for n in free};v['Bm1']=15
  if p['mode']=='raw30':v['q']=16
  v['h']=2;new=numeric(q['polynomial_source'],v)
  need(new['restored_r']<0 and new[q['output']]!=0,'off-zero negative inverse is labelled as such')
  diagnostic=dict(restored_r=new['restored_r'],full_child_is_zero=False,valid_compiler_numerals_claimed=False)
  privacy[p['mode']]={n:consumers(p,n)for n in('r','r1','R11','h','hpm1')}
  forms.append(dict(packet=q,structural_proof=proof,dense_checks=[dense(q,b)for b in(15,31)],off_zero_inverse_diagnostic=diagnostic))
 # The packing remainder excludes ZERO, not a negative representative.
 remainder_cases=[]
 for B,J,MC,MF in((16,1,2,4),(16,7,14,4),(32,3,2,4)):
  q=(B-1)*J+1;T=MC*J+1+q*(MF*J-1);need(0<T<q*q-1,'actual mask-range nonzero remainder')
  R=T-(q*q-1);need(R<0 and R%(q*q-1)==T,'negative integer with same valid nonzero remainder')
  remainder_cases.append(dict(B=B,J=J,MC=MC,native_MF=MF,q=q,T=T,negative_representative=R,scope='remainder algebra only, not a complete zero or compiler'))
 return dict(schema='complete74-nonlinear-index-projection-scout-v1',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PINS,
  scope=dict(complete_sources=3,historical_modules_imported=False,certificate_improvement=False,certificate_operations=74,
   algebraic_projection_only=True,unconditional_ring_graph_identity=True,positive_zero_equivalence_certified=False,
   unresolved_obligation='At every positive child zero on a valid fixed compiler slice, prove actual k > h*UM+1; alternatively give a genuine full-zero obstruction.',
   no_universal_frontier_update=True,no_general_optimality_claim=True,public_contract='source-pinned bounded CLI; internal builder is not a hostile-packet API'),
  counts=dict(sorted(totals.items())),local_input_coefficient_identity=cut,actual_parent_consumers=privacy,
  nonzero_remainder_boundary=remainder_cases,forms=forms)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True);ap.add_argument('--output');ap.add_argument('--expect');args=ap.parse_args()
 result=verify(args.root)
 if args.expect:need(exact(result,json.loads(Path(args.expect).read_text())),'exact typed saved receipt')
 if args.output:Path(args.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',counts=result['counts'],certificate_operations=74,positive_zero_equivalence='UNPROVED'),sort_keys=True))
if __name__=='__main__':main()


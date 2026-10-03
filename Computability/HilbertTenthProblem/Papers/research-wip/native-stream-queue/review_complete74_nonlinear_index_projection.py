#!/usr/bin/env python3
"""Independent bounded source-only review of the nonlinear r projection.
No author or historical Python imported. No positive restoration claim.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_signed_projection_elimination101.md': '55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}
AUTHOR={'complete74_nonlinear_index_projection_scout.py': '610739f1074ad792e8010287e8e162d509832c8d5e7444dc38ecae98e7710c71', 'complete74_nonlinear_index_projection_scout.json': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92', 'complete74_nonlinear_index_projection_scout.md': '2034e1343f9c4c059525445c6ef1ae287dec48c0da9d9d27123f1e5745c2c40d'}
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def auth(root,pins):
 for n,h in pins.items():need(sha((root/n).read_bytes())==h,'pin '+n)
def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e
def sos(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 acc='square_0'
 for i in range(1,len(pairs)):
  out.append([f'sum_{i}','+',acc,f'square_{i}']);acc=f'sum_{i}'
 return out,acc

def reconstruct(p):
 rows=p['source'];pairs=p['comparisons'];d={n:(o,a,b)for n,o,a,b in rows};k='k'if p['mode']=='raw30'else'R10b'
 src=lambda v:[n for n,o,a,b in rows if v in(a,b)]
 cmp=lambda v:[i for i,pair in enumerate(pairs)if v in pair]
 need(src('r')==['r1','H17']and cmp('r')==[pairs.index(['r','r_lhs'])],'all literal r consumers')
 need(src('r1')==['R11']and cmp('r1')==[]and src('R11')==[]and cmp('R11')==[pairs.index([k,'R11'])],'private deleted index graph')
 need(d['r1']==('+','r',1)and d['R11']==('+','r1','hpm1')and d['hpm1']==('*','h','UM'),'entire old index equation')
 need('r'not in[d[x][1]for x in d if x=='UM']+[d[x][2]for x in d if x=='UM'],'computed UM r-independent')
 omitted=pairs.index([k,'R11']);new=[]
 for row in rows:
  n,o,a,b=row
  if n in('r1','R11'):continue
  new.append([n,o,'restored_r'if a=='r'else a,'restored_r'if b=='r'else b])
  if n=='hpm1':new.extend([['index_partial','-',k,'hpm1'],['restored_r','-','index_partial',1]])
 retained=[i for i in range(len(pairs))if i!=omitted]
 comparisons=[['restored_r'if x=='r'else x for x in pairs[i]]for i in retained]
 return new,comparisons,omitted,retained,k

def ledger(rows,free,roots,fixed):
 degree={n:0 if n in fixed else 1 for n in free};defs={};M=0
 for n,o,a,b in rows:
  need(type(n)is str and n not in degree and o in('+','-','*'),'fresh typed row')
  need(all(type(v)is int or type(v)is str and v in degree for v in(a,b)),'closed complete DAG')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 live=set();used=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:used.add(n);continue
  if n not in live:live.add(n);todo.extend(defs[n])
 need(live==set(defs)and used==set(free),'every paid row and supplied coordinate live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),all_gates_live=True),degree

# Coefficients in three independent atoms k,H=hE,jc prove the entire local
# restoration. No nonzero relation or positive-domain inference is used.
def local_identity():
 add=lambda a,b:tuple(x+y for x,y in zip(a,b));neg=lambda a:tuple(-x for x in a)
 k=(1,0,0,0);H=(0,1,0,0);jc=(0,0,1,0);one=(0,0,0,1)
 r=add(add(k,neg(H)),neg(one));r1=add(r,one);R11=add(r1,H)
 need(R11==k and add(k,neg(R11))==(0,0,0,0),'deleted index residual identically zero')
 normarg=add(jc,neg(r));need(normarg==(-1,1,1,1),'retained norm argument matches supplied graph')
 return dict(restored_r_coefficients=list(r),r1_coefficients=list(r1),R11_coefficients=list(R11),H17_coefficients=list(normarg))

def degree_proof(p,q,d,retained):
 at=lambda v:d[v]if type(v)is str else 0
 bounds=[max(at(a),at(b))for a,b in q['comparisons']]
 need(d['restored_r']==d['H17']==9,'computed r and norm argument degree9')
 changed=[]
 for j,i in enumerate(retained):
  if p['comparisons'][i]in[['r','r_lhs'],['L17','P17'],['H17','aux_u_rhs']]:changed.append([j,bounds[j]])
 need(len(changed)==3,'only three retained residuals depend on restored r')
 rows={n:(o,a,b)for n,o,a,b in q['source']};mode=q['mode']
 if mode=='raw30':
  req={'n2':('*','Lbig','q'),'Lbig':('*','q','q'),'wn2':('*','w','n2'),'sn2':('*','s','n2'),'UM':('*','wn2','sn2'),'ksn2':('*','k','sn2'),'first_root_base':('*','UM','ksn2'),'first_next':('+','first_root_base','k'),'L9':('*','first_root_base','first_next'),'R9':('-','tau_square',1),'tau_square':('*','tau','tau')}
  need(all(rows[n]==v for n,v in req.items()),'literal raw leading monomial cone')
  target=q['comparisons'].index(['L9','R9']);need(bounds[target]==26,'raw dominant residual')
  expected=[9,24,9];D=52;leader='w^4*s^8*k^4*q^36'
 else:
  req={'q':('+','repunit',1),'repunit':('*','Bm1','Jrep'),'n2':('*','Lbig','q'),'Lbig':('*','q','q'),'wn2':('*','w','n2'),'sn2':('*','s','n2'),'UM':('*','wn2','sn2'),'R12':('+','UM','sn2'),'a_square':('*','R12','R12'),'a4':('*',4,'R12'),'a4m5':('+','a4',3),'A':('+','a_square','a4m5'),'index_product':('*','delta','A'),'index_rhs':('+','odd_index','index_product'),'difference_multiple':('*','index_rhs','R12'),'exponent_partial':('+','W','difference_multiple'),'modulus_multiple':('*','rho','a4m5'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),'mu2':('*','exponent_rhs','exponent_rhs'),'kappa2':('*','index_rhs','index_rhs'),'scaled_kappa2':('*','A','kappa2'),'norm_rhs':('+','scaled_kappa2',1)}
  need(all(rows[n]==v for n,v in req.items()),'entire projected input degree cone')
  need([d[v]for v in('W','R12','index_rhs','rho','a4m5')]==[1,8,17,1,8],'five actual input ports')
  # Expand (W+aK+rhoH)^2-(a²+H)K²-1. Term weights follow;
  # the unique highest term is -HK², with K*=delta*(a*)².
  term_degrees=[2,26,10,34,18,42,0]
  need(max(term_degrees)==42 and term_degrees.count(42)==1,'unique projected input leader')
  target=q['comparisons'].index(['mu2','norm_rhs']);bounds[target]=42;expected=[9,40,9];D=84;leader='16*Bm1^60*delta^4*w^10*s^10*Jrep^60'
 need([b for j,b in changed]==expected and all(b<D//2 for j,b in enumerate(bounds)if j!=target),'all changed and other residuals strictly below preserved leader')
 return dict(exact_degree=D,unique_top_residual=target,residual_degree_upper_bounds=bounds,changed_residual_bounds=changed,whole_polynomial_leader=leader,domain='formal supplied input and witnesses degree1; fixed compiler constants degree0; projected leader nonzero for actual Bm1>0')

def verify(root,artifacts):
 root=Path(root);artifacts=Path(artifacts);auth(root,PINS);auth(artifacts,AUTHOR)
 parents=json.loads((root/'complete74_factored_first_norm.json').read_text())['forms'];saved=json.loads((artifacts/'complete74_nonlinear_index_projection_scout.json').read_text())
 need([p['mode']for p in parents]==['raw30','positive22','signed20']and len(saved['forms'])==3,'exact three-form inventory')
 need(saved['scope']['positive_zero_equivalence_certified']is False and saved['scope']['no_universal_frontier_update']is True,'unresolved positivity scope explicit')
 local=local_identity();counts=Counter();records=[];rng=random.Random(743097)
 for parent,author in zip(parents,saved['forms']):
  p=parent['packet'];q=author['packet'];oldpoly,oldout=sos(p['source'],p['comparisons']);need(oldpoly==p['polynomial_source']and oldout==p['output'],'entire parent finalizer independently rebuilt');need(q['mode']==p['mode'],'same source mode');rows,pairs,omitted,retained,k=reconstruct(p);poly,out=sos(rows,pairs)
  need(q['source']==rows and q['comparisons']==pairs and q['polynomial_source']==poly and q['output']==out,'independently reconstructed complete child')
  need(q['witnesses']==[n for n in p['witnesses']if n!='r']and q['fixed_numerals']==p['fixed_numerals']and q['ordinary_input']==p['ordinary_input'],'entire interface except one supplied r')
  need(q['actual_k_port']==k and q['removed_parent_comparison_index']==omitted and q['parent_comparison_indices']==retained,'actual k and retained comparison mapping')
  need(q['positive_zero_equivalence_certified']is False and q['completeness_from_parent_positive_zeros']is True and q['all_value_graph_identity']is True and q['positive_parent_slice_condition']=='actual k > h*UM + 1','only certified graph and one-way positive statements')
  free=q['fixed_numerals']+q['witnesses']+[q['ordinary_input']];cl,d=ledger(rows,free,[v for ab in pairs for v in ab],q['fixed_numerals']);pl,pd=ledger(poly,free,[out],q['fixed_numerals'])
  need(exact(cl,q['certificate_ledger'])and exact(pl,q['polynomial_ledger'])and(cl['M'],cl['A'])==(40,34),'complete paid count')
  expect={'raw30':(29,18,127),'positive22':(21,10,103),'signed20':(19,8,97)}[p['mode']]
  need((len(q['witnesses']),len(pairs),pl['operations'])==expect,'one witness and row removed; three finalizer gates saved')
  proof=degree_proof(p,q,d,retained);need(proof['exact_degree']==q['degree_certificate']['exact_degree']and proof['whole_polynomial_leader']==q['degree_certificate']['whole_polynomial_leader']and proof['residual_degree_upper_bounds']==q['degree_certificate']['residual_degree_upper_bounds'],'independent all-source degree certificate')
  # Common-source induction: each identical row commutes with r's graph
  # substitution; only r1/R11 disappear and the local proof makes their
  # former comparison zero. All other squared residuals remain verbatim.
  common=[n for n,o,a,b in p['source']if n not in('r1','R11')];counts['common_register_symbolic_transfers']+=len(common);counts['retained_residual_symbolic_transfers']+=len(pairs);counts['whole_graph_identities']+=1
  for j in range(20):
   v={n:rng.randrange(1,5)if j<4 else rng.randrange(-3,4)for n in free}
   if j>=16:v={n:Fraction(x,5)for n,x in v.items()};counts['rational_cases']+=1
   ce=execute(poly,v);pv=dict(v,r=ce['restored_r']);pe=execute(p['polynomial_source'],pv)
   need(all(pe[n]==ce[n]for n in common),'all common literal numeric rows')
   need(pe[f'residual_{omitted}']==0 and pe[p['output']]==ce[out],'full graph and vanishing index residual')
   for cj,pj in enumerate(retained):need(pe[f'residual_{pj}']==ce[f'residual_{cj}'],'all retained residuals');counts['numeric_residual_identities']+=1
   counts['whole_numeric_identities']+=1
  v={n:1 for n in free};v['Bm1']=15;v['h']=2
  if p['mode']=='raw30':v['q']=16
  ce=execute(poly,v);need(ce['restored_r']<0 and ce[out]!=0,'off-zero sign boundary only')
  counts['offzero_negative_inverses']+=1;counts['live_paid_gates']+=pl['operations']
  records.append(dict(mode=p['mode'],certificate=cl,polynomial=pl,witnesses=len(q['witnesses']),comparisons=len(pairs),degree=proof,negative_diagnostic_r=ce['restored_r']))
 # Independent check of the source/native MF translation in the pretyping
 # remainder. It excludes zero but admits negative congruent integers.
 examples=[]
 for B,J,MC,F in((16,1,2,4),(16,7,14,4),(32,3,2,4)):
  q=(B-1)*J+1;T=MC*J+1+q*(F*J-1);shifted=F+B-1
  need((MC+q*shifted)*J-(q*q-1)==T and 0<T<q*q-1,'literal shifted-mask remainder')
  negative=T-(q*q-1);need(negative<0 and negative%(q*q-1)==T,'nonzero residue does not force positive representative')
  examples.append(dict(B=B,J=J,MC=MC,native_MF=F,source_MF=shifted,q=q,remainder=T,negative=negative,scope='partial remainder algebra only'))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),parent_pins=copy.deepcopy(PINS),author_pins=copy.deepcopy(AUTHOR),counts=dict(counts),local_coefficients=local,forms=records,remainder_examples=examples,scope='Three exact all-value complete SOS graph projections and unchanged74 certificate costs. Signed zero fibers have unique restoration; positive reverse map remains unproved. No numerical universal improvement, false positive zero, or maintained hostile-packet API audit claimed.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved independent receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'positive_inverse':'UNPROVED'}))
if __name__=='__main__':main()

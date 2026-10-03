#!/usr/bin/env python3
"""Independent bounded source/census/math audit. No author module is imported."""
import argparse,copy,hashlib,itertools,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
AUTH={
 'complete74_index_transport_affine_scout.py':'21577acbd2c331b3f0a71b7d680e80384bbc0fb87a71a7691532fe53bc6fb213',
 'complete74_index_transport_affine_scout.json':'7f1ee37c769911c8f085a0fd03832b9d91b3315e944818832f237597aca92dd4',
 'complete74_index_transport_affine_scout.md':'26de3b12bcbf0d28cc9810c6af4c058db5c2c5db2f6f99c85bbfb2679e5b53b8'}
PARENTS={
 'complete74_factored_first_norm.py':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908',
 'complete74_factored_first_norm.json':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete74_factored_first_norm.md':'119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f',
 'complete75_signed_projection_elimination101.md':'55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}
PORTS=('r','j','h','zquot')
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def authenticate(root,pins):
 for n,h in pins.items():need(sha((root/n).read_bytes())==h,'pinned '+n)
def run(rows,values):
 env=dict(values)
 for n,o,a,b in rows:
  u=env[a]if isinstance(a,str)else a;v=env[b]if isinstance(b,str)else b
  env[n]={'+':lambda:u+v,'-':lambda:u-v,'*':lambda:u*v}[o]()
 return env
def finalizer(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(l,r)in enumerate(pairs):out+=[[f'residual_{i}','-',l,r],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
 acc='square_0'
 for i in range(1,len(pairs)):
  n=f'sum_{i}';out.append([n,'+',acc,f'square_{i}']);acc=n
 return out,acc

def manual_source(p,sh):
 # Translate all consumers first, then apply exactly the two declared syntactic
 # cancellations. This independently builds all schedules from pinned parents.
 shifts=dict(zip(PORTS,sh));restored={n:f'shifted_old_{n}' for n,s in shifts.items()if s and (n,s)!=('j',1)}
 prefix=[[restored[n],'-'if s==1 else'+',n,1]for n,s in shifts.items()if n in restored]
 alias=lambda v:restored.get(v,v)
 c='c'if p['mode']=='raw30'else'R10a'
 rows=[]
 for n,o,a,b in p['source']:
  if n=='r1'and shifts['r']==1:continue
  if n=='aux_u_rhs'and shifts['j']==1:continue
  a,b=alias(a),alias(b)
  if shifts['r']==1:a='r'if a=='r1'else a;b='r'if b=='r1'else b
  if n=='H17'and shifts['j']==1:
   rows+=[['shifted_H17_before_c','-',a,b],['H17','-','shifted_H17_before_c',c]]
  else:rows.append([n,o,a,b])
 pairs=[[alias(a),alias(b)]for a,b in p['comparisons']]
 if shifts['j']==1:pairs[p['comparisons'].index(['H17','aux_u_rhs'])]=['shifted_H17_before_c','of']
 rows=prefix+rows;poly,out=finalizer(rows,pairs)
 return rows,pairs,poly,out

def source_ledger(rows,free,roots,fixed):
 definitions={};deg={n:0 if n in fixed else 1 for n in free};counts=Counter()
 for n,o,a,b in rows:
  need(n not in deg and o in('+','-','*'),'fresh paid gate')
  need(all(type(v)is int or type(v)is str and v in deg for v in(a,b)),'acyclic complete interface')
  da=0 if type(a)is int else deg[a];db=0 if type(b)is int else deg[b]
  deg[n]=da+db if o=='*'else max(da,db);definitions[n]=(a,b);counts['M'if o=='*'else'A']+=1
 stack=list(roots);live=set();used=set()
 while stack:
  n=stack.pop()
  if type(n)is int:continue
  if n not in definitions:used.add(n);continue
  if n not in live:live.add(n);stack.extend(definitions[n])
 need(live==set(definitions)and used==set(free),'every paid gate and coordinate live')
 return dict(M=counts['M'],A=counts['A'],operations=len(rows),all_gates_live=True),max(0 if type(n)is int else deg[n]for n in roots)

# Independent sparse coefficient expansion, four abstract atoms j,c,r,of.
def plus(a,b,sgn=1):
 z=a.copy()
 for k,c in b.items():z[k]=z.get(k,0)+sgn*c
 return{k:c for k,c in z.items()if c}
def times(a,b):
 z={}
 for x,c in a.items():
  for y,d in b.items():
   k=tuple(i+j for i,j in zip(x,y));z[k]=z.get(k,0)+c*d
 return{k:c for k,c in z.items()if c}
def local_proof():
 v=[{tuple(int(i==j)for i in range(4)):1}for j in range(4)];j,c,r,of=v;one={(0,)*4:1}
 old=plus(times(plus(j,one,-1),c),r,-1);new=plus(plus(times(j,c),r,-1),c,-1)
 need(old==new,'actual old/new norm argument polynomial')
 need(plus(old,plus(of,c,-1),-1)==plus(plus(times(j,c),r,-1),of,-1),'actual linear residual polynomial')
 return {'norm_port_coefficients':[[list(m),k]for m,k in sorted(old.items())],'linear_residual_coefficients':[[list(m),k]for m,k in sorted(plus(new,plus(of,c,-1),-1).items())]}

def verify(root,author):
 authenticate(root,PARENTS);authenticate(author,AUTH)
 saved=json.loads((author/'complete74_index_transport_affine_scout.json').read_text());parents=json.loads((root/'complete74_factored_first_norm.json').read_text())['forms']
 need([f['mode']for f in parents]==['raw30','positive22','signed20'],'exact actual parent set')
 census={(r['mode'],tuple(r['shifts'])):r for r in saved['census']};need(len(census)==len(saved['census'])==243,'unique complete recipe records')
 selected={(r['mode'],tuple(r['shifts'][n]for n in PORTS)):r for r in saved['selected_complete_sources']};need(len(selected)==len(saved['selected_complete_sources'])==15,'unique saved full-source set')
 own=[];counts=Counter();hist={};rng=random.Random(740032026);lp=local_proof()
 for f in parents:
  p=f['packet'];free=p['fixed_numerals']+p['witnesses']+[p['ordinary_input']];fixed=p['fixed_numerals'];eh=len(p['comparisons']);mh=Counter()
  # The local proof may be composed because these private consumer sets are exact.
  users=lambda name:([n for n,o,a,b in p['source']if name in(a,b)],[i for i,pair in enumerate(p['comparisons'])if name in pair])
  need(users('r')[0]==['r1','H17']and len(users('r')[1])==1,'all r consumers')
  need(users('j')==(['jc'],[])and users('jc')==(['H17'],[]),'actual auxiliary quotient privacy')
  need(users('aux_u_rhs')==([],[p['comparisons'].index(['H17','aux_u_rhs'])]),'deleted affine output comparison only')
  d={n:(o,a,b)for n,o,a,b in p['source']};cc='c'if p['mode']=='raw30'else'R10a';aa='a'if p['mode']=='raw30'else'R12';dd='d'if p['mode']=='raw30'else'R14'
  expected={'r1':('+','r',1),'hpm1':('*','h','UM'),'R11':('+','r1','hpm1'),'jc':('*','j',cc),'H17':('-','jc','r'),'aux_u_rhs':('-','of',cc),'c2':('*',cc,cc),'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),'a_square':('*',aa,aa),'A':('+','a_square','a4m5'),'a4':('*',4,aa),'a4m5':('+','a4',3),'L15':('*',dd,dd),'R15':('+','Ac2',1),'Ac2':('*','A','c2'),'R16':('*','A','f_square_minus_one')}
  need(all(d[n]==row for n,row in expected.items()),'actual complete norm/index/auxiliary definitions for positive proof')
  need(['L15','R15']in p['comparisons']and ['ic22','R16']in p['comparisons'],'both crucial norm comparisons retained')
  for sh in itertools.product((-1,0,1),repeat=4):
   rows,pairs,poly,out=manual_source(p,sh);rec=census.pop((p['mode'],sh));cl,cd=source_ledger(rows,free,[v for pair in pairs for v in pair],fixed);pl,pd=source_ledger(poly,free,[out],fixed)
   extra=(sh[0]==-1)+(sh[1]==-1)+(sh[2]!=0)+(sh[3]!=0)
   need(cl['operations']==74+extra and cl['M']==40 and pl['operations']==74+extra+3*eh-1,'independent complete count formula')
   need(rec['certificate']==cl and rec['polynomial']==pl and rec['source_sha256']==sha(json.dumps(rows,separators=(',',':')).encode()),'every census source/hash/ledger independently reconstructed')
   good=sh[0]in(0,1)and sh[1]in(0,1)and sh[2:]==(0,0)
   need(rec['positive_zero_bijection_proved']==good and rec['exact_degree']==p['exact_polynomial_degree'] and rec['propagated_degree_upper']==pd,'scope and degree metadata')
   if good or sh==(-1,-1,-1,-1):
    chosen=selected.pop((p['mode'],sh));need(chosen['source']==rows and chosen['comparisons']==pairs and chosen['polynomial_source']==poly and chosen['output']==out,'entire saved circuit and finalizer')
    need(chosen['witnesses']==p['witnesses']and chosen['fixed_numerals']==fixed and chosen['ordinary_input']==p['ordinary_input'],'complete supplied interfaces')
    need(chosen['certificate_ledger']==cl and chosen['polynomial_ledger']==pl and chosen['exact_polynomial_degree']==p['exact_polynomial_degree'] and chosen['positive_zero_bijection_proved']==good,'saved full-source ledger/domain/degree metadata');counts['saved_complete_sources']+=1
   # Constructive graph proof: generic translated producers are identical;
   # only r+1 cancellation and the two universally quantified local identities
   # above differ. Both cuts retain all other consumers and the same SOS.
   counts['complete_symbolic_transfers']+=1;counts['retained_residual_transfers']+=eh
   for case in range(2):
    v={n:rng.randrange(-3,5)for n in free}
    if case:v={n:Fraction(k,5)for n,k in v.items()};counts['rational_evaluations']+=1
    old=dict(v)
    for n,s in zip(PORTS,sh):old[n]-=s
    a=run(p['polynomial_source'],old);b=run(poly,v);need(a[p['output']]==b[out],'whole independent numeric pullback')
    for i in range(eh):need(a[f'residual_{i}']==b[f'residual_{i}'],'independent retained residual values');counts['numeric_residual_values']+=1
    counts['whole_evaluations']+=1
   counts['paid_live_polynomial_gates']+=len(poly);counts['degree_transfers']+=1;mh[cl['operations']]+=1
   own.append({'mode':p['mode'],'shifts':list(sh),'certificate':cl['operations'],'polynomial':pl['operations'],'exact_degree':p['exact_polynomial_degree'],'positive_inverse_proved':good})
  need(mh==Counter({74:4,75:20,76:33,77:20,78:4}),'independent complete grammar histogram');hist[p['mode']]={str(k):v for k,v in sorted(mh.items())}
 need(not census and not selected,'no unchecked emitted recipe or saved source')
 # Supplement the elementary mathematical proof with actual compiler mask ranges.
 for B in (16,32,64):
  for J in (1,2,7,19):
   q=(B-1)*J+1
   for MC in range(2,B-1,4):
    for MF in range(4,B-1,8):
     TC=MC*J+1;TF=MF*J-1;T=TC+q*TF;A=q*q-1
     need(0<TC<q and 0<TF<q and 0<T<A,'nonzero pretyping remainder')
     need((MC+q*(MF+B-1))*J-A==T,'shifted source MF matches native MF remainder')
     counts['pretyping_mask_cases']+=1
 for A in range(2,41):
  for c in range(2,2*A):
   ds=(A*A-1)*c*c+1;need((A*c-1)**2<ds<(A*c)**2,'consecutive-square exclusion for 1<c<2A');counts['main_norm_size_cases']+=1
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTH,parent_pins=PARENTS,counts=dict(counts),histograms=hist,local_polynomial_proof=lp,independent_census=own,scope='Independent complete243 recipe reconstruction and fifteen saved-source comparison, local coefficient-to-whole-DAG proof, complete paid ledgers and positive inverse proof for twelve minima. No global affine lower bound, no author imports or historical suites, no materialized accepting Pell tuple.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.author_root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact independent saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts']},sort_keys=True))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Independent literal source/API audit; native positive inverse reviewed separately."""
import argparse,copy,hashlib,json,math,random,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
AUTHOR={'complete74_asymmetric_scale_transfer.py': 'c0f3852a1d4c50dba3d7aeb6c877290ebcf18b233dbf944d1870780ab942b8d6', 'complete74_asymmetric_scale_transfer.json': '14816c4da8738e3c27cc1ec0217c450075c0e47b20d77ec4c4d8159aac24dc88', 'complete74_asymmetric_scale_transfer.md': '0484dc71131d7d132e12c7961de731ca4c5bb91adc98447f72fed77882461fe3'}
PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0', 'review_asymmetric_retained109_math.md': '0f9ff2fc994d54af9221e604cd9ec32890539e53a5fae3d951ad064fd64c04c5', 'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_signed_projection_elimination101.md': '55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b'}
def need(x,s):
 if not x:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sos(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 acc='square_0'
 for i in range(1,len(pairs)):out.append([f'sum_{i}','+',acc,f'square_{i}']);acc=f'sum_{i}'
 return out,acc
def evalrows(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e
class Expressions:
 # Products flatten associatively; sums normalize coefficients. A sum used
 # as a factor becomes an interned exact atom. No common-X cut is inserted.
 def __init__(self):self.atoms={}
 def atom(self,key):
  if key not in self.atoms:self.atoms[key]=len(self.atoms)
  return (((self.atoms[key],),1),)
 def value(self,v):return (((),v),)if type(v)is int and v else()if type(v)is int else self.atom(('variable',v))
 def add(self,a,b,s=1):
  r=dict(a)
  for m,c in b:r[m]=r.get(m,0)+s*c
  return tuple(sorted((m,c)for m,c in r.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)>1:a=self.atom(('sum',a))
  if len(b)>1:b=self.atom(('sum',b))
  return ((tuple(sorted(a[0][0]+b[0][0])),a[0][1]*b[0][1]),)
 def run(self,rows,values):
  e=dict(values)
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.value(a);b=e[b]if type(b)is str else self.value(b);e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else-1)
  return e
def ledger(rows,free,fixed,outputs):
 d={n:0 if n in fixed else 1 for n in free};defs={};M=0
 for n,o,a,b in rows:
  need(n not in d and o in('+','-','*'),'fresh literal row');need(all(type(v)is int or type(v)is str and v in d for v in(a,b)),'closed literal DAG')
  da=0 if type(a)is int else d[a];db=0 if type(b)is int else d[b];d[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 seen=set();inputs=set();todo=list(outputs)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:inputs.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 need(seen==set(defs)and inputs==set(free),'all paid gates and inputs live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),free=sorted(free),all_gates_live=True,literal_degree_upper_bound=max(0 if type(n)is int else d[n]for n in outputs)),d

def degree(p,d):
 rows={n:(o,a,b)for n,o,a,b in p['source']};bounds=[max(d[a]if type(a)is str else 0,d[b]if type(b)is str else 0)for a,b in p['comparisons']]
 need(rows['wn2']==('*','w','q')and rows['sn2']==('*','s','n2')and rows['UM']==('*','wn2','sn2'),'both exact scale producers');need([d[n]for n in('wn2','sn2','UM')]==[2,4,6],'asymmetric scale degrees')
 if p['mode']=='raw30':
  want={'ksn2':('*','k','sn2'),'first_root_base':('*','UM','ksn2'),'first_next':('+','first_root_base','k'),'L9':('*','first_root_base','first_next'),'tau_square':('*','tau','tau'),'R9':('-','tau_square',1)}
  top=p['comparisons'].index(['L9','R9']);D=44;leader='w^4*s^8*k^4*q^28';need(d['first_root_base']==11,'raw leading product')
 else:
  want={'R10b':('+','eta','zeta'),'ksn2':('*','R10b','sn2'),'R10a':('+','ksn2','eta'),'c2':('*','R10a','R10a'),'ic2':('*','i','c2'),'ic22':('*','ic2','ic2'),'jc':('*','j','R10a'),'H17':('-','jc','r'),'H2':('*','H17','H17'),'aux_y2':('*','y_aux','y_aux'),'aux_square_gap':('-','H2','aux_y2'),'L17':('*','ic22','aux_square_gap'),'P17':('-',1,'aux_y2'), 'q':('+','repunit',1),'repunit':('*','Bm1','Jrep'), 'R12':('+','UM','sn2'),'a_square':('*','R12','R12'),'a4':('*',4,'R12'),'a4m5':('+','a4',3),'A':('+','a_square','a4m5'),'index_product':('*','delta','A'),'index_rhs':('+','odd_index','index_product'),'difference_multiple':('*','index_rhs','R12'),'modulus_multiple':('*','rho','a4m5'),'exponent_partial':('+','W','difference_multiple'),'exponent_rhs':('+','exponent_partial','modulus_multiple'),'mu2':('*','exponent_rhs','exponent_rhs'),'kappa2':('*','index_rhs','index_rhs'),'scaled_kappa2':('*','A','kappa2'),'norm_rhs':('+','scaled_kappa2',1)}
  need([d[n]for n in('W','R12','index_rhs','rho','a4m5')]==[1,6,13,1,6],'actual expanded input weights')
  bounds[p['comparisons'].index(['mu2','norm_rhs'])]=max(2,20,8,26,14,32,0)
  need([d[n]for n in('R10a','ic22','H17','L17')]==[5,22,6,34],'unique auxiliary top cone')
  top=p['comparisons'].index(['L17','P17']);D=68;leader='Bm1^36*Jrep^36*s^12*i^4*j^4*(eta+zeta)^12'
 need(all(rows[n]==v for n,v in want.items()),'all literal exact-degree producers')
 need(bounds[top]*2==D and all(v<D//2 for i,v in enumerate(bounds)if i!=top),'unique highest residual')
 return dict(exact_degree=D,residual_degree_upper_bounds=bounds,unique_top_residual=top,leader=leader)

def input_identity():
 # Independent sparse expansion in W,a,K,rho,H.
 def add(a,b,s=1):
  r=dict(a)
  for m,c in b.items():r[m]=r.get(m,0)+s*c
  return {m:c for m,c in r.items()if c}
 def mul(a,b):
  r={}
  for m,c in a.items():
   for n,d in b.items():t=tuple(sorted(m+n));r[t]=r.get(t,0)+c*d
  return {m:c for m,c in r.items()if c}
 W,a,K,rho,H=[{(n,):1}for n in('W','a','K','rho','H')];one={():1};sq=lambda p:mul(p,p)
 mu=add(add(W,mul(a,K)),mul(rho,H));lhs=add(add(sq(mu),mul(add(sq(a),H),sq(K)),-1),one,-1)
 terms=[(sq(W),1),(mul(mul(a,W),K),2),(mul(mul(rho,W),H),2),(mul(mul(mul(a,rho),K),H),2),(mul(sq(rho),sq(H)),1),(mul(H,sq(K)),-1),(one,-1)];rhs={}
 for p,c in terms:rhs=add(rhs,{m:c*v for m,v in p.items()})
 need(lhs==rhs,'exact independent input norm cancellation')
 return [[list(m),c]for m,c in sorted(lhs.items())]

def verify(root,artifacts):
 root=Path(root);artifacts=Path(artifacts);blobs={}
 for n,h in PINS.items():
  path=root/n
  if not path.exists():path=root/Path(n).name
  data=path.read_bytes();need(sha(data)==h,'parent pin '+n);blobs[n]=data
 for n,h in AUTHOR.items():need(sha((artifacts/n).read_bytes())==h,'author pin '+n)
 source=artifacts/'complete74_asymmetric_scale_transfer.py';module={'__file__':str(source),'__name__':'independent_loaded_author'};exec(compile(source.read_bytes(),str(source),'exec'),module)
 need(exact(module['PINS'],PINS),'all author dependency pins explicitly reviewed')
 parents=json.loads(blobs['complete74_factored_first_norm.json'])['forms'];saved=json.loads((artifacts/'complete74_asymmetric_scale_transfer.json').read_text());need([f['packet']['mode']for f in saved['forms']]==['raw30','positive22','signed20'],'exact three source inventory')
 counts=Counter();records=[];rng=random.Random(446868);input_proof=input_identity()
 def reject(call,needle=None):
  try:call()
  except(ValueError,TypeError,KeyError)as e:
   if needle:need(needle in str(e),'rejection reason')
   counts['rejected_calls']+=1
  else:raise ValueError('invalid call accepted')
 for oldform,newform in zip(parents,saved['forms']):
  old=oldform['packet'];p=newform['packet'];mode=p['mode'];rows=copy.deepcopy(old['source']);hits=[r for r in rows if r==['wn2','*','w','n2']];need(len(hits)==1,'exact one scale cut');hits[0][3]='q';poly,out=sos(rows,old['comparisons'])
  need(p['source']==rows and p['polynomial_source']==poly and p['output']==out,'entire literal source/finalizer reconstructed')
  for k in('mode','witnesses','fixed_numerals','ordinary_input','comparisons','original_comparison_indices'):need(p[k]==old[k],'unchanged interface '+k)
  need([n for n,o,a,b in rows if 'w'in(a,b)]==['wn2']and all('w'not in pair for pair in p['comparisons']),'sole supplied w consumer')
  free=old['polynomial_ledger']['free'];cl,d=ledger(rows,free,p['fixed_numerals'],[v for pair in p['comparisons']for v in pair]);pl,_=ledger(poly,free,p['fixed_numerals'],[out]);need(exact(cl,p['certificate_ledger'])and exact(pl,p['polynomial_ledger']),'all exact ledgers')
  need((cl['M'],cl['A'])==(40,34)and pl['operations']=={'raw30':130,'positive22':106,'signed20':100}[mode],'unchanged paid costs')
  dg=degree(p,d);need(dg['exact_degree']==p['exact_polynomial_degree']==newform['degree_certificate']['exact_degree']and dg['residual_degree_upper_bounds']==newform['degree_certificate']['residual_degree_upper_bounds']and dg['leader']==newform['degree_certificate']['leader_formula'],'independent uniform degree')
  if mode=='raw30': expected_leader=[{'coefficient':1,'powers':{'w':4,'s':8,'k':4,'q':28}}]
  else:
   expected_leader=[]
   for k in range(13):
    powers={'Bm1':36,'Jrep':36,'s':12,'i':4,'j':4}
    if k:powers['eta']=k
    if 12-k:powers['zeta']=12-k
    expected_leader.append({'coefficient':math.comb(12,k),'powers':powers})
  need(exact(newform['degree_certificate']['whole_polynomial_leader'],expected_leader),'entire binomial leader coefficients')
  e=Expressions();v={n:e.value(n)for n in free};oe=e.run(old['polynomial_source'],v);q=oe['q'];nv=dict(v);nv['w']=e.mul(e.mul(v['w'],q),q);ne=e.run(poly,nv)
  for n,o,a,b in old['polynomial_source']:need(ne[n]==oe[n],'entire associative graph pullback '+n);counts['formal_register_identities']+=1
  counts['whole_graph_identities']+=1;counts['retained_residual_identities']+=len(p['comparisons']);counts['live_paid_gates']+=len(poly)
  need(exact(module['build'](mode,root=root),p)and exact(module['rewrite'](old,mode,root=root),p),'public canonical build/rewrite')
  for case in range(16):
   v={n:rng.randrange(1,5)if case<8 else rng.randrange(-3,4)for n in free};q=v['q']if mode=='raw30'else v['Bm1']*v['Jrep']+1;nv=dict(v,w=v['w']*q*q)
   oe=evalrows(old['polynomial_source'],v);ne=evalrows(poly,nv);need(all(oe[n]==ne[n]for n,o,a,b in poly),'all numeric forward gates');counts['numeric_forward_identities']+=1
   need(module['forward_assignment'](p,v,signed=case>=8,root=root)==nv and module['evaluate'](p,nv,signed=case>=8,root=root)==oe[out],'public forward/evaluator')
   if case<8:need(module['restore_assignment'](p,nv,root=root)==v,'unconditional positive forward roundtrip');counts['positive_map_roundtrips']+=1
   if q:
    iv=dict(v,w=Fraction(v['w'],q*q));need(module['rational_pullback'](p,v,root=root)==iv,'actual rational inverse map');need(evalrows(old['polynomial_source'],iv)[out]==evalrows(poly,v)[out],'whole rational inverse');counts['rational_inverse_identities']+=1
  one={n:1 for n in free};bad=dict(one);bad['q'if mode=='raw30'else'Bm1']=0 if mode=='raw30'else-1
  f=module['forward_assignment'](p,bad,signed=True,root=root);need(evalrows(old['polynomial_source'],bad)[out]==module['evaluate'](p,f,signed=True,root=root),'q0 polynomial forward');counts['q_zero_forward_identities']+=1;reject(lambda:module['rational_pullback'](p,bad,root=root))
  for field in('source','polynomial_source','comparisons','witnesses','fixed_numerals','historical_parent_transformation','asymmetric_scale'):
   b=module['build'](mode,root=root);b[field].clear();reject(lambda b=b:module['checked'](b,root=root));need(exact(module['build'](mode,root=root),p),'deepcopy stability');counts['defensive_copy_checks']+=1
  for field,value in(('exact_polynomial_degree',float(p['exact_polynomial_degree'])),('mode',False),('output','bogus')):
   b=copy.deepcopy(p);b[field]=value;reject(lambda b=b:module['checked'](b,root=root))
  for field in('source','polynomial_source','comparisons','witnesses'):
   b=copy.deepcopy(p);b[field]=tuple(b[field]);reject(lambda b=b:module['checked'](b,root=root))
  b=copy.deepcopy(p);b['source'][0][3]=True;reject(lambda:module['checked'](b,root=root));reject(lambda:module['rewrite'](p,mode,root=root))
  for value in(0,-1,True,1.0,Fraction(1,2)):
   b=dict(one,w=value);reject(lambda b=b:module['evaluate'](p,b,root=root))
  reject(lambda:module['evaluate'](p,one,signed=1,root=root));reject(lambda:module['evaluate'](p,{**one,'extra':1},root=root));nondiv=dict(one)
  if mode=='raw30':nondiv['q']=2
  reject(lambda:module['restore_assignment'](p,nondiv,root=root))
  returned=module['polynomial_source'](p,root=root);returned.clear();need(module['polynomial_source'](p,root=root)==poly,'source defensive copy');cert=module['degree_certificate'](p,root=root);cert['whole_polynomial_leader'].clear();need(module['degree_certificate'](p,root=root)['whole_polynomial_leader'],'degree defensive copy');counts['defensive_copy_checks']+=2
  need(exact(p['historical_parent_transformation'],old['transformation'])and'transformation'not in p,'historical same-coordinate claim archived')
  need(p['asymmetric_scale']['unconditional_integer_inverse']is False and p['asymmetric_scale']['all_value_forward_polynomial_identity']is True,'precise map metadata')
  records.append(dict(mode=mode,certificate_ledger=cl,polynomial_ledger=pl,witnesses=len(p['witnesses']),comparisons=len(p['comparisons']),degree=dg))
 for mode in(None,True,1,'raw'):reject(lambda mode=mode:module['build'](mode,root=root))
 with tempfile.TemporaryDirectory(prefix='independent_asym74_')as td:
  base=Path(td)/'nested'/'wip';base.mkdir(parents=True)
  for n,b in blobs.items():(base/Path(n).name).write_bytes(b)
  p=module['build'](root=base);parent=module['canonical_parent'](root=base);one={n:1 for n in p['polynomial_ledger']['free']}
  calls=[lambda:module['canonical_parent'](root=base),lambda:module['build'](root=base),lambda:module['rewrite'](parent,root=base),lambda:module['checked'](p,root=base),lambda:module['polynomial_source'](p,root=base),lambda:module['degree_certificate'](p,root=base),lambda:module['evaluate'](p,one,root=base),lambda:module['forward_assignment'](p,one,root=base),lambda:module['rational_pullback'](p,one,root=base),lambda:module['restore_assignment'](p,one,root=base)]
  for n,b in blobs.items():
   path=base/Path(n).name;path.write_bytes(b+b'\n')
   for call in calls:reject(call,'Pinned blob');counts['warm_pin_rejections']+=1
   path.write_bytes(b)
   if n.startswith('../'):
    primary=base/n;primary.parent.mkdir(parents=True,exist_ok=True);primary.write_bytes(b+b'\n');reject(lambda:module['build'](root=base),'Pinned blob');counts['canonical_path_pin_rejections']+=1;primary.unlink()
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=copy.deepcopy(AUTHOR),parent_pins=copy.deepcopy(PINS),counts=dict(counts),input_coefficient_identity=input_proof,forms=records,scope='Literal sources, all-value forward/rational graph maps, complete ledgers and uniform exact degrees44/68/68 plus ten public entry points. Native positive inverse theorem inherited from separately reviewed pinned proof; no full Pell-zero materialization or independent reproof claimed.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'])))
if __name__=='__main__':main()

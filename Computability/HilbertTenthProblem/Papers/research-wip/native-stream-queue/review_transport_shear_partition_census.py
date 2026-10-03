#!/usr/bin/env python3
"""Independent saved-source audit; no author imports, historical suite or census."""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
PINS={
 'transport_shear_partition_census.py':'d58f6fd00bc658a566a3ae2f1a3c8b9c7fd457b272291b595132c75a7cbf1d1c',
 'transport_shear_partition_census.json':'93becb442a3809f855053f414e8478e92b2b5eed0ff84c1cb22996b9a0ac1ef0',
 'transport_shear_partition_census.md':'27f38b0757d220e605565c6d63ff3470a73292a9cb632a8c529e8d1b89804469',
 'transport_shear_weighted_census_independent.py':'db269a2563844d6146e5ef88649499aed1c8d3650bf905714c654a93b38875d7',
 'transport_shear_weighted_census_independent.json':'5e7420acdcb0df643b10d29322cc40af59758c0e3646074eeb8b462598a9bd94',
 'transport_shear_weighted_census_independent.md':'382fc8ab7e04e33552c3a4d2daee3453760392b5c24f30086568aab89d4b525d',
 '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}
CONSTANTS=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
FACTORS=['norm_'+n for n in ('first','main','input','aux','index','transport','strong','linear')]
def need(v,m):
 if not v:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def ancestors(rows,ports):
 d={n:(o,a,b)for n,o,a,b in rows};live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is str and n in d and n not in live:live.add(n);todo.extend(d[n][1:])
 return [r[:]for r in rows if r[0]in live]

def parents(data,kind,coordinate):
 if kind.startswith('asymmetric'):
  normalized=kind=='asymmetric_normalized';rows=data['complete75_asymmetric_scale_tradeoffs.json']['source'][0 if normalized else 1]['source']
  weights=[12,18,32,56 if normalized else 24,7,3,34 if normalized else 22,7];outside=[['ic22','R16']]if kind=='asymmetric_comparison'else[]
 else:
  prefix,suffix=kind.split('_',1);uncoupled=suffix.startswith('uncoupled')or suffix=='six_comparisons';gap=prefix=='auxgap'
  which=('gap_91_degree128'if uncoupled else'gap_90_degree131')if gap else('linear_90_degree132'if uncoupled else'linear89')
  rows=next(f['source']for f in data['complete75_asymmetric_linear_gap_tradeoffs.json']['direct_transfers']if f['name']==which)
  weights=[12,18,20,20 if gap else 24,7,3,22,6 if uncoupled else 7]
  outside=[['ic22','R16']]if suffix.endswith('comparison')or suffix=='six_comparisons'else[]
  if suffix=='six_comparisons':outside.append(['H17','aux_u_rhs'])
 factors=FACTORS[:]
 if outside:del factors[6];del weights[6]
 if len(outside)==2:factors.pop();weights.pop()
 gapcore=ancestors(rows,factors+[v for p in outside for v in p]);d={n:(o,a,b)for n,o,a,b in gapcore}
 block={'tau_square':('*','tau_gap','tau_gap'),'first_root_base':('*','UM','ksn2'),'twice_tau_gap':('+','tau_gap','tau_gap'),'first_signed_gap':('-','twice_tau_gap','R10b'),'first_cross':('*','first_root_base','first_signed_gap'),'norm_first':('+','tau_square','first_cross')}
 need(all(d[n]==v for n,v in block.items()),'actual private first-gap block')
 need([n for n,o,a,b in gapcore if 'tau_gap'in(a,b)]==['tau_square','twice_tau_gap'],'only old first coordinate consumers')
 if coordinate=='first_root':
  out=[]
  for n,o,a,b in gapcore:
   if n=='tau_square':out.append([n,'*','tau_root','tau_root'])
   elif n=='norm_first':out.extend([['first_next','+','first_root_base','R10b'],['first_product','*','first_root_base','first_next'],[n,'-','tau_square','first_product']])
   elif n not in('twice_tau_gap','first_signed_gap','first_cross'):out.append([n,o,a,b])
  weights[0]=22
 else:out=gapcore
 return out,factors,weights,outside,gapcore

# Independent sparse polynomial arithmetic for local cuts and finalizers.
def plus(a,b,sign=1):
 z=dict(a)
 for m,v in b.items():z[m]=z.get(m,0)+sign*v
 return {m:v for m,v in z.items()if v}
def times(a,b):
 z={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+v*w
 return {m:v for m,v in z.items()if v}
def ring(k):
 zero=(0,)*k
 return lambda v:({zero:v}if v else{}),lambda i:{tuple(int(i==j)for j in range(k)):1}
def cut_identity():
 C,V=ring(6);r,w,K,c,t,U=map(V,range(6));q=plus(r,C(1));z=plus(t,times(w,c))
 lhs=plus(plus(times(plus(K,times(w,q)),c),U),times(z,r),-1)
 rhs=plus(plus(times(plus(K,w),c),U),times(t,r),-1)
 need(lhs==rhs,'own six-atom transport coefficient expansion')
 c3,v3=ring(3);T,L,k=map(v3,range(3));g=plus(T,L,-1)
 need(plus(times(g,g),times(L,plus(times(c3(2),g),k,-1)))==plus(times(T,T),times(L,plus(L,k)),-1),'first-root ancestry graph identity')
 return sha(stable(sorted((list(k),v)for k,v in rhs.items())).encode())

def shear(rows):
 d={n:(o,a,b)for n,o,a,b in rows}
 req={'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),'wn2':('*','w','q'),'q_minus_F':('-','q','F'),'q_minus_FZ':('-','q_minus_F','Z'),'C_after_alpha':('-','q_minus_FZ','alpha'),'scaled_t':('*','twice_cell_bits','x'),'marked_rhs':('-','C_after_alpha','scaled_t'),'kinner':('+','Kconstant','wn2'),'innerC':('*','kinner','marked_rhs'),'transport_partial':('+','innerC','q_minus_F'),'local_rhs':('*','zplus','repunit'),'norm_transport':('-','transport_partial','local_rhs')}
 need(all(d[n]==v for n,v in req.items()),'literal six-atom content/shear substitution')
 need([n for n,o,a,b in rows if 'zplus'in(a,b)]==['local_rhs'],'private transport quotient')
 need([n for n,o,a,b in rows if 'kinner'in(a,b)]==['innerC'],'private transport coefficient')
 out=copy.deepcopy(rows)
 for row in out:
  if row[0]=='kinner':row[3]='w'
  if row[0]=='local_rhs':row[2]='transport_quotient'
 return out

def inspect(rows,ports,witnesses):
 free=set(CONSTANTS+witnesses+['x']);ready=set(free);counts=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row')
  n,o,a,b=row;need(type(n)is str and n not in ready and o in('+','-','*'),'unique paid gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in(a,b)),'closed source')
  ready.add(n);counts['M'if o=='*'else'A']+=1
 need(ancestors(rows,ports)==rows,'all paid gates live')
 need({v for n,o,a,b in rows for v in(a,b)if type(v)is str and v not in ready-free}==free,'all and only declared free ports live')
 return {'operations':len(rows),'M':counts['M'],'A':counts['A'],'all_gates_live':True,'positive_witnesses':len(witnesses)}

def tail(core,factors,ordinary,partition,anchor):
 rows=copy.deepcopy(core);products=[]
 for gi,block in enumerate(partition):
  product=factors[block[0]]
  for j,index in enumerate(block[1:]):
   n=f'shear_group_{gi}_{j}';rows.append([n,'*',product,factors[index]]);product=n
  products.append(product)
 body=len(rows);comparisons=ordinary+[[p,1]for i,p in enumerate(products)if i!=anchor];out=None
 for i,(a,b)in enumerate(comparisons):
  r=f'shear_res_{i}';square=f'shear_sq_{i}';rows.extend([[r,'-',a,b],[square,'*',r,r]])
  if out is None:out=square
  else:
   n=f'shear_sum_{i}';rows.append([n,'+',out,square]);out=n
 if anchor is not None:
  if out is None:rows.append(['shear_output','-',products[anchor],1])
  else:rows.extend([['shear_positive','+',out,1],['shear_anchored','*',products[anchor],'shear_positive'],['shear_output','-','shear_anchored',1]])
  out='shear_output'
 return rows,out,products,body

def formal_finalizer(rows,out,factors,ordinary,partition,anchor):
 n=len(factors);C,V=ring(n+len(ordinary));env={f:V(i)for i,f in enumerate(factors)}
 for name,o,a,b in rows:
  if name in factors:continue
  if o=='-'and[a,b]in ordinary:env[name]=V(n+ordinary.index([a,b]));continue
  if not all(type(v)is int or v in env for v in(a,b)):continue
  aa=C(a)if type(a)is int else env[a];bb=C(b)if type(b)is int else env[b]
  env[name]=times(aa,bb)if o=='*'else plus(aa,bb,1 if o=='+'else-1)
 products=[]
 for group in partition:
  p=C(1)
  for i in group:p=times(p,V(i))
  products.append(p)
 sos={}
 for i in range(len(ordinary)):sos=plus(sos,times(V(n+i),V(n+i)))
 for i,p in enumerate(products):
  if i!=anchor:r=plus(p,C(1),-1);sos=plus(sos,times(r,r))
 expected=sos if anchor is None else plus(times(products[anchor],plus(C(1),sos)),C(1),-1)
 need(out in env and env[out]==expected,'entire formal SOS or integer-anchor finalizer')
 return len(expected)

def dag_identity(old,new,out,free):
 ids={}
 def key(x):
  if x not in ids:ids[x]=len(ids)
  return ids[x]
 def run(rows):
  e={n:key(('free',n))for n in free+['zplus']}
  for n,o,a,b in rows:
   at=lambda v:key(('int',v))if type(v)is int else e[v]
   e[n]=key(('proved_six_atom_transport',))if n=='norm_transport'else key((o,at(a),at(b)))
  return e
 a,b=run(old),run(new);retained=[n for n,o,u,v in old if n not in('kinner','innerC','transport_partial','local_rhs')]
 need(all(a[n]==b[n]for n in retained)and a[out]==b[out],'whole downstream graph equality after proved cut')
 return len(retained)

# Exact integer coefficient arrays, not modular degrees or sampled outputs.
def dadd(a,b,sgn=1):
 r=[(a[i]if i<len(a)else 0)+sgn*(b[i]if i<len(b)else 0)for i in range(max(len(a),len(b)))];return trim(r)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def dmul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 return trim(r)
def dense(rows,values):
 e=copy.deepcopy(values)
 for n,o,a,b in rows:
  aa=[a]if type(a)is int else e[a];bb=[b]if type(b)is int else e[b]
  e[n]=dmul(aa,bb)if o=='*'else dadd(aa,bb,1 if o=='+'else-1)
 return e
def scalar(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def leaders(kind,coordinate,v):
 Q=v['Bm1']*v['Jrep'];k=v['eta']+v['zeta'];w,s=v['w'],v['s'];gamma=v['rho']+v['sigma'];gap=kind.startswith('auxgap');norm=kind=='asymmetric_normalized';asym=kind.startswith('asymmetric');uncoupled='uncoupled'in kind or kind.endswith('six_comparisons')
 C=Q-v['F']-v['Z']-v['alpha']-v['twice_cell_bits']*v['x'];L=w*s*s*k*Q**7
 return {'norm_first':-L*L if coordinate=='first_root'else L*(2*v['tau_gap']-k),
 'norm_main':8*gamma*k*w*w*s**3*Q**11,
 'norm_input':-4*v['delta']**2*w**5*s**5*Q**20 if asym else 4*v['delta']*(2*v['rho']-v['delta'])*w**3*s**3*Q**12,
 'norm_aux':v['i']**2*k**6*w**4*s**10*Q**34 if norm else 2*v['aux_gap']*v['f']**2*k*w*w*s**3*Q**11 if gap else v['f']**2*k*k*w*w*s**4*Q**14,
 'norm_index':-v['h']*w*s*Q**4,'norm_transport':w*C-v['transport_quotient']*Q,
 'norm_strong':-v['i']**2*k**4*w*w*s**6*Q**20 if norm else v['i']**2*k**4*s**4*Q**12,
 'norm_linear':-v['j']*k*s*Q**3 if uncoupled else -v['h']*w*s*Q**4,
 'strong':v['i']**2*k**4*s**4*Q**12,'linear':v['j']*k*s*Q**3}

def verify(root):
 blobs={};pins=dict(PINS)
 for n,h in PINS.items():blobs[n]=(root/n).read_bytes();need(sha(blobs[n])==h,'pin '+n)
 r=json.loads(blobs['transport_shear_partition_census.json']);need(r['source_sha256']==PINS['transport_shear_partition_census.py'],'receipt source pin')
 for n,h in r['dependency_pins'].items():
  blobs[n]=(root/n).read_bytes();need(sha(blobs[n])==h,'inherited pin '+n)
  if n in pins:need(pins[n]==h,'consistent lineage pins')
  pins[n]=h
 data={n:json.loads(b)for n,b in blobs.items()if n.endswith('.json')}
 weighted=data['transport_shear_weighted_census_independent.json'];wm={(b['coordinate'],b['kind']):b for b in weighted['bases']}
 need(len(r['forms'])==len(wm)==26,'full26 inventory')
 need('fixed positive compiler numerals are B,DC,DR'in blobs['../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md'].decode(),'actual valid fixed-numeral positivity premise')
 counts=Counter();records=[];seen=set();points=set();rng=random.Random(923704);local=cut_identity()
 for f in r['forms']:
  key=f['coordinate_family'],f['kind'];need(key in wm and key not in seen,'unique actual family');seen.add(key);b=wm[key]
  before,factors,weights,ordinary,gapcore=parents(data,key[1],key[0]);new=shear(before);weights[factors.index('norm_transport')]=2
  need(new==f['base_source']and factors==f['factors']and weights==f['weights']and ordinary==f['ordinary_comparisons'],'independent entire core reconstruction')
  need(f['fixed_numerals']==CONSTANTS and f['ordinary_input']=='x','unchanged ordinary interface')
  names={n for n,o,a,c in new};free={v for n,o,a,c in new for v in(a,c)if type(v)is str and v not in names};witnesses=sorted(free-set(CONSTANTS+['x']))
  need(len(witnesses)==19 and set(f['witnesses'])==set(witnesses)and len(f['witnesses'])==19,'exact supplied positive witness set')
  core=inspect(new,factors+[v for p in ordinary for v in p],witnesses);need(core==f['core_ledger'],'complete live core counts')
  need(core['M']==b['core_M']and core['A']==b['core_A']and weights==b['weights'],'weighted core authentication')
  residual_degrees=[22,6][:len(ordinary)];need(f['residual_degrees']==residual_degrees==b['residual_degrees'],'retained ordinary comparisons')
  counts['independent_reconstructed_cores']+=1;counts['proved_local_source_cuts']+=1
  # A distinct exact affine line; theorem exactness is inherited uniform leader algebra.
  scales={n:(i%4)+1 for i,n in enumerate(witnesses+['x'])};scales.update(delta=2,rho=5,Jrep=3,x=2,eta=2,zeta=3,transport_quotient=4)
  if key[0]=='gap_root':scales['tau_gap']=1
  fixed=dict(Bm1=31,Kconstant=163,twice_cell_bits=10,inner_bits=3,MC=30,MF=35)
  values={n:[i%5-2,scales[n]]for i,n in enumerate(witnesses+['x'])};values.update({n:[v]for n,v in fixed.items()})
  tops=leaders(key[1],key[0],dict(scales,**fixed));ce=dense(new,values)
  for name,degree in zip(factors,weights):need(len(ce[name])-1==degree and ce[name][-1]==tops[name]!=0,'actual factor leader and degree');counts['exact_factor_expansions']+=1
  for i,(a,c)in enumerate(ordinary):
   rr=dadd(ce[a],ce[c],-1);need(len(rr)-1==residual_degrees[i]and rr[-1]==tops['strong'if i==0 else'linear']!=0,'retained comparison leader');counts['exact_comparison_expansions']+=1
  predicted={w['operations']:w for w in b['best_by_cost']};need(len(f['winners'])==len(predicted),'all per-cost winners saved')
  costs=set()
  for winner in f['winners']:
   p,anchor=winner['partition'],winner['anchor'];n=len(factors)
   need(type(p)is list and p and all(type(g)is list and g and all(type(i)is int for i in g)for g in p),'typed nonempty groups')
   need(sorted(i for g in p for i in g)==list(range(n))and all(g==sorted(g)for g in p)and [g[0]for g in p]==sorted(g[0]for g in p),'disjoint full canonical partition')
   need(anchor is None or type(anchor)is int and 0<=anchor<len(p),'single anchor')
   rows,out,products,body=tail(new,factors,ordinary,p,anchor);oldrows,oldout,_,_=tail(before,factors,ordinary,p,anchor)
   need(rows==winner['source']and out==winner['output']and products==winner['group_products']and body==winner['certificate_operations'],'all literal winner and finalizer gates')
   ledger=inspect(rows,[out],witnesses);need(ledger==winner['ledger'],'complete full paid live ledger')
   ops=len(rows);need(ops==winner['operations']and ops not in costs and ops in predicted,'unique full per-cost source');costs.add(ops)
   target=predicted[ops];need((ledger['M'],ledger['A'])==(target['M'],target['A']),'independently predicted complete M/A')
   groups=[sum(weights[i]for i in g)for g in p];ds=residual_degrees+[d for i,d in enumerate(groups)if i!=anchor];degree=(groups[anchor]if anchor is not None else 0)+2*max(ds+[0])
   need(degree==winner['exact_degree']==target['predicted_degree']and groups==winner['group_degrees'],'winner exact objective/degree')
   counts['formal_finalizer_monomials']+=formal_finalizer(rows,out,factors,ordinary,p,anchor)
   counts['whole_graph_register_identities']+=dag_identity(oldrows,rows,out,CONSTANTS+witnesses+['x'])
   counts['SOS_finalizers'if anchor is None else'anchor_finalizers']+=1
   if anchor is not None and not ds:counts['pure_product_finalizers']+=1
   e=dense(rows,values);claimed=dense(rows,f['degree_affine_substitution'])[out];evidence=winner['degree_evidence'];prime=evidence['prime'];need(prime==2147483647,'claimed modular evidence field');reduced=[v%prime for v in claimed];trim(reduced);need(sha(stable(reduced).encode())==evidence['full_coefficients_sha256']and reduced[-1]==evidence['leading_coefficient_mod_prime']!=0 and len(reduced)-1==degree,'independent replay of saved modular coefficient evidence');counts['saved_modular_evidence_checks']+=1;lift=copy.deepcopy(values);lift['zplus']=dadd(lift.pop('transport_quotient'),dmul(values['w'],e['marked_rhs']));prev=dense(oldrows,lift)
   need(e[out]==prev[oldout],'full exact coefficient graph pullback')
   gt=[]
   for g in p:
    z=1
    for i in g:z*=tops[factors[i]]
    gt.append(z)
   rs=[(d,tops['strong'if i==0 else'linear'])for i,d in enumerate(residual_degrees)]+[(d,gt[i])for i,d in enumerate(groups)if i!=anchor]
   topdegree=max([d for d,z in rs]+[0]);leader=sum(z*z for d,z in rs if d==topdegree)if rs else 1
   if anchor is not None:leader*=gt[anchor]
   need(len(e[out])-1==degree and e[out][-1]==leader!=0,'exact full source degree and nonzero leader')
   for case in range(3):
    v={n:rng.randrange(-3,5)for n in CONSTANTS+witnesses+['x']}
    if case==2:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_pullbacks']+=1
    now=scalar(rows,v);oldv=dict(v);oldv['zplus']=oldv.pop('transport_quotient')+v['w']*now['marked_rhs'];previous=scalar(oldrows,oldv)
    need(now[out]==previous[oldout],'whole signed/rational pullback');counts['scalar_pullbacks']+=1
   counts['complete_sources']+=1;counts['live_paid_gates']+=ops;counts['M']+=ledger['M'];counts['A']+=ledger['A'];counts['exact_full_coefficient_identities']+=1;counts['exact_full_degree_checks']+=1
   points.add((ops,degree));need(winner['improves_saved_frontier']is False,'no new pair flag')
   records.append({'coordinate':key[0],'kind':key[1],'operations':ops,'M':ledger['M'],'A':ledger['A'],'exact_degree':degree,'partition':p,'anchor':anchor,'complete_coefficients_sha256':sha(stable(e[out]).encode())})
  need(costs==set(predicted),'no omitted objective cost')
 need(seen==set(wm),'all26 bases accounted')
 frontier=sorted(v for v in points if not any(u!=v and u[0]<=v[0]and u[1]<=v[1]for u in points));need([list(v)for v in frontier]==r['frontier']==weighted['predicted_frontier'],'whole saved-source frontier matches independent census')
 need((counts['complete_sources'],counts['live_paid_gates'],counts['M'],counts['A'])==(202,19375,9702,9673),'complete paid totals')
 return {'status':'PASS_INDEPENDENT_FULL_SAVED_SOURCE_REVIEW','source_sha256':sha(Path(__file__).read_bytes()),'pins':pins,'local_coefficient_identity_sha256':local,'counts':dict(counts),'sources':records,'frontier':[list(v)for v in frontier],'scope':'All202 saved winners and26 cores independently reconstructed from pinned JSON; full formal finalizers, live paid counts, signed graph identities, exact integer affine-line coefficients and inherited uniform leader proof. Reads independent weighted receipt for coverage/minima; no census rerun, author Python or historical suite, public API or giant accepting Pell tuple.'}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root);text=json.dumps(r,sort_keys=True,indent=2)+'\n';need(same(r,json.loads(text)),'exact typed JSON roundtrip')
 if a.output:a.output.write_text(text)
 else:need(same(r,json.loads(a.expect.read_text())),'fresh exact saved receipt')
 print(r['status'],r['counts']);print(r['frontier'])

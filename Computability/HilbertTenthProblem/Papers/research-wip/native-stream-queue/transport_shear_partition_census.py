#!/usr/bin/env python3
"""Finite26-base transport-shear census, with every per-cost winning source saved.
The pinned predecessor base builder is reused; its verifier/census never runs.
"""
import argparse,copy,hashlib,json,random,types
from pathlib import Path
from collections import Counter
from fractions import Fraction
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'complete86_first_root_partitions.py':'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988',
'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
'complete86_first_root_partitions.md':'7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0',
'complete86_transport_quotient_shear.py':'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45',
'complete86_transport_quotient_shear.json':'77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc',
'complete86_transport_quotient_shear.md':'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
 'transport_shear_frontier_probe.json':'4e58078d955a9cc7d5642dea24e8f1ac76ac71da2f8b82b568bb27794d25d865'}
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def partitions(n):
 a=[0]*n
 def visit(i,m):
  if i==n:yield [[j for j in range(n)if a[j]==k]for k in range(m+1)];return
  for k in range(m+2):a[i]=k;yield from visit(i+1,max(m,k))
 yield from visit(1,0)

def degree(b,part,anchor):
 ds=[sum(b['weights'][i]for i in g)for g in part];r=max([0]+b['residual_degrees'])
 return 2*max([r]+ds)if anchor is None else ds[anchor]+2*max([r]+[d for i,d in enumerate(ds)if i!=anchor])

def emit(b,part,anchor,inspect):
 rows=copy.deepcopy(b['source']);products=[]
 for j,g in enumerate(part):
  current=b['factors'][g[0]]
  for k,i in enumerate(g[1:]):
   n=f'shear_group_{j}_{k}';rows.append([n,'*',current,b['factors'][i]]);current=n
  products.append(current)
 pairs=b['ordinary_comparisons']+[[v,1]for i,v in enumerate(products)if i!=anchor]
 body=len(rows);out=None
 for i,(a,c)in enumerate(pairs):
  r=f'shear_res_{i}';s=f'shear_sq_{i}';rows.extend([[r,'-',a,c],[s,'*',r,r]])
  if out is None:out=s
  else:n=f'shear_sum_{i}';rows.append([n,'+',out,s]);out=n
 if anchor is not None:
  if out is None:rows.append(['shear_output','-',products[anchor],1])
  else:rows.extend([['shear_positive','+',out,1],['shear_anchored','*',products[anchor],'shear_positive'],['shear_output','-','shear_anchored',1]])
  out='shear_output'
 ledger=inspect(rows,[out],b['witnesses'])
 return dict(source=rows,output=out,ledger=ledger,certificate_operations=body,group_products=products)

def shear(parent,inspect):
 b=copy.deepcopy(parent);d={n:(op,a,c)for n,op,a,c in b['source']}
 required={'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),'wn2':('*','w','q'),'kinner':('+','Kconstant','wn2'),'innerC':('*','kinner','marked_rhs'),'q_minus_F':('-','q','F'),'q_minus_FZ':('-','q_minus_F','Z'),'C_after_alpha':('-','q_minus_FZ','alpha'),'scaled_t':('*','twice_cell_bits','x'),'marked_rhs':('-','C_after_alpha','scaled_t'),'transport_partial':('+','innerC','q_minus_F'),'local_rhs':('*','zplus','repunit'),'norm_transport':('-','transport_partial','local_rhs')}
 need(all(d.get(n)==v for n,v in required.items()),'all literal local identity cuts')
 for name,consumer in [('zplus','local_rhs'),('kinner','innerC')]:need([n for n,op,a,c in b['source']if name in(a,c)]==[consumer],'sole private consumer')
 for row in b['source']:
  if row[0]=='kinner':row[3]='w'
  if row[0]=='local_rhs':row[2]='transport_quotient'
 b['witnesses']=['transport_quotient'if n=='zplus'else n for n in b['witnesses']]
 i=b['factors'].index('norm_transport');need(b['weights'][i]==3,'old transport cubic');b['weights'][i]=2
 actual=inspect(b['source'],b['factors']+[v for p in b['ordinary_comparisons']for v in p],b['witnesses'])
 need(actual==b['core_ledger'],'all paid core counts unchanged')
 return b

def local_identity():
 zero=(0,)*6
 def atom(i):return {tuple(int(i==j)for j in range(6)):1}
 def add(a,b,sign=1):
  c=a.copy()
  for m,v in b.items():c[m]=c.get(m,0)+sign*v
  return {m:v for m,v in c.items()if v}
 def mul(a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    p=tuple(x+y for x,y in zip(m,n));c[p]=c.get(p,0)+v*w
  return {m:v for m,v in c.items()if v}
 r,w,K,C,t,U=[atom(i)for i in range(6)];q=add(r,{zero:1});z=add(t,mul(w,C))
 before=add(add(mul(add(K,mul(w,q)),C),U),mul(z,r),-1)
 after=add(add(mul(add(K,w),C),U),mul(t,r),-1)
 need(before==after,'exact independent local coefficient identity')
 return sha(canonical(sorted(before.items())).encode())

def graph_identity(old,new,out,free):
 ids={}
 def intern(t):
  if t not in ids:ids[t]=len(ids)
  return ids[t]
 def run(rows):
  e={v:intern(('var',v))for v in free+['zplus']}
  for n,op,a,b in rows:
   at=lambda v:intern(('int',v))if type(v)is int else e[v]
   e[n]=intern(('proved_transport_cut',))if n=='norm_transport'else intern((op,at(a),at(b)))
  return e
 a=run(old);b=run(new);retained=[n for n,op,x,y in old if n not in('kinner','innerC','transport_partial','local_rhs')]
 need(all(a[n]==b[n]for n in retained)and a[out]==b[out],'all retained registers and full finalizer under local identity')
 return len(retained)

def verify(root):
 root=Path(root);blobs={}
 for n,pin in PINS.items():blobs[n]=(root/n).read_bytes();need(sha(blobs[n])==pin,'pin '+n)
 mod=types.ModuleType('pinned_predecessor_base_builder');mod.__file__=str(root/'complete86_first_root_partitions.py');exec(compile(blobs['complete86_first_root_partitions.py'],mod.__file__,'exec'),mod.__dict__)
 # Every ancestral builder dependency is authenticated by its existing guard,
 # including on the later public base calls. No old census or verify is called.
 mod._authenticate(root);dependency_pins=dict(mod.PINS);dependency_pins.update(PINS)
 known=json.loads(blobs['transport_shear_frontier_probe.json'])['saved_schedule_frontier']
 cache={n:list(partitions(n))for n in(6,7,8)};need([len(cache[n])for n in(6,7,8)]==[203,877,4140],'complete Bell inventories')
 forms=[];counts=Counter(local_ring_identities=1);points=set();improvements=[];rng=random.Random(298672);local_hash=local_identity()
 for coordinate_family in('first_root','gap_root'):
  for kind in mod.KINDS:
   old=mod.base(root,kind)if coordinate_family=='first_root'else mod.canonical_parent(root,kind);b=shear(old,mod.inspect)
   n=len(b['factors']);m=len(b['ordinary_comparisons']);core=b['core_ledger'];best={};hist=Counter();digest=hashlib.sha256()
   for part in cache[n]:
    counts['partitions']+=1;g=len(part)
    for anchor in[None]+list(range(g)):
     special=m==0 and g==1 and anchor==0;ops=core['operations']+n+3*m+2*g-1-int(special);dd=degree(b,part,anchor)
     record=dict(partition=part,anchor=anchor,operations=ops,exact_degree=dd)
     digest.update((canonical(record)+'\n').encode());counts['plans']+=1;hist[(ops,dd)]+=1;points.add((ops,dd))
     if ops not in best or dd<best[ops]['exact_degree']:best[ops]=copy.deepcopy(record)
   # Whole core degree evidence at a fixed affine specialization. Uniform
   # exactness comes from the inherited nonzero factor leaders, not this line.
   scales={name:(i%4)+1 for i,name in enumerate(b['witnesses']+['x'])};scales.update(delta=2,rho=5,Jrep=2,x=1,eta=2,zeta=3,transport_quotient=3)
   if coordinate_family=='gap_root':scales['tau_gap']=1
   fixed=mod._fixed(16);vals={name:[i+1,scales[name]]for i,name in enumerate(b['witnesses']+['x'])};vals.update({name:[v]for name,v in fixed.items()})
   prime=2147483647;poly=mod._dense(b['source'],vals,prime);topvals=dict(scales,**fixed);tops=mod._tops(kind,topvals);Q=fixed['Bm1']*scales['Jrep'];k=scales['eta']+scales['zeta']
   if coordinate_family=='gap_root':tops['norm_first']=scales['w']*scales['s']**2*k*Q**7*(2*scales['tau_gap']-k)
   C1=Q-scales['F']-scales['Z']-scales['alpha']-fixed['twice_cell_bits']*scales['x'];tops['norm_transport']=scales['w']*C1-scales['transport_quotient']*Q
   for name,d in zip(b['factors'],b['weights']):
    need(len(poly[name])-1==d and poly[name][-1]==tops[name]%prime and poly[name][-1]!=0,'actual inherited/new factor degree and leader');counts['factor_degree_expansions']+=1
   winners=[]
   for ops,plan in sorted(best.items()):
    p=emit(b,plan['partition'],plan['anchor'],mod.inspect);prior=emit(old,plan['partition'],plan['anchor'],mod.inspect)
    need(p['ledger']['operations']==ops and p['ledger']==prior['ledger'],'complete paid winner ledger')
    counts['retained_register_identities']+=graph_identity(prior['source'],p['source'],p['output'],b['witnesses']+mod.CONSTANTS+['x']);counts['complete_source_identities']+=1
    for case in range(4):
     v={name:rng.randrange(-3,4)for name in b['witnesses']+mod.CONSTANTS+['x']}
     if case==3:v={name:Fraction(value,3)for name,value in v.items()};counts['rational_cases']+=1
     now=mod.execute(p['source'],v);ov=v.copy();ov['zplus']=ov.pop('transport_quotient')+v['w']*now['marked_rhs'];before=mod.execute(prior['source'],ov)
     need(now[p['output']]==before[prior['output']],'entire scalar coordinate pullback');counts['full_numeric_pullbacks']+=1
    dense=mod._dense(p['source'],vals,prime);dd=plan['exact_degree'];need(len(dense[p['output']])-1==dd,'whole literal degree attained')
    groups=[sum(b['weights'][i]for i in g)for g in plan['partition']];gt=[]
    for g in plan['partition']:
     val=1
     for i in g:val*=tops[b['factors'][i]]
     gt.append(val)
    residuals=[(d,tops['strong'if i==0 else'linear'])for i,d in enumerate(b['residual_degrees'])]+[(d,gt[i])for i,d in enumerate(groups)if i!=plan['anchor']]
    highest=max([0]+[d for d,c in residuals]);leader=sum(c*c for d,c in residuals if d==highest)if residuals else 1
    if plan['anchor']is not None:leader*=gt[plan['anchor']]
    need(dense[p['output']][-1]==leader%prime and leader%prime!=0,'whole source leading coefficient');counts['complete_degree_expansions']+=1
    counts['literal_winner_sources']+=1;counts['winner_paid_gates']+=ops;counts['winner_M']+=p['ledger']['M'];counts['winner_A']+=p['ledger']['A']
    improved=not any(x<=ops and y<=dd for x,y in known)
    rec=dict(plan,**p,group_degrees=groups,degree_evidence=dict(prime=prime,leading_coefficient_mod_prime=leader%prime,full_coefficients_sha256=sha(canonical(dense[p['output']]).encode())),improves_saved_frontier=improved)
    winners.append(rec)
    if improved:improvements.append(dict(coordinate_family=coordinate_family,kind=kind,**plan))
   forms.append(dict(coordinate_family=coordinate_family,kind=kind,base_source=b['source'],factors=b['factors'],weights=b['weights'],ordinary_comparisons=b['ordinary_comparisons'],residual_degrees=b['residual_degrees'],witnesses=b['witnesses'],fixed_numerals=mod.CONSTANTS,ordinary_input='x',core_ledger=core,partitions=len(cache[n]),plans=sum(hist.values()),objective_sha256=digest.hexdigest(),objective_histogram=[dict(operations=o,exact_degree=d,multiplicity=count)for(o,d),count in sorted(hist.items())],degree_affine_substitution=vals,winners=winners))
 frontier=sorted(p for p in points if not any(q!=p and q[0]<=p[0]and q[1]<=p[1]for q in points));frontier=[list(p)for p in frontier]
 need(frontier==known and not improvements,'no new Pareto point in this exact finite family')
 need((counts['partitions'],counts['plans'],counts['literal_winner_sources'],counts['winner_paid_gates'])==(59262,298672,202,19375),'complete finite census totals')
 return dict(status='PASS_FINITE_TRANSPORT_SHEAR_PARTITION_CENSUS',source_sha256=sha(Path(__file__).read_bytes()),dependency_pins=dependency_pins,counts=dict(counts),local_identity_sha256=local_hash,frontier=frontier,improvements=improvements,forms=forms,scope='Exactly26 authenticated cores and all disjoint factor partitions with SOS or one integer anchor. All298672 objectives counted;202 per-base per-cost winning full sources emitted, checked and saved. Uniform degrees inherit unchanged nonzero factor leaders plus quadratic transport. No arbitrary circuit lower bound or new universal operation record; no historical verifier/census or broad public API audit.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts']);print('FRONTIER',r['frontier'])
if __name__=='__main__':main()

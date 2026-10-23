#!/usr/bin/env python3
"""Finite exact audit for support-separated quadratic consistency encodings.

No search for zeros or consistency test is performed. Exact polynomial
coefficient identities, coherent fixed-port binding, DAG sizes, and nonzero
leading coefficients are checked independently of the builder's metadata.
"""
from pathlib import Path
import collections,gzip,hashlib,itertools,json,math,random,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from parent_arithmetic import add,mul,shift_positive
from portpoly import parse
def need(ok,message):
 if not ok:raise ValueError(message)
def jread(p):return json.loads((ROOT/p).read_text())
def pval(recipe,ports,mod=None):
 total=0
 for row in recipe:
  x=row['coefficient']
  for p,e in zip(ports,row['powers']):x*=pow(p,e,mod) if mod else p**e
  total+=x
 return total%mod if mod else total
def dag(body,variables,fixed,p):
 out=[]
 for i,node in enumerate(body['nodes']):
  k=node['kind']
  if k=='literal':v=node['value']
  elif k=='fixed':v=fixed[node['name']]
  elif k=='variable':v=variables[node['name']]
  else:
   a,b=node['left'],node['right'];need(a<i and b<i,'not topological')
   x,y=out[a],out[b];v=x+y if k=='add' else x-y if k=='sub' else x*y
  out.append(v%p)
 return out[body['output']],out
def degree(body,fixed,p):
 deg=[];lead=[]
 for node in body['nodes']:
  k=node['kind']
  if k=='variable':d,c=1,1
  elif k=='literal':d,c=0,node['value']%p
  elif k=='fixed':d,c=0,fixed[node['name']]%p
  else:
   a,b=node['left'],node['right']
   if k=='mul':d,c=deg[a]+deg[b],lead[a]*lead[b]%p
   else:
    d=max(deg[a],deg[b]);x=lead[a] if deg[a]==d else 0;y=lead[b] if deg[b]==d else 0
    c=(x+y if k=='add' else x-y)%p
  deg.append(d);lead.append(c)
 return deg[body['output']],lead[body['output']]
def counts(body):
 ns=body['nodes'];live={body['output']}
 for i in range(len(ns)-1,-1,-1):
  need(i in live,'dead DAG node')
  if ns[i]['kind'] in ('add','sub','mul'):live.update((ns[i]['left'],ns[i]['right']))
 return dict(collections.Counter(n['kind'] for n in ns if n['kind'] in ('add','sub','mul')))
def exact_parent(path='upstream/parent_system.json'):
 parent=jread(path);names=parent['variables']+parent['constants'];n=31;z=(0,)*len(names)
 env={}
 for i,name in enumerate(names):m=list(z);m[i]=1;env[name]={tuple(m):1}
 def get(v):return ({z:v} if v else {}) if isinstance(v,int) else env[v]
 for name,op,a,b in parent['source']:env[name]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),-1 if op=='-' else 1)
 rows=[add(get(a),get(b),-1) for a,b in parent['comparisons']]
 if path=='upstream/parent_system.json':
  sparse=jread('upstream/parent_sparse.json')
  for row,ref in zip(rows,sparse['equations']):need(row=={tuple(t['powers']):t['coefficient'] for t in ref['terms']},'raw parent identity')
 rows=[shift_positive(r,n) for r in rows];order=list(range(4))+list(range(5,22))+[4]
 return [rows[i] for i in order]
def weighted_rows(source):
 rows=[]
 for row in source['rows']:
  terms=row['terms'] if isinstance(row,dict) else row;out={}
  for term in terms:
   alpha=tuple(term['alpha'])
   if 'weighted_coefficient' in term:poly=parse(term['weighted_coefficient'])
   elif isinstance(term['leaf'],int):poly={(0,0,0,0):term['leaf']*term['sign']}
   else:poly={tuple(t['powers']):t['coefficient']*term['sign'] for t in source['recipes'][term['leaf']]}
   for port,co in poly.items():out[alpha+port]=co
  rows.append(out)
 return rows
def check_packing(w,rows,targets):
 n=31;pairs=list(itertools.combinations_with_replacement(range(32),2));sums=collections.defaultdict(list)
 for a,b in pairs:sums[w[a]+w[b]].append((a,b))
 active=set()
 for row in rows:
  for mon in row:
   alpha=mon[:n];pair=[0]*(2-sum(alpha))
   for i,e in enumerate(alpha):pair += [i+1]*e
   need(len(pair)==2,'nonquadratic monomial');active.add(tuple(pair))
 for pair in active:need(sums[w[pair[0]]+w[pair[1]]]==[pair],'active pair is contaminated')
 d={};owner={}
 for j,(row,E) in enumerate(zip(rows,targets)):
  for mon,co in row.items():
   alpha,port=mon[:n],mon[n:];e=E-sum(a*b for a,b in zip(alpha,w[1:]));need(e>=0,'negative source exponent')
   need(e not in owner or owner[e]==j,'overlapping row kernel coefficients');owner[e]=j
   d[e,port]=d.get((e,port),0)+co
 extracted=[{} for _ in rows];ti={e:i for i,e in enumerate(targets)}
 for (e,port),co in d.items():
  for a,b in pairs:
   j=ti.get(e+w[a]+w[b])
   if j is None:continue
   alpha=[0]*n
   if a:alpha[a-1]+=1
   if b:alpha[b-1]+=1
   mon=tuple(alpha)+port;fac=1 if a==b else 2
   extracted[j][mon]=extracted[j].get(mon,0)+fac*co
 for got,row in zip(extracted,rows):
  want={}
  for mon,co in row.items():
   alpha=mon[:n];fac=math.factorial(2-sum(alpha))*math.prod(math.factorial(x) for x in alpha)
   need((2*co)%fac==0,'factorial divisibility');want[mon]=2*co//fac
  need({m:c for m,c in got.items() if c}==want,'exact target identity failed')
 highest=max(e for e,p in d);need(highest==targets[-1],'kernel leading exponent')
 need({port:co for (e,port),co in d.items() if e==highest}=={(0,0,0,0):2},'kernel positive leading coefficient')
 return {'active_pairs':len(active),'all_pairs':len(pairs),'distinct_pair_sums':len(sums),'collided_sum_positions':sum(len(v)>1 for v in sums.values()),'maximum_collision_multiplicity':max(map(len,sums.values())),'exact_symbolic_target_identities':22,'maximum_weight':max(w),'targets':targets,'kernel_maximum_exponent':highest,'product_degree_bound':highest+2*max(w)}
def norm_identities():
 def ring(n):
  z=(0,)*n
  def const(v):return {z:v} if v else {}
  xs=[]
  for i in range(n):a=list(z);a[i]=1;xs.append({tuple(a):1})
  return const,xs
 c,(A,C,E,G,H)=ring(5)
 sq=lambda x:mul(x,x)
 one=c(1);D=add(mul(add(sq(A),one,-1),sq(C)),one);F=add(mul(add(sq(A),one,-1),sq(E)),one);I=add(mul(add(sq(G),one,-1),sq(H)),one)
 MD=mul(A,C);MF=mul(A,E);MI=mul(G,H);V1=mul(mul(MD,MF),MI)
 delta=add(add(mul(mul(add(sq(C),one,-1),sq(MF)),sq(MI)),mul(mul(D,add(sq(E),one,-1)),sq(MI))),mul(mul(D,F),add(sq(H),one,-1)))
 need(add(sq(V1),mul(mul(D,F),I),-1)==delta,'exact telescoping identity')
 c,(E0,Om,V0,V1,a0,a1)=ring(6)
 theta=add(E0,mul(mul(Om,V0),V1),-1)
 left=add(sq(theta),mul(sq(Om),add(a0,mul(sq(V0),a1))),-1)
 right=add(add(add(sq(E0),mul(c(2),mul(mul(mul(E0,Om),V0),V1)),-1),mul(mul(sq(Om),sq(V0)),add(sq(V1),a1,-1))),mul(sq(Om),a0),-1)
 need(left==right,'exact inner norm cancellation')
 return {'telescoping_identity':True,'inner_norm_cancellation_identity':True}

def check_artifact_metadata(w,q9):
 """Validate local references and redundant source labels as literal data."""
 root=ROOT.resolve();references=0
 def link(owner,body,key,expected):
  nonlocal references
  need(body.get('artifact_paths_relative_to')=='this_json_file','unspecified artifact path base')
  value=body.get(key);need(isinstance(value,str),'missing artifact reference '+key)
  path=(owner.parent/value).resolve()
  need(path==(root/expected).resolve() and path.is_file(),'invalid local artifact reference '+key)
  references+=1
  return path
 target_path=ROOT/'quartic/QUADRATIC_TARGETS.json'
 source=link(target_path,q9,'source_file','upstream/parent_system60.json')
 need(q9['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest(),'attached parent source digest')
 targets=[400+401*j for j in range(22)]
 need(q9['weights']==w[1:] and q9['maximum_weight']==200,'quadratic target weight metadata')
 need(q9['target_spacing']==401 and q9['target_maximum']==targets[-1],'quadratic target range metadata')
 need(len(q9['rows'])==q9['row_count']==22,'quadratic target row count')
 need([r['target_exponent'] for r in q9['rows']]==targets,'quadratic row target metadata')
 term_count=0
 for row in q9['rows']:
  for term in row['terms']:
   alpha=term['alpha'];need(len(alpha)==31 and all(type(x) is int and x>=0 for x in alpha) and sum(alpha)<=2,'quadratic exponent metadata')
   weight=sum(a*b for a,b in zip(alpha,w[1:]));factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(x) for x in alpha)
   need(term['weight']==weight,'stale term weight metadata')
   need(term['encoding_exponent']==row['target_exponent']-weight,'term encoding exponent metadata')
   need(term['multinomial_inverse_weight']==factor,'term factorial metadata')
   need(parse(term['weighted_coefficient'])=={p:c*factor for p,c in parse(term['coefficient']).items()},'unweighted source coefficient metadata')
   term_count+=1
 need(term_count==q9['shifted_row_term_count']==136,'quadratic term count metadata')
 target_hash=hashlib.sha256(target_path.read_bytes()).hexdigest()
 nine_paths=sorted((ROOT/'nine/generated').glob('multitarget_nine_*.json'))
 need(len(nine_paths)==4,'nine-variable artifact count')
 for path in nine_paths:
  body=json.loads(path.read_text())
  link(path,body,'coefficient_binding','coefficients/COEFFICIENT_BINDING.json')
  link(path,body,'fixed_leaf_binding','fixed/FIXED_LEAVES.json')
  link(path,body,'proof','SPARSE_PACKING_PROOF.md')
  need(body['target_records_sha256']==target_hash,'nine target record digest')
  need(body['weights']==w[1:] and body['W']==200,'nine weight metadata')
  need(body['target_maximum']==8821 and body['Kcode']==9221,'nine source support metadata')
  need(body['row_order']==q9['row_order_one_based'],'nine source row order metadata')
 path=ROOT/'data/polynomial.json';body=json.loads(path.read_text())
 link(path,body,'coefficient_binding','data/coefficient_recipes.json')
 link(path,body,'native_coefficient_binding','coefficients/COEFFICIENT_BINDING.json')
 link(path,body,'fixed_leaf_binding','fixed/FIXED_LEAVES.json')
 link(path,body,'proof','sections/ten.tex')
 need(body['source_parameters']=={'maximum_weight':200,'targets':targets,'span':9221,'beta_exponent':2140030},'ten source parameter metadata')
 return {'local_file_references':references,'term_weights_and_encoding_exponents':term_count,'parent_source_sha256':q9['source_sha256'],'nine_target_records_sha256':target_hash,'nine_artifact_digests_checked':len(nine_paths)}

def main():
 norm_certificate=norm_identities()
 w=jread('data/weights.json')['weights'];need(w[0]==0 and len(w)==len(set(w))==32 and min(w[1:])>0,'weight shape')
 data10=jread('data/coefficient_recipes.json');rows10=weighted_rows(data10);parent=exact_parent()
 for row,raw in zip(rows10,parent):
  expected={m:c*math.factorial(2-sum(m[:31]))*math.prod(math.factorial(x) for x in m[:31]) for m,c in raw.items()};need(row==expected,'coefficient recipe vs exact parent')
 q9=jread('quartic/QUADRATIC_TARGETS.json');metadata_certificate=check_artifact_metadata(w,q9);rows9=weighted_rows(q9)
 for row,raw in zip(rows9,exact_parent('upstream/parent_system60.json')):
  expected={m:c*math.factorial(2-sum(m[:31]))*math.prod(math.factorial(x) for x in m[:31]) for m,c in raw.items()};need(row==expected,'nine coefficient recipe vs exact shifted parent')
 # The exact affine transport shift z_old=z+1 changes only row14 by -(q-1).
 for i,(a,b) in enumerate(zip(rows10,rows9)):
  diff=add(a,b,-1)
  if i!=13:need(not diff,'unexpected parent difference')
  else:
   p=(1,0,0,0);zero=(0,)*31;jmon=(1,)+(0,)*30
   need(diff=={zero+p:2,jmon+p:1},'transport shift differs from q-1')
 targets=[400+401*j for j in range(22)]
 extraction10=check_packing(w,rows10,targets);extraction9=check_packing(w,rows9,targets)
 corrupted=w.copy();corrupted[2]=corrupted[1]
 try:check_packing(corrupted,rows9,targets)
 except ValueError:negative_control=True
 else:raise ValueError('collision negative control escaped')
 ports=[];bindings=[];expected_binding={r['port']:r for r in jread('coefficients/COEFFICIENT_BINDING.json')['files']}
 for name in ['beta','K','MC','MF_source']:
  path=ROOT/'coefficients/payloads'/f'{name}.bin.gz';raw=gzip.decompress(path.read_bytes());ports.append(int.from_bytes(raw,'little'))
  need(hashlib.sha256(raw).hexdigest()==expected_binding[name]['sha256'],'inherited raw coefficient digest')
  bindings.append({'name':name,'raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw),'bits':ports[-1].bit_length()})
 need([x.bit_length() for x in ports]==[1064921,1070004,1064921,1064922],'coherent package31 port bit lengths')
 b10=jread('data/polynomial.json');p9=jread('nine/generated/multitarget_nine_positive.json');c9=jread('nine/generated/multitarget_nine_positive_degree_certificate.json');n9=jread('nine/generated/multitarget_nine_natural.json')
 fixed_leaf_checks=0
 for family,circuit in [('signed10',b10),('positive9',p9)]:
  entries=jread('fixed/FIXED_LEAVES.json')[family]
  need({e['name'] for e in entries}=={n['name'] for n in circuit['nodes'] if n['kind']=='fixed'},'materialized live coefficient coverage')
  for e in entries:
   raw=gzip.decompress((ROOT/e['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==e['raw_sha256'],'fixed leaf digest');need(raw[0] in (0,1),'fixed leaf sign encoding')
   value=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1);recipe=e['recipe'];want=(1<<recipe['power_of_two']) if isinstance(recipe,dict) else pval(recipe,ports)
   need(value==want,'fixed leaf exact recipe');fixed_leaf_checks+=1
 need(sum(counts(b10).values())==653,'ten operation count');need(sum(counts(p9).values())==652,'nine positive operation count');need(sum(counts(n9).values())==655,'nine natural operation count');counts(c9)
 degree_certs=[];replays=0
 for prime in [1000000007,1000000009,998244353]:
  f10={n:pval(rec,ports,prime) for n,rec in data10['recipes'].items()};f10['beta_source']=pow(2,data10['beta_source_exponent'],prime)
  f9={r['name']:pval(r['terms'],ports,prime) for r in p9['coefficient_recipes']};f9['base_floor']=pow(2,p9['base_floor_exponent'],prime)
  d10,l10=degree(b10,f10,prime);d9,l9=degree(c9,f9,prime)
  need(d10==59564744 and l10!=0,'ten exact degree certificate');need(d9==32568568 and l9==pow(2,2050,prime),'nine exact degree certificate')
  degree_certs.append({'prime':prime,'nine_degree':d9,'nine_diagonal_leader':l9,'ten_degree':d10,'ten_diagonal_leader':l10})
  rng=random.Random(20261023+prime)
  for _ in range(40):
   vals={name:rng.randrange(1,300) for name in p9['variables']};v,_=dag(p9,vals,f9,prime);vc,_=dag(c9,vals,f9,prime);vn,_=dag(n9,{n:x-1 for n,x in vals.items()},f9,prime)
   need(v==vc==vn,'nine formula/certificate/domain replay');replays+=1
 need((1<<data10['beta_source_exponent'])>4*33**2*8*(1+sum(ports))**2,'ten source coefficient bound')
 for recipe in p9['coefficient_recipes']:need(abs(pval(recipe['terms'],ports))<(1<<p9['coefficient_bound_power_of_two']),'nine source coefficient bound')
 result={'status':'PASS','scope':'Finite exact source coefficient identities, bindings and degree/circuit certificates; not an end-to-end proof-assistant certificate or a consistency test.','source_commit':'124c07c0b77a9e20e84676514d8b1ff78536ea3f','packing_nine':extraction9,'packing_ten':extraction10,'collision_negative_control':negative_control,'norm_identity_certificates':norm_certificate,'materialized_fixed_leaf_checks':fixed_leaf_checks,'bindings':bindings,'nine_positive':{'variables':9,'degree':32568568,'operations':652,'counts':counts(p9)},'nine_natural':{'variables':9,'degree':32568568,'operations':655,'counts':counts(n9)},'ten_integer':{'variables':10,'degree':59564744,'operations':653,'counts':counts(b10)},'degree_certificates':degree_certs,'modular_formula_domain_replays':replays}
 result['artifact_metadata_checks']=metadata_certificate
 (ROOT/'certificates/sparse_extraction.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()

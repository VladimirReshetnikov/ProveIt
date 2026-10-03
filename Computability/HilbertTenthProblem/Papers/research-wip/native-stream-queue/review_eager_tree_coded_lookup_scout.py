#!/usr/bin/env python3
"""Independent finite-source and natural-domain audit of coded Tree lookups."""
import argparse,copy,hashlib,itertools,json,math,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
 'eager_tree_coded_lookup_scout.py':'b2769ca2c8b8754f5b5c9d65c0ad97a5f590c5b6ebc5712a2964ac1d1a1d0e73',
 'eager_tree_coded_lookup_scout.json':'acfcbd04609e49150a0e9089c7937ca0fcd20b852a337a3e39248a4e582d01c6',
 'eager_tree_coded_lookup_scout.md':'81d9be0663b212039802c1c841dd200e82baedc02ecf1005957e8f90beef457b',
 'eager_tree_constructor_projection.py':'a4c09cc720ac0d5b7f884e8636900a93ba6c17a7040a0f01c83b94f6f469bc81',
 'eager_tree_constructor_projection.json':'26bf1f948751f94e77e5716fddc0668c8d8c910bcb2ac6237b50ece7a9090852',
 'eager_tree_constructor_projection.md':'c5a65687c3756f220e11210525e9bc6ce7968ec2def7348a9dcf5d2cb69d8fc7',
}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def digest(a):return hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def read(root,name):
 p=Path(root)/name;b=p.read_bytes();need(hashlib.sha256(b).hexdigest()==PINS[name],'Pin '+str(p));return b

def constant(x):return {():x}if x else{}
def variable(x):return{((x,1),):1}
def plus(a,b,sign=1):
 z=dict(a)
 for m,v in b.items():z[m]=z.get(m,0)+sign*v
 return {m:v for m,v in z.items()if v}
def times(a,b):
 z={}
 for m,u in a.items():
  for n,v in b.items():
   d=dict(m)
   for x,k in n:d[x]=d.get(x,0)+k
   q=tuple(sorted(d.items()));z[q]=z.get(q,0)+u*v
 return {m:v for m,v in z.items()if v}
def power(a,k):
 z=constant(1)
 for _ in range(k):z=times(z,a)
 return z
def polynomial_degree(a):return max((sum(k for _,k in m)for m in a),default=0)
def poly_rows(rows,free,old=None):
 env={x:variable(x)for x in free}
 for n,o,a,b in rows:
  if old is not None and n in old:env[n]=old[n];continue
  x=env[a]if type(a)is str else constant(a);y=env[b]if type(b)is str else constant(b)
  env[n]=times(x,y)if o=='*'else plus(x,y,1 if o=='+'else -1)
 return env
def pair(a,b):return plus(power(plus(a,b),2),a)
def code(coords,order):
 x,y,z=[coords[i]for i in order];return pair(x,pair(y,z))
def numeric(rows,a):
 e=dict(a)
 for n,o,x,y in rows:
  x=e[x]if type(x)is str else x;y=e[y]if type(y)is str else y;e[n]=x+y if o=='+'else x-y if o=='-'else x*y
 return e

def ledger(rows,free,out):
 seen=set(free);defs={};deg={v:1 for v in free}
 need(len(seen)==len(free),'unique free')
 for row in rows:
  need(type(row)is list and len(row)==4,'row grammar');n,o,a,b=row
  need(type(n)is str and n not in seen and o in('+','-','*'),'fresh gate')
  for x in(a,b):need(type(x)is int or type(x)is str and x in seen,'closed exact operand')
  da=deg[a]if type(a)is str else 0;db=deg[b]if type(b)is str else 0
  deg[n]=da+db if o=='*'else max(da,db);seen.add(n);defs[n]=[a,b]
 live=set();todo=list(out)
 while todo:
  x=todo.pop()
  if type(x)is int or x in live:continue
  live.add(x);todo+=defs.get(x,[])
 need(set(defs)<=live and set(free)<=live,'literal liveness')
 M=sum(r[1]=='*'for r in rows)
 return dict(M=M,A=len(rows)-M,operations=len(rows),degree_upper_bound=max(deg[x]if type(x)is str else 0 for x in out),all_live=True)

def sos(p):
 rows=p['polynomial_source'];base=p['source'];rs=p['residuals'];need(rows[:len(base)]==base,'finalizer prefix')
 need(len(rows)-len(base)==2*len(rs)-1,'complete finalizer length')
 env={r:variable('residual_'+str(i))for i,r in enumerate(rs)}
 for n,o,a,b in rows[len(base):]:
  need(type(a)is str and a in env and type(b)is str and b in env,'finalizer only paid residual/sum ports')
  env[n]=times(env[a],env[b])if o=='*'else plus(env[a],env[b],1 if o=='+'else -1)
 want={}
 for i in range(len(rs)):want=plus(want,power(variable('residual_'+str(i)),2))
 need(env[p['output']]==want,'entire abstract SOS')
 need(sum(r[1]=='*'for r in rows[len(base):])==len(rs),'one square per residual')

def weights(i):
 v=lambda f:variable(f'r{i}_{f}')
 t3,t4=v('t3'),v('t4');a,b,y,u,vv,z=[v(f)for f in('a','b','y','u','v','z')]
 return [
  [plus(times(t3,b),times(t4,y)),plus(times(t3,y),times(t4,a)),times(plus(t3,t4),u)],
  [plus(times(t3,a),times(t4,u)),plus(times(t3,y),times(t4,b)),plus(times(t3,vv),times(t4,z))],
  [times(t3,u),times(t3,vv),times(t3,z)],
 ]
def targets(i,mode,order):
 v=lambda f:variable(f'r{i}_{f}')
 t3,t4=v('t3'),v('t4')
 if mode=='weighted':return [code(c,order)for c in weights(i)]
 branches=[(('b','y','u'),('y','a','u')),(('a','y','v'),('u','b','z'))]
 out=[plus(times(t3,code([v(f)for f in a],order)),times(t4,code([v(f)for f in b],order)))for a,b in branches]
 out.append(times(t3,code([v(f)for f in('u','v','z')],order)))
 if mode=='hybrid':out[0]=pair(times(plus(t3,t4),v('u')),plus(times(t3,pair(v('b'),v('y'))),times(t4,pair(v('y'),v('a')))))
 return out

def verify(root,artifacts):
 parent_data={n:read(root,n)for n in PINS if 'coded_lookup'not in n}
 read(artifacts,'eager_tree_coded_lookup_scout.md')
 author_source=read(artifacts,'eager_tree_coded_lookup_scout.py');saved=json.loads(read(artifacts,'eager_tree_coded_lookup_scout.json'))
 need(saved['source_sha256']==PINS['eager_tree_coded_lookup_scout.py'],'receipt pin')
 author=types.ModuleType('_reviewed_coded_tree');author.__file__=str(Path(artifacts)/'eager_tree_coded_lookup_scout.py');exec(compile(author_source,author.__file__,'exec'),author.__dict__)
 parent_receipt=json.loads(parent_data['eager_tree_constructor_projection.json']);parents={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in parent_receipt['forms']}
 counts=dict(census_sources=0,selected_full_packets=0,paid_gates=0,retained_literal_rows=0,retained_residual_identities=0,old_lookup_identities=0,new_lookup_identities=0,target_identities=0,whole_sos_corrections=0,exact_degrees=0,whole_evaluations=0,rational_evaluations=0,guards=0,copies=0,pins=0)
 oldenvs={}
 for key,p in parents.items():
  sos(p);env=poly_rows(p['source'],p['free']);oldenvs[key]=env
  for i in range(p['N']):
   w=weights(i)
   tag_sum={}
   for t in range(5):tag_sum=plus(tag_sum,variable(f'r{i}_t{t}'))
   need(env[p['residuals'][17*i]]==plus(tag_sum,constant(1),-1),'actual common natural one-hot row')
   for slot in range(3):
    active=plus(variable(f'r{i}_t3'),variable(f'r{i}_t4'))if slot<2 else variable(f'r{i}_t3')
    ps={}
    for j in range(i+1,p['N']):ps=plus(ps,variable(f'r{i}_p{slot}_{j}'))
    need(env[p['residuals'][17*i+5+slot]]==plus(ps,active,-1),'actual common pointer row')
    for column,field in enumerate(('x','y','z')):
     wanted={}
     for j in range(i+1,p['N']):wanted=plus(wanted,times(variable(f'r{i}_p{slot}_{j}'),variable(f'r{j}_{field}')))
     wanted=plus(wanted,w[slot][column],-1)
     need(env[p['residuals'][17*i+8+3*slot+column]]==wanted,'actual old lookup semantics');counts['old_lookup_identities']+=1
 rng=random.Random(17301);selected_hashes={digest(p):p for p in saved['selected_full_packets']};matched=set();census=[];n8={};whole_nonidentity=None
 # Independently generate exactly the declared family and check multiplicity.
 expected_recipes={(N,c,'gated',o,s,a)for N in range(1,9)for c in(False,True)for o in itertools.permutations(range(3))for s in(False,True)for a in(False,True)}
 expected_recipes|={(N,c,'weighted',(0,1,2),False,False)for N in range(1,9)for c in(False,True)}
 expected_recipes|={(N,c,'hybrid',(2,0,1),True,True)for N in range(1,9)for c in(False,True)}
 actual_recipes=[(r['N'],r['cleanup'],r['mode'],tuple(r['order']),r['sharing'],r['algebra'])for r in saved['census']]
 need(len(actual_recipes)==len(set(actual_recipes))==416 and set(actual_recipes)==expected_recipes,'exact independent recipe coverage')
 # Other supported option combinations are not a census claim.
 for rec in saved['census']:
  N=rec['N'];cleanup=rec['cleanup'];mode=rec['mode'];order=tuple(rec['order'])
  p=author.build(N,cleanup=cleanup,mode=mode,order=order,sharing=rec['sharing'],algebra=rec['algebra'],root=root)
  need(exact(author.checked(p,root=root),p),'canonical packet')
  old=parents[N,cleanup];oldenv=oldenvs[N,cleanup];oldrows={r[0]:r for r in old['source']}
  need(p['free']==old['free']and p['witnesses']==(3*N*N+23*N)//2,'same full interface')
  need(p['residual_count']==len(p['residuals'])==11*N+3,'residual count')
  need(p['parent_residuals']==old['residuals']and p['full_polynomial_identity']is False and p['natural_zero_tuple_equivalent']is True,'current parent and domain metadata')
  removed={17*i+j for i in range(N)for j in range(8,17)};kept=[i for i in range(len(old['residuals']))if i not in removed]
  need(p['retained_parent_indices']==kept and p['residuals'][:len(kept)]==[old['residuals'][i]for i in kept],'exact retained map')
  for row in p['source']:
   if row[0]in oldrows:need(row==oldrows[row[0]],'unchanged literal parent arithmetic');counts['retained_literal_rows']+=1
  actual=ledger(p['polynomial_source'],p['free'],[p['output']]);need(actual==p['polynomial_ledger']==rec['ledger'],'full independent ledger')
  need(ledger(p['source'],p['free'],p['residuals'])==p['certificate_ledger'],'certificate ledger');sos(p)
  need(digest(p['polynomial_source'])==rec['source_sha256'],'census complete source hash')
  counts['paid_gates']+=actual['operations']
  env=poly_rows(p['source'],p['free'],oldenv)
  for idx in kept:need(env[old['residuals'][idx]]==oldenv[old['residuals'][idx]],'retained residual identity');counts['retained_residual_identities']+=1
  need(set(p['row_code_ports'])=={str(j)for j in range(1,N)},'no unpaid or dead root-row code')
  for j,port in p['row_code_ports'].items():need(env[port]==code([variable(f'r{j}_{f}')for f in('x','y','z')],order),'entire referenced row code')
  for i in range(N):
   ts=targets(i,mode,order)
   for slot in range(3):
    m=p['lookup_map'][3*i+slot]
    need(m['row']==i and m['slot']==slot and m['parent_indices']==list(range(17*i+8+3*slot,17*i+11+3*slot)),'current lookup map')
    need(m['target_parent_ports']==[oldrows[old['residuals'][idx]][3]for idx in m['parent_indices']]and m['target_port']==p['target_code_ports'][i][slot],'actual target metadata')
    want={}
    for j in range(i+1,N):want=plus(want,times(variable(f'r{i}_p{slot}_{j}'),code([variable(f'r{j}_{f}')for f in('x','y','z')],order)))
    want=plus(want,ts[slot],-1)
    need(env[m['child_port']]==want,'full literal new residual coefficients');counts['new_lookup_identities']+=1
    need(env[m['target_port']]==ts[slot],'whole target formula');counts['target_identities']+=1
  maxdeg=max(polynomial_degree(env[r])for r in p['residuals']);want_degree={'gated':10,'weighted':16,'hybrid':12}[mode]
  need(2*maxdeg==want_degree==p['exact_degree']==actual['degree_upper_bound'],'exact actual degree by nonzero SOS leaders');counts['exact_degrees']+=1
  # Same retained residuals plus two literal SOS finalizers prove the complete correction.
  counts['whole_sos_corrections']+=1;counts['census_sources']+=1
  census.append([N,cleanup,mode,list(order),rec['sharing'],rec['algebra'],actual['M'],actual['A'],want_degree])
  key=digest(p)
  if key in selected_hashes:
   need(exact(p,selected_hashes[key]),'selected full packet canonical');matched.add(key)
   for case in range(4):
    a={f:rng.randrange(0,4)for f in p['free']}
    if case>0:a={f:(-v if j%3==0 else v)for j,(f,v)in enumerate(a.items())}
    if case==3:a={f:Fraction(v,3)for f,v in a.items()};counts['rational_evaluations']+=1
    before=numeric(old['polynomial_source'],a);after=numeric(p['polynomial_source'],a)
    corr=sum(after[m['child_port']]**2-sum(before[old['residuals'][k]]**2 for k in m['parent_indices'])for m in p['lookup_map'])
    need(after[p['output']]-before[old['output']]==corr,'whole numeric correction');counts['whole_evaluations']+=1
    if whole_nonidentity is None and corr and case==0:whole_nonidentity=dict(N=N,mode=mode,assignment=a,old=before[old['output']],new=after[p['output']],difference=corr)
  if not rec['sharing']and not rec['algebra']:
   expected=(9*N*N+(229-2*int(cleanup))*N+16)//2;need(actual['operations']==expected,'complete unshared formula')
  if mode=='gated'and order==(2,0,1)and rec['algebra']:
   need((actual['M'],actual['A'])==((3*N*N+87*N+2)//2,3*N*N+(67-int(cleanup))*N+7),'full gated formula')
  if mode=='hybrid':need((actual['M'],actual['A'])==((3*N*N+87*N+2)//2,3*N*N+(65-int(cleanup))*N+7),'full hybrid formula')
  if N==8 and cleanup and order==(2,0,1)and rec['sharing']and rec['algebra']:n8[mode]=actual
 need(matched==set(selected_hashes),'all saved selected packets reviewed');counts['selected_full_packets']=len(matched)
 need(n8['gated']['operations']==1172 and n8['hybrid']['operations']==1156,'N8 frontiers')
 # Independent exact chart proof on one generic row; row renaming gives all rows.
 charts=0
 def specialize(poly,t3,t4):
  z={}
  for mon,c in poly.items():
   rest=[]
   for v,k in mon:
    if v=='r0_t3':c*=t3**k
    elif v=='r0_t4':c*=t4**k
    else:rest.append((v,k))
   z[tuple(rest)]=z.get(tuple(rest),0)+c
  return {m:c for m,c in z.items()if c}
 for mode in('gated','weighted','hybrid'):
  for order in itertools.permutations(range(3)):
   if mode=='hybrid'and order!=(2,0,1):continue
   ts=targets(0,mode,order)
   for bits in((0,0),(1,0),(0,1)):
    for slot in range(3):need(specialize(ts[slot],*bits)==specialize(code(weights(0)[slot],order),*bits),'natural tag-chart coefficient proof');charts+=1
 decode_cases=0
 def decode(v):
  s=math.isqrt(v);u=v-s*s;need(0<=u<=s,'code shell');return u,s-u
 for order in itertools.permutations(range(3)):
  for triple in itertools.product(range(7),repeat=3):
   x,y,z=[triple[i]for i in order];value=(x+((y+z)**2+y))**2+x
   xx,inner=decode(value);yy,zz=decode(inner);back=[None]*3
   for i,v in zip(order,(xx,yy,zz)):back[i]=v
   need(tuple(back)==triple,'explicit natural code inverse');decode_cases+=1
 need(((-1+0)**2-1)==0 and (Fraction(7,16)+Fraction(5,16))**2+Fraction(7,16)==1,'scope counterexamples')
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('malformed accepted')
 for x in(True,False,0,-1,9,1.0,'2',None):reject(lambda x=x:author.build(x,root=root))
 for opt in('cleanup','sharing','algebra'):
  for x in(0,1,0.0,None,'true'):reject(lambda opt=opt,x=x:author.build(2,root=root,**{opt:x}))
 for order in([2,0,1],(2,False,1),(2,0,0),(1,2),None):reject(lambda order=order:author.build(2,order=order,root=root))
 p=author.build(2,root=root)
 for k in p:
  z=copy.deepcopy(p);del z[k];reject(lambda z=z:author.checked(z,root=root))
 for k in('N','residual_count','witnesses','exact_degree'):
  z=copy.deepcopy(p);z[k]=float(z[k]);reject(lambda z=z:author.checked(z,root=root))
 for k in('source','polynomial_source','residuals','lookup_map','free','parent_pins','paid_pair_recipes'):
  z=copy.deepcopy(p);z[k]=None;reject(lambda z=z:author.checked(z,root=root))
 for k in('source','lookup_map','parent_pins','free'):
  z=author.build(2,root=root);z[k].clear();need(exact(author.build(2,root=root),p),'defensive rebuilt copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='review-coded-tree-')as tmp:
  for n,b in parent_data.items():(Path(tmp)/n).write_bytes(b)
  author.build(2,root=tmp)
  for n,b in parent_data.items():
   (Path(tmp)/n).write_bytes(b+b' ');reject(lambda:author.build(2,root=tmp));(Path(tmp)/n).write_bytes(b);counts['pins']+=1
 optimized=subprocess.run([sys.executable,'-O',author.__file__],capture_output=True,text=True,timeout=30);need(optimized.returncode!=0 and 'Run without -O'in optimized.stderr,'author optimized guard')
 return dict(status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pins=PINS,counts=counts,census_digest=digest(census),generic_tag_chart_identities=charts,explicit_natural_decode_cases=decode_cases,N8=n8,complete_offzero_nonidentity=whole_nonidentity,scope='All416 declared recipes and19 saved full packets; same-coordinate natural zero proof, all-value correction, exact degree. No historical author verify calls; no general circuit optimality or fixed-arity claim.')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()

"""Finite eager Tree leaf-tag projection with nonnegative integer guards.

All16 pinned terminal sources. This is a mixed nonnegative finalizer, not SOS.
Natural zero bijection; signed polynomial pullback has an explicit correction.
"""
import argparse,copy,hashlib,json,math,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_terminal_projection.py':'edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd','eager_tree_terminal_projection.json':'25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95','eager_tree_terminal_projection.md':'ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b'}

def need(v,msg):
 if not v:raise ValueError(msg)

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def _live(rows,ports):
 live={r for r in ports if type(r)is str}
 for n,o,a,b in reversed(rows):
  if n in live:live.update(x for x in(a,b)if type(x)is str)
 return [r for r in rows if r[0]in live]

def _inspect(rows,free,ports):
 degree={v:1 for v in free};deps={};M=0
 for row in rows:
  need(type(row)is list and len(row)==4,'Literal source row');n,o,a,b=row
  need(type(n)is str and n not in degree and o in('+','-','*'),'Fresh gate')
  need(all(type(x)is int or type(x)is str and x in degree for x in(a,b)),'Exact closed operand')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0;degree[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);M+=o=='*'
 live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'All arithmetic and supplied coordinates live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),degree_upper_bound=max(degree[n]if type(n)is str else 0 for n in ports),all_live=True)

def _assignment(p,v,signed):
 need(type(signed)is bool and type(v)is dict and set(v)==set(p['free']),'Exact mode and complete assignment')
 need(all(type(n)is str and type(x)is int for n,x in v.items()),'Exact integer assignment')
 if not signed:need(all(x>=0 for x in v.values()),'Natural coordinates')
 return dict(v)

def _run(rows,v):
 env=dict(v)
 for n,o,a,b in rows:
  a=env[a]if type(a)is str else a;b=env[b]if type(b)is str else b;env[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return env

def _coefficients(rows,free):
 env={n:[0,1]for n in free}
 for n,o,a,b in rows:
  a=env[a]if type(a)is str else[a];b=env[b]if type(b)is str else[b];p=[0]*(len(a)+len(b)-1 if o=='*'else max(len(a),len(b)))
  if o=='*':
   for i,x in enumerate(a):
    for j,y in enumerate(b):p[i+j]+=x*y
  else:
   for i,x in enumerate(a):p[i]+=x
   for i,x in enumerate(b):p[i]+=x if o=='+'else-x
  while len(p)>1 and p[-1]==0:p.pop()
  env[n]=p
 return env

def S(a):return 2*a+1

def F(a,b):return (a+b)*(a+b+1)+2*b+2

def split(x):
 if x==0:return(0,)
 if x%2:return(1,(x-1)//2)
 n=(x-2)//2;t=(math.isqrt(8*n+1)-1)//2;b=n-t*(t+1)//2;return(2,t-b,b)

def application(x,y,budget=100):
 records={};active=set();fuel=[budget]
 def rec(x,y):
  if(x,y)in records:return records[x,y]['z']
  if(x,y)in active or fuel[0]<=0 or max(x.bit_length(),y.bit_length())>96:raise ValueError('bounded evaluator limit')
  active.add((x,y));fuel[0]-=1;a=b=c=u=v=0;children=[];sx=split(x)
  if sx[0]==0:tag=0;z=S(y)
  elif sx[0]==1:tag=1;a=sx[1];z=F(a,y)
  else:
   first,b=sx[1:];sf=split(first)
   if sf[0]==0:tag=2;z=b
   elif sf[0]==1:
    tag=3;a=sf[1];u=rec(b,y);v=rec(a,y);z=rec(u,v);children=[(b,y),(a,y),(u,v)]
   else:
    tag=4;a,bb=sf[1:];c=b;b=bb;u=rec(y,a);z=rec(u,b);children=[(y,a),(u,b)]
  if z.bit_length()>96:raise ValueError('bounded code size')
  records[x,y]=dict(x=x,y=y,z=z,a=a,b=b,c=c,u=u,v=v,tag=tag,children=children)
  active.remove((x,y));return z
 z=rec(x,y);return z,records

def flatten_records(records,keys,external):
 N=len(keys);d={};index={key:i for i,key in enumerate(keys)if key is not None}
 for i,key in enumerate(keys):
  r=records[key]if key is not None else dict(x=0,y=0,z=1,a=0,b=0,c=0,u=0,v=0,tag=0,children=[])
  for f in('x','y','z','a','b','c','u','v'):d[f'r{i}_{f}']=r[f]
  a,b,c,y=[r[n]for n in('a','b','c','y')]
  for f,v in dict(d=F(a,b),e=F(a,y),q=F(0,b),j=F(S(a),b),k=F(F(a,b),c),mu=0).items():d[f'r{i}_{f}']=v
  for tag in range(5):d[f'r{i}_t{tag}']=int(r['tag']==tag)
  for s in range(3):
   for j in range(N):d[f'r{i}_p{s}_{j}']=int(s<len(r['children'])and index[r['children'][s]]==j)
 d.update(zip(('program','argument','output'),external));return d

def _parents(root):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Parent pin '+name);blobs[name]=b
 receipt=json.loads(blobs['eager_tree_terminal_projection.json']);need(receipt['source_sha256']==PINS['eager_tree_terminal_projection.py'],'Parent source lineage')
 forms={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in receipt['forms']}
 need(len(receipt['forms'])==16 and set(forms)=={(N,c)for N in range(1,9)for c in(False,True)},'Exact parent family');return forms

def _rewrite(old):
 N=old['N'];defs={r[0]:r[1:]for r in old['source']};positions={r[0]:i for i,r in enumerate(old['source'])};rowmap=[];insertions={};removed=set();leafchanges={};guards=[]
 for i in range(N):
  tag=f'r{i}_t0';tagrow=old['residuals'][5*i];leaf=old['residuals'][5*i+2];need(defs[tagrow][0]=='-'and defs[tagrow][2]==1,'Literal one-hot subtraction')
  top=defs[tagrow][1];chain=[tagrow]
  for k in reversed(range(2,3 if i==N-1 else 5)):
   need(defs[top][0]=='+'and defs[top][2]==f'r{i}_t{k}','Literal ordered tag chain');chain.append(top);top=defs[top][1]
  need(defs[top]==['+',tag,f'r{i}_t1'],'Literal first tag addition');chain.append(top);chain.reverse()
  need(defs[leaf][0]=='*'and defs[leaf][1]==tag,'Literal leaf residual')
  need([r[0]for r in old['source']if tag in r[2:]]==[top,leaf],'Exact t0 consumer closure')
  need(all([r[0]for r in old['source']if p in r[2:]]==[chain[j+1]]for j,p in enumerate(chain[:-1])),'Private removed chain')
  pair=f'leaf_tag_pair_{i}';sm=f'leaf_tag_sum_{i}';minus=f'leaf_tag_minus_{i}';guard=f'leaf_tag_guard_{i}';new=[[pair,'+',f'r{i}_t1',f'r{i}_t2']]
  active=None
  if i<N-1:
   candidates=[r[0]for r in old['source']if r[1:]==['+',f'r{i}_t3',f'r{i}_t4']];need(len(candidates)==1,'Unique already paid active port');active=candidates[0];need(positions[active]<positions[top],'Paid active precedes new sum');new.append([sm,'+',pair,active])
  else:sm=pair
  new.extend([[minus,'-',sm,1],[guard,'*',sm,minus]]);insertions[top]=new;removed.update(chain);leafchanges[leaf]=minus;guards.append(guard)
  rowmap.append(dict(row=i,parent_tag=tag,parent_tag_residual=tagrow,parent_leaf_residual=leaf,active_port=active,tag_sum=sm,sum_minus_one=minus,guard=guard,removed_chain=chain))
 rows=[]
 for n,o,a,b in old['source']:
  rows.extend(insertions.get(n,[]))
  if n in removed:continue
  if n in leafchanges:a=leafchanges[n]
  rows.append([n,o,a,b])
 ordinary=[r for j,r in enumerate(old['residuals'])if j not in{5*i for i in range(N)}];terms=[]
 for j,r in enumerate(old['residuals']):
  if j in{5*i for i in range(N)}:terms.append(dict(kind='integer_nonnegative_guard',port=guards[j//5]))
  else:terms.append(dict(kind='square',port=r))
 ports=[t['port']for t in terms];rows=_live(rows,ports);free=[v for v in old['free']if v not in{m['parent_tag']for m in rowmap}];poly=copy.deepcopy(rows);accports=[]
 for i,t in enumerate(terms):
  if t['kind']=='square':name=f'leaf_square_{i}';poly.append([name,'*',t['port'],t['port']]);accports.append(name)
  else:accports.append(t['port'])
 out=accports[0]
 for i,p in enumerate(accports[1:],1):name=f'leaf_sum_{i}';poly.append([name,'+',out,p]);out=name
 cert=_inspect(rows,free,ports);ledger=_inspect(poly,free,[out]);epsilon=int(old['cleanup'])
 need((ledger['M'],ledger['A'],ledger['operations'])==((3*N*N+81*N-46)//2,(3*N*N+(127-2*epsilon)*N-76)//2,3*N*N+(104-epsilon)*N-61),'Complete paid formula')
 need(old['polynomial_ledger']['M']==ledger['M']and old['polynomial_ledger']['A']-ledger['A']==2*N-1,'Only2N-1 additions saved')
 need(cert['M']-old['certificate_ledger']['M']==N and old['certificate_ledger']['A']-cert['A']==2*N-1,'Mixed certificate ledger')
 degree=6 if N==1 else 10*N-8;need(ledger['degree_upper_bound']==degree and len(free)-3==12*N-5,'Supplied arity and degree upper')
 need(len(ordinary)==7*N and len(terms)==8*N,'Mixed finalizer term accounting')
 return dict(N=N,cleanup=old['cleanup'],free=free,source=rows,ordinary_residuals=ordinary,integer_guard_ports=guards,finalizer_terms=terms,polynomial_source=poly,output=out,certificate_ledger=cert,polynomial_ledger=ledger,witnesses=len(free)-3,squared_residual_count=7*N,unsquared_guard_count=N,nonnegative_term_count=8*N,exact_degree=degree,row_map=rowmap,parent_pins=copy.deepcopy(PINS),full_polynomial_identity=False,graph_correction='Fchild=Fparent[t0_i=1-s_i]+sum_i s_i(s_i-1)',natural_zero_bijection=True,unconditional_natural_pullback=False,sos_finalizer=False,degree_certificate=dict(diagonal_leading_coefficient=17 if N==1 else 8*2**(10*(N-1))+2**(8*(N-1)),reason='Unchanged leading squared source residuals; leaf substitution and guard degree at most4 and2.'),scope='All supplied coordinates natural including zero. Full zero-tuple bijection with the pinned terminal parent only; its earlier projection limitations remain. Exact externalN1..8; no fixed-arity universal or new decoder claim.')

def canonical_parent(N,*,cleanup=True,root=None):
 need(type(N)is int and 1<=N<=8 and type(cleanup)is bool,'Exact saved N/cleanup');return _parents(root)[N,cleanup]
def build(N,*,cleanup=True,root=None):return _rewrite(canonical_parent(N,cleanup=cleanup,root=root))
def rewrite(parent,*,root=None):
 need(type(parent)is dict,'Complete parent packet');p=canonical_parent(parent.get('N'),cleanup=parent.get('cleanup'),root=root);need(exact(parent,p),'Canonical parent');return _rewrite(p)
def checked(packet,*,root=None):
 need(type(packet)is dict,'Complete child packet');p=build(packet.get('N'),cleanup=packet.get('cleanup'),root=root);need(exact(p,packet),'Canonical full child');return p
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);v=_assignment(p,values,signed);return _run(p['polynomial_source'],v)[p['output']]
def _pullback(p,v):
 out=dict(v)
 for m in p['row_map']:
  i=m['row'];s=sum(v[f'r{i}_t{k}']for k in range(1,3 if i==p['N']-1 else 5));out[m['parent_tag']]=1-s
 return out
def integer_pullback(packet,values,*,root=None):
 p=checked(packet,root=root);return _pullback(p,_assignment(p,values,True))
def restore_zero(packet,values,*,root=None):
 p=checked(packet,root=root);v=_assignment(p,values,False);need(_run(p['polynomial_source'],v)[p['output']]==0,'Complete child natural zero required');out=_pullback(p,v);need(all(x>=0 for x in out.values()),'Restored natural tags');old=canonical_parent(p['N'],cleanup=p['cleanup'],root=root);need(_run(old['polynomial_source'],out)[old['output']]==0,'Restored complete parent zero');return out
def project_parent_zero(packet,values,*,root=None):
 p=checked(packet,root=root);old=canonical_parent(p['N'],cleanup=p['cleanup'],root=root);v=_assignment(old,values,False);need(_run(old['polynomial_source'],v)[old['output']]==0,'Complete parent natural zero required');out={n:v[n]for n in p['free']};need(_run(p['polynomial_source'],out)[p['output']]==0 and _pullback(p,out)==v,'Full natural zero bijection');return out

# Exact ring DAGs with coefficient cuts for only the tag chain and leaf sign.
def _formal(old,p):
 nodes={}
 def node(key):
  if key not in nodes:nodes[key]=len(nodes)
  return nodes[key]
 def literal(v):return node(('int',v))
 def op(o,a,b):
  if o in('+','*')and a>b:a,b=b,a
  return node((o,a,b))
 free={v:node(('var',v))for v in p['free']}
 def run(rows,base,cuts=None):
  e=dict(base)
  for n,o,a,b in rows:
   aa=e[a]if type(a)is str else literal(a);bb=e[b]if type(b)is str else literal(b);e[n]=op(o,aa,bb)
   if cuts and n in cuts:e[n]=cuts[n]
  return e
 after=run(p['source'],free);base=dict(free);cuts={};leaves={}
 for m in p['row_map']:
  # Expand the actual two local cones in independent remaining tags and
  # an opaque leaf-error E. This proves the cuts before using them below.
  i=m['row'];names=[f'r{i}_t{k}'for k in range(1,3 if i==p['N']-1 else 5)]
  def add(a,b,sign=1):
   out=dict(a)
   for mon,value in b.items():out[mon]=out.get(mon,0)+sign*value
   return {mon:value for mon,value in out.items()if value}
  def mul(a,b):
   out={}
   for ma,ca in a.items():
    for mb,cb in b.items():key=tuple(sorted(ma+mb));out[key]=out.get(key,0)+ca*cb
   return {mon:value for mon,value in out.items()if value}
  one={():1};sp={(name,):1 for name in names};parent_defs={n:(o,a,b)for n,o,a,b in old['source']};child_defs={n:(o,a,b)for n,o,a,b in p['source']};error=parent_defs[m['parent_leaf_residual']][2]
  def expand(name,definitions,known):
   if type(name)is int:return {():name}if name else{}
   if name in known:return known[name]
   o,a,b=definitions[name];aa=expand(a,definitions,known);bb=expand(b,definitions,known);value=mul(aa,bb)if o=='*'else add(aa,bb,1 if o=='+'else-1);known[name]=value;return value
  known={name:{(name,):1}for name in names};known[error]={('leaf_error',):1};parent_known=dict(known);parent_known[m['parent_tag']]=add(one,sp,-1)
  need(expand(m['parent_tag_residual'],parent_defs,parent_known)=={},'Actual affine tag cut')
  old_leaf=expand(m['parent_leaf_residual'],parent_defs,parent_known);new_leaf=expand(m['parent_leaf_residual'],child_defs,dict(known));need(add(old_leaf,new_leaf)=={},'Actual leaf sign coefficient identity')
  need(expand(m['guard'],child_defs,dict(known))==mul(sp,add(sp,one,-1)),'Actual unsquared integer guard polynomial')
  base[m['parent_tag']]=op('-',literal(1),after[m['tag_sum']]);cuts[m['parent_tag_residual']]=literal(0);cuts[m['parent_leaf_residual']]=node(('negative',after[m['parent_leaf_residual']]));leaves[m['parent_leaf_residual']]=after[m['parent_leaf_residual']]
 before=run(old['source'],base,cuts)
 for r in p['ordinary_residuals']:
  need(before[r]==(node(('negative',after[r]))if r in leaves else after[r]),'All retained residuals agree up to proved leaf sign')
 need(all(before[m['parent_tag_residual']]==literal(0)for m in p['row_map']),'All omitted parent tag residuals zero')
 # The independently checked finalizer recipes now give exactly the guard sum correction.
 return dict(retained_residual_identities=len(p['ordinary_residuals']),zero_tag_rows=p['N'],leaf_sign_identities=p['N'],whole_corrections=1)

def verify(root=None):
 parents=_parents(root);forms=[];rng=random.Random(208955);counts=dict(retained_residual_identities=0,zero_tag_rows=0,leaf_sign_identities=0,whole_corrections=0,exact_degrees=0,numeric_corrections=0,rational_corrections=0,genuine_bijections=0,offzero_negative_pullbacks=0)
 for N in range(1,9):
  for cleanup in(False,True):
   old=parents[N,cleanup];p=build(N,cleanup=cleanup,root=root);need(exact(rewrite(old,root=root),p),'Public canonical rewrite')
   for k,v in _formal(old,p).items():counts[k]+=v
   u=_coefficients(p['polynomial_source'],p['free'])[p['output']];need(len(u)-1==p['exact_degree']and u[-1]==p['degree_certificate']['diagonal_leading_coefficient']>0,'Exact full degree');counts['exact_degrees']+=1
   for case in range(8):
    v={n:rng.randint(-3,4)for n in p['free']}
    if case>=6:v={n:Fraction(x,5)for n,x in v.items()};counts['rational_corrections']+=1
    restored=_pullback(p,v);env=_run(p['polynomial_source'],v);correction=sum(env[n]for n in p['integer_guard_ports']);need(env[p['output']]==_run(old['polynomial_source'],restored)[old['output']]+correction,'Entire signed/rational correction');counts['numeric_corrections']+=1
    if case<6:need(integer_pullback(p,v,root=root)==restored and evaluate(p,v,signed=True,root=root)==env[p['output']],'Public signed algebra')
   one={n:1 for n in p['free']};rest=integer_pullback(p,one,root=root);need(any(v<0 for v in rest.values())and evaluate(p,one,root=root)>0,'No unrestricted natural inverse');counts['offzero_negative_pullbacks']+=1
   forms.append(dict(packet=p,parent_ledger=old['polynomial_ledger'],saving=dict(M=0,A=2*N-1,operations=2*N-1),degree_specialization=dict(all_supplied_ports='t',degree=len(u)-1,leading_coefficient=u[-1],coefficient_sha256=digest(u))))
 fixtures=[];tags=set()
 for x,y in[(0,3),(1,4),(2,5),(4,0),(8,0),(10,2),(10,1014),(12,0),(18,1),(20,2),(154,1)]:
  try:z,records=application(x,y)
  except ValueError:continue
  post=[];seen=set()
  def visit(key):
   if key in seen:return
   seen.add(key)
   for child in records[key]['children']:visit(child)
   post.append(key)
  visit((x,y));tags.add(records[x,y]['tag'])
  for pad in(0,1,2):
   keys=list(reversed(post))+[None]*pad;N=len(keys)
   if N>8:continue
   raw=flatten_records(records,keys,(x,y,z))
   for cleanup in(False,True):
    old=parents[N,cleanup];p=build(N,cleanup=cleanup,root=root);v={n:raw[n]for n in old['free']};child=project_parent_zero(p,v,root=root);need(restore_zero(p,child,root=root)==v and evaluate(p,child,root=root)==0,'Genuine full natural bijection');counts['genuine_bijections']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(tags==set(range(5)),'All five real evaluation rules')
 # Exact nonnegative-real failure of the integer nonnegativity argument.
 p=build(1,root=root);old=parents[1,True];v={n:Fraction(0)for n in p['free']};v.update(r0_x=Fraction(1),r0_t2=Fraction(1,2),program=Fraction(1));env=_run(p['polynomial_source'],v);before=_run(old['polynomial_source'],_pullback(p,v))[old['output']];need(env[p['output']]==0 and before==Fraction(1,4),'Actual rational real-domain counterexample')
 real_fixture=dict(values={n:str(x)for n,x in v.items()},child_output='0',restored_parent_output='1/4',scope='Nonnegative rational algebra only; rejected by the natural integer API')
 counts['guards']=0
 def reject(fn):
  try:fn()
  except(ValueError,KeyError,TypeError):counts['guards']+=1
  else:raise AssertionError('Malformed public call accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):reject(lambda N=N:build(N,root=root))
 for c in(0,1,None,'true'):reject(lambda c=c:build(1,cleanup=c,root=root))
 p=build(2,root=root);old=parents[2,True];zero={n:0 for n in p['free']}
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root))
 for key in('N','witnesses','squared_residual_count','unsquared_guard_count','nonnegative_term_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:checked(q,root=root))
 for key in('free','source','finalizer_terms','row_map','ordinary_residuals'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:checked(q,root=root))
 q=copy.deepcopy(p);q['finalizer_terms'][0]['kind']='square';reject(lambda:checked(q,root=root))
 q=copy.deepcopy(old);q['free'].reverse();reject(lambda:rewrite(q,root=root))
 for val in(True,0.0,Fraction(0),-1):
  vv=dict(zero,program=val);reject(lambda vv=vv:evaluate(p,vv,root=root));reject(lambda vv=vv:restore_zero(p,vv,root=root))
 for val in(True,0.0,Fraction(0)):reject(lambda val=val:integer_pullback(p,dict(zero,program=val),root=root))
 for vv in({},dict(zero,extra=0),list(zero)):reject(lambda vv=vv:integer_pullback(p,vv,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:evaluate(p,zero,signed=mode,root=root))
 reject(lambda:restore_zero(p,zero,root=root));reject(lambda:project_parent_zero(p,{n:0 for n in old['free']},root=root))
 counts['copies']=0
 for key,value in p.items():
  if type(value)not in(dict,list):continue
  q=build(2,root=root);q[key].clear();need(exact(build(2,root=root),p),'Mutable public field isolated');counts['copies']+=1
 accessor=polynomial_source(p,root=root);accessor.clear();need(exact(checked(p,root=root),p),'Source accessor isolation');counts['copies']+=1
 restored=integer_pullback(p,zero,root=root);restored['program']=9;need(zero['program']==0,'Pullback copy');counts['copies']+=1
 cp=canonical_parent(2,root=root);cp['parent_pins'].clear();need(exact(canonical_parent(2,root=root),old),'Parent deep copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='leaf_tag_pins_')as tmp:
  base=Path(__file__).resolve().parent if root is None else Path(root);blobs={n:(base/n).read_bytes()for n in PINS}
  for n,b in blobs.items():(Path(tmp)/n).write_bytes(b)
  build(2,root=tmp)
  for n,b in blobs.items():
   (Path(tmp)/n).write_bytes(b+b' ')
   for fn in(lambda:build(2,root=tmp),lambda:checked(p,root=tmp),lambda:integer_pullback(p,zero,root=tmp)):reject(fn)
   (Path(tmp)/n).write_bytes(b)
 counts['warm_pin_rejections']=9
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_LEAF_TAG_PROJECTION',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=copy.deepcopy(PINS),counts=counts,forms=forms,genuine_fixtures=fixtures,real_domain_counterexample=real_fixture,scope='Mixed finalizer of N unsquared nonnegative integer guards and7N residual squares. Natural zero bijection with terminal parent; integer graph correction, no unconditional natural inverse or real zero equivalence. External finiteN1..8, not fixed-arity universality.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts']);print([(f['packet']['N'],f['packet']['cleanup'],f['packet']['polynomial_ledger'])for f in out['forms']])
if __name__=='__main__':main()

"""Direct ordinary-input root aliases for all16 pinned finite eager Tree sources.

Mixed finalizer: N integer guards and7N-3 residual squares. Complete polynomial
restoration identity and natural zero bijection, with external sizeN1..8.
"""
import argparse,copy,hashlib,json,math,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_leaf_tag_projection.py':'e491a2dd852fca307d1c5f7138b078a0b815a0cea271ef05000cf001be1f6015','eager_tree_leaf_tag_projection.json':'1f786cd77987db5892ac40b4329f7bce1b6ad3ff26aa7cf15e0a25dde21114eb','eager_tree_leaf_tag_projection.md':'9f6e8d07accec6eb33ee402427e7fd795ff91487174fc47248653e855447ea8f'}

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
  raw=(root/name).read_bytes();need(hashlib.sha256(raw).hexdigest()==pin,'Parent pin '+name);blobs[name]=raw
 receipt=json.loads(blobs['eager_tree_leaf_tag_projection.json']);need(receipt['source_sha256']==PINS['eager_tree_leaf_tag_projection.py'],'Parent source lineage')
 forms={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in receipt['forms']};need(len(receipt['forms'])==16 and set(forms)=={(N,c)for N in range(1,9)for c in(False,True)},'Exact frozen parent family');return forms

def _rewrite(old):
 N=old['N'];aliases={'r0_x':'program','r0_y':'argument','r0_z':'output'};bindings=[]
 for field,port in aliases.items():
  need(old['free'].count(field)==old['free'].count(port)==1,'Exact root and ordinary input ports')
  matches=[r for r in old['source']if r[1:]==['-',field,port]];need(len(matches)==1,'Unique literal root-binding subtraction');name=matches[0][0]
  need([r[0]for r in old['source']if port in r[2:]]==[name],'Ordinary parent input has only its binding consumer')
  need(not any(name in r[2:]for r in old['source']),'Binding gate has no certificate consumer')
  need(old['ordinary_residuals'].count(name)==1,'One ordinary binding residual occurrence')
  indices=[j for j,t in enumerate(old['finalizer_terms'])if t['port']==name];need(len(indices)==1 and old['finalizer_terms'][indices[0]]['kind']=='square','One binding square in the mixed finalizer')
  bindings.append(dict(parent_field=field,ordinary_port=port,parent_residual=name,parent_term_index=indices[0]))
 deleted={b['parent_residual']for b in bindings};rows=[[n,o,aliases.get(a,a),aliases.get(b,b)]for n,o,a,b in old['source']if n not in deleted];free=[v for v in old['free']if v not in aliases]
 ordinary=[r for r in old['ordinary_residuals']if r not in deleted];guards=copy.deepcopy(old['integer_guard_ports']);terms=[copy.deepcopy(t)for t in old['finalizer_terms']if t['port']not in deleted];ports=[t['port']for t in terms]
 need(_live(rows,ports)==rows,'No hidden source pruning beyond the3 root rows')
 poly=copy.deepcopy(rows);accports=[]
 for i,t in enumerate(terms):
  need(t['kind']in('square','integer_nonnegative_guard'),'Exact mixed term kind')
  if t['kind']=='square':name=f'direct_root_square_{i}';poly.append([name,'*',t['port'],t['port']]);accports.append(name)
  else:accports.append(t['port'])
 out=accports[0]
 for i,port in enumerate(accports[1:],1):name=f'direct_root_sum_{i}';poly.append([name,'+',out,port]);out=name
 cert=_inspect(rows,free,ports);ledger=_inspect(poly,free,[out]);epsilon=int(old['cleanup']);degree=6 if N==1 else 10*N-8
 need((ledger['M'],ledger['A'],ledger['operations'])==((3*N*N+81*N-52)//2,(3*N*N+(127-2*epsilon)*N-88)//2,3*N*N+(104-epsilon)*N-70),'Complete paid schedule formula')
 need({k:old['polynomial_ledger'][k]-ledger[k]for k in('M','A','operations')}==dict(M=3,A=6,operations=9),'Exact9gate saving')
 need({k:old['certificate_ledger'][k]-cert[k]for k in('M','A','operations')}==dict(M=0,A=3,operations=3),'Exactly3 binding subtractions removed')
 need(len(free)-3==12*N-8 and len(ordinary)==7*N-3 and len(guards)==N and len(terms)==8*N-3,'Complete mixed interface counts')
 need(ledger['degree_upper_bound']==degree,'Preserved full degree upper bound')
 return dict(N=N,cleanup=old['cleanup'],free=free,source=rows,ordinary_residuals=ordinary,integer_guard_ports=guards,finalizer_terms=terms,polynomial_source=poly,output=out,certificate_ledger=cert,polynomial_ledger=ledger,witnesses=len(free)-3,squared_residual_count=len(ordinary),unsquared_guard_count=N,nonnegative_term_count=len(terms),exact_degree=degree,root_aliases=aliases,root_binding_map=bindings,parent_pins=copy.deepcopy(PINS),full_polynomial_graph_identity=True,graph_identity='Fchild=Fparent[r0_x=program,r0_y=argument,r0_z=output]',natural_zero_bijection=True,unconditional_natural_restoration=True,sos_finalizer=False,degree_certificate=dict(diagonal_leading_coefficient=old['degree_certificate']['diagonal_leading_coefficient'],reason='All-variable diagonal identifies each root field with its ordinary input already; removed binding squares vanish identically. Upper degree is unchanged.'),scope='Natural supplied fields including zero; ordinary program,argument,output remain inputs. Bijection only with the immediate pinned leaf-tag parent. Exact externalN1..8; no unbounded/fixed-arity universal or new decoder claim.')

def canonical_parent(N,*,cleanup=True,root=None):
 need(type(N)is int and 1<=N<=8 and type(cleanup)is bool,'Exact saved N/cleanup');return _parents(root)[N,cleanup]
def build(N,*,cleanup=True,root=None):return _rewrite(canonical_parent(N,cleanup=cleanup,root=root))
def rewrite(parent,*,root=None):
 need(type(parent)is dict,'Complete parent packet');old=canonical_parent(parent.get('N'),cleanup=parent.get('cleanup'),root=root);need(exact(parent,old),'Canonical full parent');return _rewrite(old)
def checked(packet,*,root=None):
 need(type(packet)is dict,'Complete child packet');p=build(packet.get('N'),cleanup=packet.get('cleanup'),root=root);need(exact(packet,p),'Canonical full child');return p
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);v=_assignment(p,values,signed);return _run(p['polynomial_source'],v)[p['output']]
def _restore(p,v):return dict(v,**{field:v[port]for field,port in p['root_aliases'].items()})
def restore_assignment(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);return _restore(p,_assignment(p,values,signed))
def project_parent_zero(packet,values,*,root=None):
 p=checked(packet,root=root);old=canonical_parent(p['N'],cleanup=p['cleanup'],root=root);v=_assignment(old,values,False);need(_run(old['polynomial_source'],v)[old['output']]==0,'Complete parent natural zero required')
 need(all(v[field]==v[port]for field,port in p['root_aliases'].items()),'Root bindings forced at parent zero');out={n:v[n]for n in p['free']};need(_restore(p,out)==v and _run(p['polynomial_source'],out)[p['output']]==0,'Full natural zero inverse');return out

def _formal(old,p):
 # Canonical structural expressions with exact zero/unit/constant rules.
 # No selected residual cut or equation is supplied to this evaluator.
 table={};integer_values={}
 def node(key):
  if key not in table:table[key]=len(table)
  return table[key]
 def integer(value):
  n=node(('int',value));integer_values[n]=value;return n
 zero,one=integer(0),integer(1)
 def op(o,a,b):
  if a in integer_values and b in integer_values:
   aa,bb=integer_values[a],integer_values[b];return integer(aa+bb if o=='+'else aa-bb if o=='-'else aa*bb)
  if o=='-'and a==b:return zero
  if o=='*':
   if a==zero or b==zero:return zero
   if a==one:return b
   if b==one:return a
  if o=='+'and a==zero:return b
  if o in('+','-')and b==zero:return a
  return node((o,a,b))
 base={v:node(('var',v))for v in p['free']}
 def run(rows,env):
  env=dict(env)
  for n,o,a,b in rows:env[n]=op(o,env[a]if type(a)is str else integer(a),env[b]if type(b)is str else integer(b))
  return env
 before=run(old['polynomial_source'],dict(base,**{field:base[port]for field,port in p['root_aliases'].items()}));after=run(p['polynomial_source'],base)
 need(before[old['output']]==after[p['output']],'Complete all-value graph identity without supplied cuts')
 need(all(before[r]==after[r]for r in p['ordinary_residuals']),'Every retained ordinary residual unchanged');need(all(before[r]==after[r]for r in p['integer_guard_ports']),'Every integer guard unchanged')
 need(all(before[b['parent_residual']]==zero for b in p['root_binding_map']),'All3 removed binding residuals identically zero')
 need(all(before[r[0]]==after[r[0]]for r in p['source']),'All retained certificate gates coincide')
 return dict(full_graph_identities=1,retained_certificate_gates=len(p['source']),retained_residual_identities=len(p['ordinary_residuals']),retained_guard_identities=len(p['integer_guard_ports']),removed_zero_bindings=3)

def verify(root=None):
 olds=_parents(root);forms=[];rng=random.Random(946036);counts=dict(full_graph_identities=0,retained_certificate_gates=0,retained_residual_identities=0,retained_guard_identities=0,removed_zero_bindings=0,exact_degrees=0,full_numeric_identities=0,rational_identities=0,unconditional_natural_maps=0,genuine_bijections=0)
 for N in range(1,9):
  for cleanup in(False,True):
   old=olds[N,cleanup];p=build(N,cleanup=cleanup,root=root);need(exact(rewrite(old,root=root),p),'Public full canonical rewrite')
   for k,v in _formal(old,p).items():counts[k]+=v
   coeff=_coefficients(p['polynomial_source'],p['free'])[p['output']];before=_coefficients(old['polynomial_source'],old['free'])[old['output']]
   need(coeff==before,'Complete diagonal coefficient polynomial unchanged');need(len(coeff)-1==p['exact_degree']and coeff[-1]==p['degree_certificate']['diagonal_leading_coefficient']>0,'Exact complete degree');counts['exact_degrees']+=1
   for case in range(8):
    v={n:rng.randint(-3,4)if case<5 else rng.randint(0,4)for n in p['free']}
    if case in(3,4):v={n:Fraction(x,7)for n,x in v.items()};counts['rational_identities']+=1
    restored=_restore(p,v);value=_run(p['polynomial_source'],v)[p['output']];need(_run(old['polynomial_source'],restored)[old['output']]==value,'Entire signed/rational graph identity');counts['full_numeric_identities']+=1
    if case not in(3,4):need(restore_assignment(p,v,signed=case<5,root=root)==restored and evaluate(p,v,signed=case<5,root=root)==value,'Public integer maps and values')
    if case>=5:need(all(x>=0 for x in restored.values()),'Unconditional natural restoration');counts['unconditional_natural_maps']+=1
   forms.append(dict(packet=p,parent_ledger=old['polynomial_ledger'],parent_certificate_ledger=old['certificate_ledger'],complete_saving=dict(M=3,A=6,operations=9),degree_specialization=dict(all_supplied_ports='t',degree=len(coeff)-1,leading_coefficient=coeff[-1],coefficient_sha256=digest(coeff))))
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
    p=build(N,cleanup=cleanup,root=root);old=olds[N,cleanup];v={n:raw[n]for n in old['free']};child=project_parent_zero(p,v,root=root);need(restore_assignment(p,child,root=root)==v and evaluate(p,child,root=root)==0,'Genuine complete natural bijection');counts['genuine_bijections']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(tags==set(range(5)),'All five evaluation rules')
 # The parent real-witness limitation survives this exact input alias.
 p=build(1,root=root);old=olds[1,True];v={n:Fraction(0)for n in p['free']};v.update(program=Fraction(1),r0_t2=Fraction(1,2));value=_run(p['polynomial_source'],v)[p['output']];need(value==0 and _run(old['polynomial_source'],_restore(p,v))[old['output']]==0,'Inherited nonnegative rational zero preserved')
 rational_boundary=dict(values={n:str(x)for n,x in v.items()},child_and_parent_output='0',scope='Inherited rational-witness false evaluation program1,argument0,output0; public integer APIs reject it.')
 counts['guards']=0
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Malformed call accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):reject(lambda N=N:build(N,root=root))
 for c in(0,1,None,'true'):reject(lambda c=c:build(1,cleanup=c,root=root))
 p=build(2,root=root);old=olds[2,True];v={n:0 for n in p['free']}
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root))
 for key in('N','witnesses','squared_residual_count','unsquared_guard_count','nonnegative_term_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:checked(q,root=root))
 for key in('free','source','finalizer_terms','root_binding_map','ordinary_residuals'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:checked(q,root=root))
 q=copy.deepcopy(p);q['root_aliases']['r0_x']='argument';reject(lambda:checked(q,root=root))
 q=copy.deepcopy(p);q['finalizer_terms'][0]['kind']='square';reject(lambda:checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:checked(q,root=root))
 q=copy.deepcopy(old);q['free'].reverse();reject(lambda:rewrite(q,root=root))
 for val in(True,0.0,Fraction(0),-1):
  vv=dict(v,program=val)
  for fn in(evaluate,restore_assignment):reject(lambda fn=fn,vv=vv:fn(p,vv,root=root))
 for vv in({},dict(v,extra=0),list(v)):
  for fn in(evaluate,restore_assignment):reject(lambda fn=fn,vv=vv:fn(p,vv,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:restore_assignment(p,v,signed=mode,root=root))
 reject(lambda:project_parent_zero(p,{n:0 for n in old['free']},root=root))
 counts['copies']=0
 for key,value in p.items():
  if type(value)not in(dict,list):continue
  q=build(2,root=root);q[key].clear();need(exact(build(2,root=root),p),'All mutable packet fields isolated');counts['copies']+=1
 src=polynomial_source(p,root=root);src.clear();need(exact(checked(p,root=root),p),'Source accessor copied');counts['copies']+=1
 restored=restore_assignment(p,v,root=root);restored['program']=8;need(v['program']==0,'Restoration copied');counts['copies']+=1
 cp=canonical_parent(2,root=root);cp['parent_pins'].clear();need(exact(canonical_parent(2,root=root),old),'Parent accessor copied');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='direct_root_pins_')as tmp:
  base=Path(__file__).resolve().parent if root is None else Path(root);blobs={n:(base/n).read_bytes()for n in PINS}
  for n,b in blobs.items():(Path(tmp)/n).write_bytes(b)
  build(2,root=tmp)
  for n,b in blobs.items():
   (Path(tmp)/n).write_bytes(b+b' ')
   for fn in(lambda:build(2,root=tmp),lambda:checked(p,root=tmp),lambda:restore_assignment(p,v,root=tmp)):reject(fn)
   (Path(tmp)/n).write_bytes(b)
 counts['warm_pin_rejections']=9
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_DIRECT_ROOT_PROJECTION',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=copy.deepcopy(PINS),counts=counts,forms=forms,genuine_fixtures=fixtures,inherited_rational_boundary=rational_boundary,scope='Complete graph identity and unconditional natural restoration of3 root fields. Full natural-zero bijection with immediate leaf-tag parent; N guards plus7N-3 residual squares. External finiteN1..8, not fixed-arity universality.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts']);print([(f['packet']['N'],f['packet']['cleanup'],f['packet']['polynomial_ledger'])for f in out['forms']])
if __name__=='__main__':main()

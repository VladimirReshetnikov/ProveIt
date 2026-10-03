"""Maintained finite Tree terminal-row projection of the pinned product source.

Saved external sizes1..8. Exact polynomial graph identity and natural
existential projection; zero-fiber bijection only on the normalized c=0 slice.
"""
import argparse,copy,hashlib,json,math,random,subprocess,sys,tempfile
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_pointer_product_scout.py':'35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd','eager_tree_pointer_product_scout.json':'9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc','eager_tree_pointer_product_scout.md':'c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3'}
def need(v,msg):
 if not v:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def _parents(root):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Parent pin '+name);blobs[name]=b
 receipt=json.loads(blobs['eager_tree_pointer_product_scout.json']);forms={}
 need(receipt['source_sha256']==PINS['eager_tree_pointer_product_scout.py'],'Parent source receipt link')
 for f in receipt['forms']:
  p=f['packet'];forms[p['N'],p['cleanup']]=p
 need(set(forms)=={(N,c)for N in range(1,9)for c in(False,True)},'Exact saved parent family');return forms

def _fold(op,a,b):
 if type(a)is int and type(b)is int:return a+b if op=='+'else a-b if op=='-'else a*b
 if op=='*':
  if a==0 or b==0:return 0
  if a==1:return b
  if b==1:return a
 if op=='+'and a==0:return b
 if op in('+','-')and b==0:return a
 return None
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
def _finalizer(rows,residuals):
 out=copy.deepcopy(rows)
 for i,r in enumerate(residuals):out.append([f'terminal_square_{i}','*',r,r])
 name='terminal_square_0'
 for i in range(1,len(residuals)):
  n=f'terminal_sum_{i}';out.append([n,'+',name,f'terminal_square_{i}']);name=n
 return out,name

def _rewrite(old):
 N=old['N'];last=N-1;fixed={f'r{last}_{f}':0 for f in('t3','t4','c')};aliases=dict(fixed);changed=set(fixed);rows=[];identities=[]
 for n,o,a,b in old['source']:
  aa,bb=aliases.get(a,a),aliases.get(b,b);affected=a in changed or b in changed;value=_fold(o,aa,bb)if affected else None
  if value is not None:aliases[n]=value;changed.add(n);identities.append([n,o,aa,bb,value])
  else:
   rows.append([n,o,aa,bb])
   if affected:changed.add(n)
 need([m['row']for m in old['slot_map'][-3:]]==[last]*3,'Three terminal slots')
 need(old['residuals'][-3:]==[m['child_port']for m in old['slot_map'][-3:]],'Literal last residual occurrences')
 need(all(aliases.get(r,r)==0 for r in old['residuals'][-3:]),'Three restored zero residuals')
 res=[aliases.get(r,r)for r in old['residuals'][:-3]];rows=_live(rows,res);free=[v for v in old['free']if v not in fixed];poly,out=_finalizer(rows,res);cert=_inspect(rows,free,res);ledger=_inspect(poly,free,[out]);cleanup=int(old['cleanup'])
 need((ledger['M'],ledger['A'],ledger['operations'])==((3*N*N+81*N-46)//2,(3*N*N+(131-2*cleanup)*N-78)//2,3*N*N+(106-cleanup)*N-62),'Full paid formula')
 need({k:old['polynomial_ledger'][k]-ledger[k]for k in('M','A','operations')}==dict(M=11,A=20,operations=31),'Complete31gate saving')
 need({k:old['certificate_ledger'][k]-cert[k]for k in('M','A','operations')}==dict(M=8,A=17,operations=25),'Certificate25gate saving')
 degree=6 if N==1 else 10*N-8
 need(len(free)-3==13*N-5 and len(res)==8*N and ledger['degree_upper_bound']==degree,'Interface/degree upper')
 return dict(N=N,cleanup=old['cleanup'],free=free,source=rows,residuals=res,polynomial_source=poly,output=out,certificate_ledger=cert,polynomial_ledger=ledger,witnesses=len(free)-3,residual_count=len(res),exact_degree=degree,fixed_parent_coordinates=fixed,removed_parent_residual_indices=list(range(len(old['residuals'])-3,len(old['residuals']))),residual_map=[dict(parent_index=i,parent_port=r,child_port=res[i])for i,r in enumerate(old['residuals'][:-3])],local_constant_identities=identities,parent_pins=copy.deepcopy(PINS),full_polynomial_graph_identity=True,natural_existential_projection=True,full_parent_zero_bijection=False,normalized_parent_slice=f'r{last}_c=0 (terminalt3=t4=0 already follows at every parent natural zero)',domains='All supplied coordinates natural including zero; signed evaluation/restoration is integer algebra only. Exact external N in saved range1..8.',degree_certificate=dict(uniform_leader='t2^2*b^4+t1^2*(a+y)^4'if N==1 else'Root third product residual has leader(-1)^(N-1)*t[0,3]^N*(u0+v0)^(4(N-1)); its square attains10N-8',diagonal_leading_coefficient=17 if N==1 else 8*2**(10*(N-1))+2**(8*(N-1))),scope='Exact all-value graph identity after restoring terminal tags and c as0. Natural existential projection, with bijection only to the normalized terminalc0 parent slice. No bijection with all parent zeros, fixed-arity universal bound or new input decoder.')

def canonical_parent(N,*,cleanup=True,root=None):
 need(type(N)is int and 1<=N<=8 and type(cleanup)is bool,'Exact saved N/cleanup');return _parents(root)[N,cleanup]
def build(N,*,cleanup=True,root=None):return _rewrite(canonical_parent(N,cleanup=cleanup,root=root))
def rewrite(parent,*,root=None):
 need(type(parent)is dict,'Complete parent packet');old=canonical_parent(parent.get('N'),cleanup=parent.get('cleanup'),root=root);need(exact(parent,old),'Canonical full parent');return _rewrite(old)
def checked(packet,*,root=None):
 need(type(packet)is dict,'Complete child packet');q=build(packet.get('N'),cleanup=packet.get('cleanup'),root=root);need(exact(packet,q),'Canonical full child');return q
def polynomial_source(packet,*,root=None):return checked(packet,root=root)['polynomial_source']
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
def evaluate(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);v=_assignment(p,values,signed);return _run(p['polynomial_source'],v)[p['output']]
def restore_assignment(packet,values,*,signed=False,root=None):
 p=checked(packet,root=root);return dict(_assignment(p,values,signed),**p['fixed_parent_coordinates'])
def project_parent_zero(packet,values,*,root=None):
 p=checked(packet,root=root);old=canonical_parent(p['N'],cleanup=p['cleanup'],root=root);v=_assignment(old,values,False)
 need(_run(old['polynomial_source'],v)[old['output']]==0,'Parent natural zero required');last=p['N']-1;need(v[f'r{last}_t3']==v[f'r{last}_t4']==0,'Forced terminal tags')
 out={n:v[n]for n in p['free']};need(_run(p['polynomial_source'],out)[p['output']]==0,'Complete projected natural zero');return out

# Structural ring expressions with only exact constant/zero/unit folding.
def _expressions(rows,free,fixed=None):
 e={v:('var',v)for v in free};e.update({n:('int',v)for n,v in(fixed or{}).items()})
 def op(o,a,b):
  aa=a[1]if a[0]=='int'else a;bb=b[1]if b[0]=='int'else b;r=_fold(o,aa,bb)
  if r is not None:return ('int',r)if type(r)is int else r
  return(o,a,b)
 for n,o,a,b in rows:e[n]=op(o,e[a]if type(a)is str else('int',a),e[b]if type(b)is str else('int',b))
 return e

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


def verify(root=None):
 olds=_parents(root);forms=[];rng=random.Random(310316);counts=dict(full_graph_identities=0,retained_residual_identities=0,restored_zero_occurrences=0,arbitrary_c_graph_identities=0,exact_degrees=0,full_evaluations=0,rational_evaluations=0,unconditional_natural_maps=0,genuine_projections=0,normalized_zero_bijections=0,arbitrary_c_nonunique_examples=0)
 for N in range(1,9):
  for cleanup in(False,True):
   old=olds[N,cleanup];p=build(N,cleanup=cleanup,root=root);need(exact(rewrite(old,root=root),p),'Canonical public rewrite')
   before=_expressions(old['polynomial_source'],old['free'],p['fixed_parent_coordinates']);after=_expressions(p['polynomial_source'],p['free']);need(before[old['output']]==after[p['output']],'Complete all-value polynomial graph identity');counts['full_graph_identities']+=1
   for item in p['residual_map']:need(before[item['parent_port']]==after[item['child_port']],'Every retained residual identity');counts['retained_residual_identities']+=1
   for i in p['removed_parent_residual_indices']:need(before[old['residuals'][i]]==('int',0),'Restored zero residual occurrence');counts['restored_zero_occurrences']+=1
   tags={f'r{N-1}_t3':0,f'r{N-1}_t4':0};arbitrary=_expressions(old['polynomial_source'],old['free'],tags);need(arbitrary[old['output']]==after[p['output']],'Entire polynomial independent of arbitrary c after onlytag restoration');counts['arbitrary_c_graph_identities']+=1
   uni=_coefficients(p['polynomial_source'],p['free'])[p['output']];need(len(uni)-1==p['exact_degree']and uni[-1]==p['degree_certificate']['diagonal_leading_coefficient']>0,'Exact full coefficient degree certificate');counts['exact_degrees']+=1
   for case in range(6):
    v={n:rng.randint(-2,3)if case<3 else rng.randint(0,3)for n in p['free']}
    if case==2:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_evaluations']+=1
    restored=dict(v,**p['fixed_parent_coordinates']);value=_run(p['polynomial_source'],v)[p['output']]
    need(_run(old['polynomial_source'],restored)[old['output']]==value,'Full signed/rational graph identity');counts['full_evaluations']+=1
    if case!=2:need(evaluate(p,v,signed=case<3,root=root)==value and restore_assignment(p,v,signed=case<3,root=root)==restored,'Public integer source/maps')
    if case>=3:need(all(x>=0 for x in restored.values()),'Unconditional natural restoration');counts['unconditional_natural_maps']+=1
   forms.append(dict(packet=p,parent_ledger=old['polynomial_ledger'],parent_certificate_ledger=old['certificate_ledger'],complete_saving=dict(M=11,A=20,operations=31),degree_specialization=dict(all_supplied_ports='t',degree=len(uni)-1,leading_coefficient=uni[-1],coefficient_sha256=digest(uni))))
 fixtures=[];tags=set();examples=[]
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
    old=olds[N,cleanup];p=build(N,cleanup=cleanup,root=root);v={n:raw[n]for n in old['free']};nv=project_parent_zero(p,v,root=root);need(evaluate(p,nv,root=root)==0,'Actual child zero');counts['genuine_projections']+=1
    restored=restore_assignment(p,nv,root=root);need(restored==v and project_parent_zero(p,restored,root=root)==nv,'Exact normalized-slice zero inverse');counts['normalized_zero_bijections']+=1
    altered=dict(v);altered[f'r{N-1}_c']=7;need(altered!=restored and _run(old['polynomial_source'],altered)[old['output']]==0 and project_parent_zero(p,altered,root=root)==nv,'Full parent nonunique c fiber');counts['arbitrary_c_nonunique_examples']+=1
    if N==1 and cleanup and x==0 and pad==0:examples.append(dict(parent_zero_c0=v,parent_zero_c7=altered,child_zero=nv))
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(tags==set(range(5))and len(examples)==1,'All five rules and explicit c ambiguity example')
 counts['guards']=0
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Malformed call accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):reject(lambda N=N:build(N,root=root))
 for c in(0,1,None,'true'):reject(lambda c=c:build(1,cleanup=c,root=root))
 p=build(2,root=root);old=canonical_parent(2,root=root);v={n:0 for n in p['free']}
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root))
 for key in('N','exact_degree','witnesses','residual_count'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:checked(q,root=root))
 for key in('source','free','residuals','residual_map'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:checked(q,root=root))
 q=copy.deepcopy(old);q['free'].reverse();reject(lambda:rewrite(q,root=root))
 for value in(True,0.0,-1,Fraction(0)):
  bad=dict(v,program=value)
  for fn in(evaluate,restore_assignment):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for bad in({},dict(v,extra=0),list(v)):
  reject(lambda bad=bad:evaluate(p,bad,root=root))
 for mode in(None,0,1):reject(lambda mode=mode:restore_assignment(p,v,signed=mode,root=root))
 reject(lambda:project_parent_zero(p,{n:0 for n in old['free']},root=root))
 counts['copies']=0
 for key,value in p.items():
  if type(value)not in(dict,list):continue
  q=build(2,root=root);q[key].clear();need(exact(build(2,root=root),p),'Every mutable packet field isolated');counts['copies']+=1
 restored=restore_assignment(p,v,root=root);restored['program']=99;need(v['program']==0,'Map defensive assignment copy');counts['copies']+=1
 raw=polynomial_source(p,root=root);raw.clear();need(exact(checked(p,root=root),p),'Source accessor copy');counts['copies']+=1
 cp=canonical_parent(2,root=root);cp['parent_pins'].clear();need(exact(canonical_parent(2,root=root),old),'Parent accessor deep copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='terminal_projection_pins_')as tmp:
  base=Path(__file__).resolve().parent if root is None else Path(root);blobs={n:(base/n).read_bytes()for n in PINS}
  for n,b in blobs.items():(Path(tmp)/n).write_bytes(b)
  build(2,root=tmp)
  for n,b in blobs.items():
   (Path(tmp)/n).write_bytes(b+b' ')
   for fn in(lambda:build(2,root=tmp),lambda:checked(p,root=tmp),lambda:restore_assignment(p,v,root=tmp)):reject(fn)
   (Path(tmp)/n).write_bytes(b)
 counts['warm_pin_rejections']=9
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_TERMINAL_PROJECTION',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=copy.deepcopy(PINS),counts=counts,forms=forms,genuine_fixtures=fixtures,arbitrary_c_nonunique_examples=examples,scope='Exact complete polynomial graph identity on terminaltag/c0 restoration and natural existential projection. Bijection only to normalized terminalc0 parent slice; no full-parent-fiber bijection or fixed-arity universality.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts']);print([(f['packet']['N'],f['packet']['cleanup'],f['packet']['polynomial_ledger'])for f in out['forms']])
if __name__=='__main__':main()

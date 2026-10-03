"""Finite pointer-free Tree scout using an active product of code differences."""
import argparse,copy,hashlib,json,math,random,sys,tempfile,subprocess
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_coded_lookup_scout.py':'b2769ca2c8b8754f5b5c9d65c0ad97a5f590c5b6ebc5712a2964ac1d1a1d0e73','eager_tree_coded_lookup_scout.json':'acfcbd04609e49150a0e9089c7937ca0fcd20b852a337a3e39248a4e582d01c6','eager_tree_coded_lookup_scout.md':'81d9be0663b212039802c1c841dd200e82baedc02ecf1005957e8f90beef457b'}
def need(q,s):
 if not q:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def parents(root=None):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  b=(root/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'Parent bytes '+name);blobs[name]=b
 saved=json.loads(blobs['eager_tree_coded_lookup_scout.json']);out={}
 for p in saved['selected_full_packets']:
  if p['mode']=='gated'and p['algebra']and p['order']==[2,0,1]:out[p['N'],p['cleanup']]=p
 need(set(out)=={(n,c)for n in range(1,9)for c in(False,True)},'Saved degree10 paid-pair family');return out

def live_rows(rows,ports):
 live={n for n in ports if type(n)is str}
 for n,o,a,b in reversed(rows):
  if n in live:live.update(x for x in(a,b)if type(x)is str)
 return [r for r in rows if r[0]in live]
def inspect(rows,free,ports):
 degree={x:1 for x in free};deps={};M=0
 for n,o,a,b in rows:
  need(type(n)is str and n not in degree and o in('+','-','*'),'Fresh gate')
  need(all(type(x)is int or type(x)is str and x in degree for x in(a,b)),'Closed exact source')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0;degree[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);M+=o=='*'
 live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'All gates and supplied fields live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),degree_upper_bound=max(degree[n]for n in ports),all_live=True)
def finalizer(rows,residuals):
 out=copy.deepcopy(rows)
 for i,r in enumerate(residuals):out.append([f'product_square_{i}','*',r,r])
 last='product_square_0'
 for i in range(1,len(residuals)):
  name=f'product_sum_{i}';out.append([name,'+',last,f'product_square_{i}']);last=name
 return out,last

def _build(old):
 N=old['N'];defs={r[0]:r for r in old['source']};row_sum_indices=[8*i+j for i in range(N)for j in(5,6,7)];lookup_indices=list(range(8*N+3,11*N+3));deleted=row_sum_indices+lookup_indices;common=[r for i,r in enumerate(old['residuals'])if i not in deleted];need(len(common)==5*N+3,'All unchanged local/root residuals')
 active=[]
 for i in range(N):
  regs=[]
  for j in(5,6,7):
   row=defs[old['residuals'][8*i+j]];need(row[1]=='-','Literal parent pointer row-sum residual');regs.append(row[3])
  need(regs[0]==regs[1]and regs[2]==f'r{i}_t3'and defs[regs[0]][1:]==['+',f'r{i}_t3',f'r{i}_t4'],'Literal active/t3 ports');active.append(regs)
 seeds=common+[r for rs in active for r in rs]+[m['target_port']for m in old['lookup_map']if m['row']<N-1]+list(old['row_code_ports'].values())
 rows=copy.deepcopy(live_rows(old['source'],seeds));new=[];maps=[];number=0
 def emit(op,a,b):
  nonlocal number
  name=f'pointer_product_{number}';number+=1;rows.append([name,op,a,b]);return name
 for m in old['lookup_map']:
  i,s=m['row'],m['slot'];differences=[emit('-',old['row_code_ports'][str(j)],m['target_port'])for j in range(i+1,N)]
  if differences:
   prod=differences[0]
   for d in differences[1:]:prod=emit('*',prod,d)
   r=emit('*',active[i][s],prod)
  else:r=active[i][s]
  new.append(r);maps.append(dict(row=i,slot=s,parent_lookup_port=m['child_port'],child_port=r,active_port=active[i][s],target_port=m['target_port']if differences else None,difference_ports=differences))
 res=common+new;rows=live_rows(rows,res);removed_pointers=[f'r{i}_p{s}_{j}'for i in range(N)for s in range(3)for j in range(i+1,N)];removed_vacuous=[f'r{N-1}_u',f'r{N-1}_v'];free=[n for n in old['free']if n not in set(removed_pointers+removed_vacuous)];poly,out=finalizer(rows,res);ledger=inspect(poly,free,[out]);cleanup=int(old['cleanup'])
 need((ledger['M'],ledger['A'],ledger['operations'])==((3*N*N+81*N-24)//2,(3*N*N+(131-2*cleanup)*N-38)//2,3*N*N+(106-cleanup)*N-31),'Complete paid general formula')
 need(len(free)-3==13*N-2 and len(res)==8*N+3,'Actual supplied interface')
 need(ledger['degree_upper_bound']==max(10,10*N-8),'Actual complete degree upper')
 return dict(N=N,cleanup=old['cleanup'],free=free,source=rows,residuals=res,polynomial_source=poly,output=out,certificate_ledger=inspect(rows,free,res),polynomial_ledger=ledger,witnesses=len(free)-3,residual_count=len(res),exact_degree=max(10,10*N-8),parent_pins=copy.deepcopy(PINS),retained_parent_residual_indices=[i for i in range(len(old['residuals']))if i not in deleted],removed_parent_residual_indices=sorted(deleted),removed_pointer_coordinates=removed_pointers,removed_vacuous_coordinates=removed_vacuous,slot_map=maps,full_polynomial_identity=False,natural_existential_projection=True,zero_fiber_bijection=False,scope='External saved N1..8. Same represented natural triples and exact existential projection over retained coordinates. One chosen pointer restoration; multiple matching rows and deleted unused lastu/v prevent a zero-fiber bijection. No fixed-arity universal bound.')
def build(N,*,cleanup=True,root=None):
 need(type(N)is int and 1<=N<=8 and type(cleanup)is bool,'Exact saved N/cleanup');return _build(parents(root)[N,cleanup])
def checked(p,*,root=None):
 need(type(p)is dict,'Complete packet');q=build(p.get('N'),cleanup=p.get('cleanup'),root=root);need(exact(p,q),'Canonical packet');return q
def run(rows,values):
 env=dict(values)
 for n,o,a,b in rows:
  a=env[a]if type(a)is str else a;b=env[b]if type(b)is str else b;env[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return env

def assignment(p,v):
 need(type(v)is dict and set(v)==set(p['free'])and all(type(n)is str and type(x)is int and x>=0 for n,x in v.items()),'Exact full natural assignment');return dict(v)
def restore_zero(p,v,*,root=None):
 p=checked(p,root=root);v=assignment(p,v);need(run(p['polynomial_source'],v)[p['output']]==0,'Child natural zero required');old=parents(root)[p['N'],p['cleanup']];out=dict(v);out.update({n:0 for n in p['removed_pointer_coordinates']+p['removed_vacuous_coordinates']});env=run(old['source'],out)
 for m in old['lookup_map']:
  i,s=m['row'],m['slot'];active=out[f'r{i}_t3']+(out[f'r{i}_t4']if s<2 else 0)
  if active:
   choices=[j for j in range(i+1,p['N'])if env[old['row_code_ports'][str(j)]]==env[m['target_port']]];need(choices,'Natural product guarantees matching later row');out[f'r{i}_p{s}_{choices[0]}']=1
 need(run(old['polynomial_source'],out)[old['output']]==0,'Complete natural parent lift');return out
def project_zero(p,v,*,root=None):
 p=checked(p,root=root);old=parents(root)[p['N'],p['cleanup']];v=assignment(old,v);need(run(old['polynomial_source'],v)[old['output']]==0,'Parent natural zero required');out={n:v[n]for n in p['free']};need(run(p['polynomial_source'],out)[p['output']]==0,'Complete natural projection');return out

# Exact univariate specialization, with all remaining variables equal to t.
def coefficients(rows,free):
 env={n:[0,1]for n in free}
 for n,o,a,b in rows:
  a=env[a]if type(a)is str else[a];b=env[b]if type(b)is str else[b]
  out=[0]*(len(a)+len(b)-1 if o=='*'else max(len(a),len(b)))
  if o=='*':
   for i,x in enumerate(a):
    for j,y in enumerate(b):out[i+j]+=x*y
  else:
   for i,x in enumerate(a):out[i]+=x
   for i,x in enumerate(b):out[i]+=x if o=='+'else-x
  while len(out)>1 and out[-1]==0:out.pop()
  env[n]=out
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


def verify(root):
 oldforms=parents(root);forms=[];rng=random.Random(271113);counts=dict(complete_sources=0,retained_literal_gates=0,whole_corrections=0,rational_corrections=0,degree_certificates=0,genuine_projections=0,genuine_lifts=0,nonunique_parent_fixtures=0)
 for N in range(1,9):
  for cleanup in(False,True):
   old=oldforms[N,cleanup];p=_build(old);olddefs={r[0]:r for r in old['source']};common=[old['residuals'][i]for i in p['retained_parent_residual_indices']]
   copied=[r for r in p['source']if r[0]in olddefs];need(all(r==olddefs[r[0]]for r in copied),'Literal retained DAG');counts['retained_literal_gates']+=len(copied)
   need(p['residuals'][:len(common)]==common,'Full common residual interface')
   uni=coefficients(p['polynomial_source'],p['free'])[p['output']];need(len(uni)-1==p['exact_degree']and uni[-1]>0,'Exact full source degree attained');counts['degree_certificates']+=1
   for case in range(6):
    v={n:rng.randint(-2,3)for n in old['free']}
    if case>=4:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_corrections']+=1
    nv={n:v[n]for n in p['free']};before=run(old['polynomial_source'],v);after=run(p['polynomial_source'],nv)
    correction=sum(after[m['child_port']]**2 for m in p['slot_map'])-sum(before[old['residuals'][i]]**2 for i in p['removed_parent_residual_indices'])
    need(after[p['output']]-before[old['output']]==correction,'All-value whole source correction with arbitrary old pointers/lastu/v');counts['whole_corrections']+=1
   forms.append(dict(packet=p,parent_ledger=old['polynomial_ledger'],degree_specialization=dict(variable='Every remaining supplied port equals t',degree=len(uni)-1,leading_coefficient=uni[-1],coefficient_sha256=digest(uni))));counts['complete_sources']+=1
 fixtures=[];covered=set()
 for x,y in[(0,3),(1,4),(2,5),(4,0),(8,0),(10,2),(10,1014),(12,0),(18,1),(20,2),(154,1)]:
  try:z,records=application(x,y)
  except ValueError:continue
  post=[];seen=set()
  def visit(key):
   if key in seen:return
   seen.add(key)
   for child in records[key]['children']:visit(child)
   post.append(key)
  visit((x,y));covered.add(records[x,y]['tag'])
  for pad in(0,1,2):
   keys=list(reversed(post))+[None]*pad;N=len(keys)
   if N>8:continue
   raw=flatten_records(records,keys,(x,y,z))
   for cleanup in(False,True):
    old=oldforms[N,cleanup];p=build(N,cleanup=cleanup,root=root);v={n:raw[n]for n in old['free']};nv=project_zero(p,v,root=root);counts['genuine_projections']+=1
    lifted=restore_zero(p,nv,root=root);need(project_zero(p,lifted,root=root)==nv,'Chosen lift is a right inverse of projection');counts['genuine_lifts']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(covered==set(range(5)),'All five rules exercised')
 # Root10 applied0 has a leaf premise. Duplicating that leaf
 # gives two actual parent zeros with identical retained row fields.
 z,rec=application(10,0);post=[];seen=set()
 def visit(key):
  if key in seen:return
  seen.add(key)
  for child in rec[key]['children']:visit(child)
  post.append(key)
 visit((10,0));keys=list(reversed(post));N=len(keys)+1;raw=flatten_records(rec,keys+[None],(10,0,z));original=keys.index((0,0));last=N-1
 for field in['x','y','z','a','b','c','u','v']+[f't{i}'for i in range(5)]:raw[f'r{last}_{field}']=raw[f'r{original}_{field}']
 old=oldforms[N,True];p=build(N,root=root);v={n:raw[n]for n in old['free']};need(run(old['polynomial_source'],v)[old['output']]==0,'First duplicated-leaf parent zero');w=dict(v);slot=next(s for s in range(3)if v[f'r0_p{s}_{original}']==1);w[f'r0_p{slot}_{original}']=0;w[f'r0_p{slot}_{last}']=1;need(run(old['polynomial_source'],w)[old['output']]==0 and v!=w,'Second parent pointer zero');nv=project_zero(p,v,root=root);need(project_zero(p,w,root=root)==nv,'Same retained child tuple');counts['nonunique_parent_fixtures']+=1
 nonunique=dict(N=N,input=[10,0],output=z,first_parent=v,second_parent=w,child=nv,chosen_lift=restore_zero(p,nv,root=root))
 # Last unused coordinates are independently nonunique; tags3/4 are0.
 w=dict(v);w[f'r{last}_u']=7;w[f'r{last}_v']=11;need(run(old['polynomial_source'],w)[old['output']]==0 and project_zero(p,w,root=root)==nv,'Separate unused-coordinate nonuniqueness');counts['nonunique_parent_fixtures']+=1
 counts['guards']=0
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Bad call accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):reject(lambda N=N:build(N,root=root))
 for c in(0,1,None,'true'):reject(lambda c=c:build(1,cleanup=c,root=root))
 p=build(2,root=root)
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root))
 reject(lambda:restore_zero(p,{n:0 for n in p['free']},root=root));reject(lambda:project_zero(p,{n:0 for n in oldforms[2,True]['free']},root=root))
 for value in(True,1.0,-1,Fraction(1)):
  v={n:0 for n in p['free']};v['program']=value;reject(lambda v=v:restore_zero(p,v,root=root))
 counts['copies']=0
 for key in('source','polynomial_source','free','slot_map','parent_pins'):
  q=build(2,root=root);q[key].clear();need(exact(build(2,root=root),p),'Fresh defensive copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='tree_pointer_pins_')as tmp:
  data={n:(Path(root)/n).read_bytes()for n in PINS}
  for n,b in data.items():(Path(tmp)/n).write_bytes(b)
  build(2,root=tmp)
  for n,b in data.items():
   (Path(tmp)/n).write_bytes(b+b' ');reject(lambda:build(2,root=tmp));(Path(tmp)/n).write_bytes(b)
 counts['warm_pin_rejections']=3
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized guard');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_POINTER_PRODUCT_SCOUT',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=copy.deepcopy(PINS),counts=counts,forms=forms,genuine_fixtures=fixtures,nonunique_zero_fixture=nonunique,scope='Bounded fixed-N complete sources1..8. Exact natural existential projection of pointer fields and two unused last-row fields, not a bijection or same polynomial. No fixed-arity universality claim; formal degree grows withN.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts']);print([(f['packet']['N'],f['packet']['cleanup'],f['packet']['polynomial_ledger'])for f in out['forms']])
if __name__=='__main__':main()

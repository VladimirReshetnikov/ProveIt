"""Paid finite Tree triple-code lookup scout; external N in saved range1..8.

Only new code arithmetic is shared. Parent source arithmetic remains literal.
"""
import argparse,copy,hashlib,itertools,json,random,sys,math,tempfile,subprocess
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_constructor_projection.py':'a4c09cc720ac0d5b7f884e8636900a93ba6c17a7040a0f01c83b94f6f469bc81','eager_tree_constructor_projection.json':'26bf1f948751f94e77e5716fddc0668c8d8c910bcb2ac6237b50ece7a9090852','eager_tree_constructor_projection.md':'c5a65687c3756f220e11210525e9bc6ce7968ec2def7348a9dcf5d2cb69d8fc7'}
ORDERS=tuple(itertools.permutations(range(3)))
def need(q,s):
 if not q:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(tuple,list):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def parents(root=None):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 data={}
 for name,pin in PINS.items():
  blob=(root/name).read_bytes();need(hashlib.sha256(blob).hexdigest()==pin,'Parent pin '+name);data[name]=blob
 receipt=json.loads(data['eager_tree_constructor_projection.json']);out={}
 for form in receipt['forms']:
  p=form['packet'];out[p['N'],p['cleanup']]=p
 need(set(out)=={(n,c)for n in range(1,9)for c in(False,True)},'Exact saved parent family');return out

def live_rows(rows,ports):
 live={n for n in ports if type(n)is str}
 for n,op,a,b in reversed(rows):
  if n in live:live.update(x for x in(a,b)if type(x)is str)
 return [r for r in rows if r[0]in live]
def inspect(rows,free,ports):
 degrees={v:1 for v in free};deps={};M=0
 for n,o,a,b in rows:
  need(type(n)is str and n not in degrees and o in('+','-','*'),'Fresh arithmetic row')
  need(all(type(v)is int or type(v)is str and v in degrees for v in(a,b)),'Exact closed operand')
  da=degrees[a]if type(a)is str else 0;db=degrees[b]if type(b)is str else 0
  degrees[n]=da+db if o=='*'else max(da,db);deps[n]=(a,b);M+=o=='*'
 live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'Every gate and supplied coordinate live')
 return dict(M=M,A=len(rows)-M,operations=len(rows),degree_upper_bound=max(degrees[n]if type(n)is str else 0 for n in ports),all_live=True)
def finalize(rows,residuals):
 out=copy.deepcopy(rows)
 for i,r in enumerate(residuals):out.append([f'coded_square_{i}','*',r,r])
 last='coded_square_0'
 for i in range(1,len(residuals)):
  name=f'coded_sum_{i}';out.append([name,'+',last,f'coded_square_{i}']);last=name
 return out,last

class Emitter:
 def __init__(self,rows,share,pair_ports=None):self.rows=rows;self.share=share;self.cache={};self.number=0;self.pair_ports=pair_ports or {}
 def op(self,op,a,b):
  key=(op,tuple(sorted((a,b),key=lambda x:(type(x).__name__,str(x)))))if op in('+','*')else(op,(a,b))
  if self.share and key in self.cache:return self.cache[key]
  name='code_gate_'+str(self.number);self.number+=1;self.rows.append([name,op,a,b]);self.cache[key]=name;return name
 def add(self,a,b):return self.op('+',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def pair(self,u,v):
  if (u,v)in self.pair_ports:return self.sub(*self.pair_ports[u,v])
  s=self.add(u,v);return self.add(self.mul(s,s),u)
 def triple(self,coords,order):
  x,y,z=[coords[j]for j in order];return self.pair(x,self.pair(y,z))

def _build(old,mode,order,sharing,algebra=False):
 N=old['N'];old_defs={r[0]:r for r in old['source']};removed=[17*i+j for i in range(N)for j in range(8,17)]
 retained=[r for i,r in enumerate(old['residuals'])if i not in removed]
 target_ports=[]
 for i in range(N):
  targets=[]
  for slot in range(3):
   triple=[]
   for col in range(3):
    row=old_defs[old['residuals'][17*i+8+3*slot+col]];need(row[1]=='-','Literal old lookup subtraction');triple.append(row[3])
   targets.append(triple)
  target_ports.append(targets)
 seeds=retained+([x for row in target_ports for triple in row for x in triple]if mode=='weighted'else[])
 pair_ports={};proofs=[]
 if algebra:
  for i in range(N):
   a,y=f'r{i}_a',f'r{i}_y';definition=next(item for item in old['constructor_definitions']if item['coordinate']==f'r{i}_e');out=old_defs[definition['computed_port']]
   need(out[1]=='+'and out[3]==2,'Literal e final+2');plus=old_defs[out[2]];need(plus[1]=='+','Literal e sum');prod=old_defs[plus[2]];twoy=old_defs[plus[3]]
   need(prod[1]=='*'and twoy[1:]==['*',y,2],'Literal e quadratic and2y');summ=old_defs[prod[2]];one=old_defs[prod[3]]
   need(summ[1:]==['+',a,y]and one[1:]==['+',prod[2],1],'Literal paid (a+y)(a+y+1)')
   pair_ports[a,y]=(prod[0],y);pair_ports[y,a]=(prod[0],a);proofs.append(dict(row=i,paid_product=prod[0],sum_port=prod[2],identities=['P(a,y)=paid_product-y','P(y,a)=paid_product-a']))
 rows=copy.deepcopy(live_rows(old['source'],seeds));e=Emitter(rows,sharing,pair_ports);codes={} 
 # Root row0 has no incoming strict-forward pointers; do not pay a dead code.
 for j in range(1,N):codes[j]=e.triple([f'r{j}_{f}'for f in('x','y','z')],order)
 new_res=[];targets=[];maps=[]
 for i in range(N):
  var=lambda f:f'r{i}_{f}'
  t3,t4=var('t3'),var('t4')
  if mode=='weighted':t=[e.triple(c,order)for c in target_ports[i]]
  else:
   recipes=[(('b','y','u'),('y','a','u')),(('a','y','v'),('u','b','z'))]
   t=[]
   for slot,(left,right)in enumerate(recipes):
    if mode=='hybrid'and slot==0:
     need(order==(2,0,1),'Hybrid order');a=e.pair(var('b'),var('y'));b=e.pair(var('y'),var('a'));h=e.add(e.mul(t3,a),e.mul(t4,b));active=old_defs[old['residuals'][17*i+5]][3]
     need(old_defs[active][1:]==['+',t3,t4],'Paid active selector');t.append(e.pair(e.mul(active,var('u')),h))
    else:
     l=e.triple([var(f)for f in left],order);r=e.triple([var(f)for f in right],order)
     t.append(e.add(e.mul(t3,l),e.mul(t4,r)))
   t.append(e.mul(t3,e.triple([var(f)for f in('u','v','z')],order)))
  targets.append(t)
  for slot in range(3):
   terms=[e.mul(f'r{i}_p{slot}_{j}',codes[j])for j in range(i+1,N)]
   total=terms[0]if terms else 0
   for term in terms[1:]:total=e.add(total,term)
   r=e.sub(total,t[slot]);new_res.append(r);maps.append(dict(row=i,slot=slot,parent_indices=list(range(17*i+8+3*slot,17*i+11+3*slot)),child_port=r,target_port=t[slot],target_parent_ports=target_ports[i][slot]))
 residuals=retained+new_res;rows=live_rows(rows,residuals);poly,out=finalize(rows,residuals);ledger=inspect(poly,old['free'],[out])
 return dict(N=N,cleanup=old['cleanup'],mode=mode,order=list(order),sharing=sharing,algebra=algebra,paid_pair_recipes=proofs,free=copy.deepcopy(old['free']),source=rows,residuals=residuals,polynomial_source=poly,output=out,certificate_ledger=inspect(rows,old['free'],residuals),polynomial_ledger=ledger,witnesses=old['witnesses'],residual_count=len(residuals),parent_residuals=copy.deepcopy(old['residuals']),retained_parent_indices=[i for i in range(len(old['residuals']))if i not in removed],lookup_map=maps,row_code_ports={str(k):v for k,v in codes.items()},target_code_ports=targets,exact_degree={'weighted':16,'gated':10,'hybrid':12}[mode],full_polynomial_identity=False,natural_zero_tuple_equivalent=True,parent_pins=copy.deepcopy(PINS),scope='Finite saved parent range1..8; external N remains. All supplied coordinates natural including zero. Same full natural zero tuples, not polynomial equality or signed/real zero equivalence. No fixed-arity or paid ordinary-input recoder claim.')

def build(N,*,cleanup=True,mode='gated',order=(2,0,1),sharing=True,algebra=True,root=None):
 need(type(N)is int and 1<=N<=8 and type(cleanup)is bool and type(sharing)is bool and type(algebra)is bool,'Exact saved N and Boolean options')
 need(type(mode)is str and mode in('gated','weighted','hybrid')and type(order)is tuple and len(order)==3 and all(type(x)is int for x in order)and order in ORDERS,'Exact code recipe')
 need(mode!='hybrid'or order==(2,0,1),'Hybrid fixed order')
 return _build(parents(root)[N,cleanup],mode,order,sharing,algebra)
def checked(p,*,root=None):
 need(type(p)is dict,'Complete packet');q=build(p.get('N'),cleanup=p.get('cleanup'),mode=p.get('mode'),order=tuple(p.get('order',[])),sharing=p.get('sharing'),algebra=p.get('algebra'),root=root);need(exact(p,q),'Canonical full packet');return q

def run(rows,values):
 env=dict(values)
 for n,o,a,b in rows:
  x=env[a]if type(a)is str else a;y=env[b]if type(b)is str else b;env[n]=x+y if o=='+'else x-y if o=='-'else x*y
 return env

def add(a,b,sign=1):
 p=dict(a)
 for m,c in b.items():p[m]=p.get(m,0)+sign*c
 return {m:c for m,c in p.items()if c}
def mul(a,b):
 p={}
 for ma,ca in a.items():
  for mb,cb in b.items():m=tuple(sorted(ma+mb));p[m]=p.get(m,0)+ca*cb
 return {m:c for m,c in p.items()if c}
def atom(v):return {():v}if type(v)is int and v else {}if type(v)is int else {(v,):1}
def expand(rows,free):
 env={v:atom(v)for v in free}
 for n,o,a,b in rows:
  x=env[a]if type(a)is str else atom(a);y=env[b]if type(b)is str else atom(b);env[n]=mul(x,y)if o=='*'else add(x,y,-1 if o=='-'else 1)
 return env
def degree(p):return max(map(len,p),default=0)
def P(u,v):return (u+v)**2+u
def C(coords,order):
 x,y,z=[coords[j]for j in order];return P(x,P(y,z))
def digest(obj):return hashlib.sha256(json.dumps(obj,sort_keys=True,separators=(',',':')).encode()).hexdigest()

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
 oldforms=parents(root);census=[];selected=[];counts=dict(complete_sources=0,retained_literal_gates=0,retained_residuals=0,whole_corrections=0,rational_corrections=0,target_values=0,exact_degrees=0,injective_codes=0,local_natural_equivalences=0)
 rng=random.Random(271001)
 for N in range(1,9):
  for cleanup in(False,True):
   old=oldforms[N,cleanup];parentnodes={r[0]:r for r in old['source']};best=None
   for mode,order,sharing,algebra in [('gated',o,s,a)for o in ORDERS for s in(False,True)for a in(False,True)]+[('weighted',(0,1,2),False,False),('hybrid',(2,0,1),True,True)]:
    p=_build(old,mode,order,sharing,algebra);need(p['free']==old['free']and p['residual_count']==11*N+3,'Complete supplied interface')
    copied=[r for r in p['source']if r[0]in parentnodes];need(all(parentnodes[r[0]]==r for r in copied),'Literal retained arithmetic');counts['retained_literal_gates']+=len(copied)
    kept=[old['residuals'][i]for i in p['retained_parent_indices']];need(p['residuals'][:len(kept)]==kept,'Every retained residual port');counts['retained_residuals']+=len(kept)
    ledger=p['polynomial_ledger'];need(ledger['degree_upper_bound']==p['exact_degree'],'Formal degree upper')
    if not sharing and not algebra:
     expected=(9*N*N+(229-2*int(cleanup))*N+16)//2
     need(ledger['operations']==expected,'No-sharing exact complete formula')
     em=(3*N*N+(91 if mode=='gated'else 101)*N+2)//2
     ea=3*N*N+((69 if mode=='gated'else 64)-int(cleanup))*N+7
     need((ledger['M'],ledger['A'])==(em,ea),'Mode-specific unshared ledger')
    for case in range(3):
     v={f:rng.randint(-2,3)for f in p['free']}
     if case==2:v={f:Fraction(x,3)for f,x in v.items()};counts['rational_corrections']+=1
     before=run(old['polynomial_source'],v);after=run(p['polynomial_source'],v)
     correction=sum(after[m['child_port']]**2-sum(before[old['residuals'][idx]]**2 for idx in m['parent_indices'])for m in p['lookup_map'])
     need(after[p['output']]-before[old['output']]==correction,'Entire signed/rational polynomial correction');counts['whole_corrections']+=1
     for item in p['lookup_map']:
      i=item['row'];slot=item['slot'];local=lambda f:v[f'r{i}_{f}'];t3,t4=local('t3'),local('t4')
      if mode=='weighted':expect=C([before[x]if type(x)is str else x for x in item['target_parent_ports']],order)
      else:
       choices=[((local('b'),local('y'),local('u')),(local('y'),local('a'),local('u'))),((local('a'),local('y'),local('v')),(local('u'),local('b'),local('z')))]
       expect=t3*C(choices[slot][0],order)+t4*C(choices[slot][1],order)if slot<2 else t3*C((local('u'),local('v'),local('z')),order)
       if mode=='hybrid'and slot==0:expect=P((t3+t4)*local('u'),t3*P(local('b'),local('y'))+t4*P(local('y'),local('a')))
      need(after[item['target_port']]==expect,'Literal entire target code');counts['target_values']+=1
    # Exact sparse residual expansion supplies a nonzero highest form.
    # The sum of real squares of highest forms cannot cancel.
    residual_polys=expand(p['source'],p['free']);maxdeg=max(degree(residual_polys[r])for r in p['residuals']);need(2*maxdeg==p['exact_degree'],'Exact nonzero residual leader')
    leaders=[dict(port=r,degree=degree(residual_polys[r]),terms=sum(len(m)==maxdeg for m in residual_polys[r]))for r in p['residuals']if degree(residual_polys[r])==maxdeg]
    counts['exact_degrees']+=1
    if algebra and order==(2,0,1)and mode=='gated':
     need((ledger['M'],ledger['A'])==((3*N*N+87*N+2)//2,3*N*N+(67-int(cleanup))*N+7),'Best degree10 complete formula')
    if mode=='hybrid':
     need((ledger['M'],ledger['A'])==((3*N*N+87*N+2)//2,3*N*N+(65-int(cleanup))*N+7),'Hybrid degree12 complete formula')
    # Prove the literal new target polynomial, including on all three
    # permissible tag choices, independently of the encoded lookup.
    def pp(u,v):return add(mul(add(u,v),add(u,v)),u)
    def cc(coords):
     xx,yy,zz=[coords[j]for j in order];return pp(xx,pp(yy,zz))
    if N==1:
     def pol(f):return atom('r0_'+f)
     a,b,u,v,y,z=[pol(f)for f in('a','b','u','v','y','z')];t3,t4=pol('t3'),pol('t4')
     weights=[(add(mul(t3,b),mul(t4,y)),add(mul(t3,y),mul(t4,a)),mul(add(t3,t4),u)),(add(mul(t3,a),mul(t4,u)),add(mul(t3,y),mul(t4,b)),add(mul(t3,v),mul(t4,z))),(mul(t3,u),mul(t3,v),mul(t3,z))]
     branch=[add(mul(t3,cc((b,y,u))),mul(t4,cc((y,a,u)))),add(mul(t3,cc((a,y,v))),mul(t4,cc((u,b,z)))),mul(t3,cc((u,v,z)))]
     expect=[cc(w)for w in weights]if mode=='weighted'else list(branch)
     if mode=='hybrid':expect[0]=pp(mul(add(t3,t4),u),add(mul(t3,pp(b,y)),mul(t4,pp(y,a))))
     for slot in range(3):need(residual_polys[p['target_code_ports'][0][slot]]==expect[slot],'Entire exact target coefficient identity')
     def subst(poly,a,b):
      out={}
      for mon,coef in poly.items():
       rest=[]
       for variable in mon:
        if variable=='r0_t3':coef*=a
        elif variable=='r0_t4':coef*=b
        else:rest.append(variable)
       out=add(out,{tuple(rest):coef})
      return out
     for bits in((0,0),(1,0),(0,1)):
      for slot in range(3):need(subst(expect[slot],*bits)==subst(cc(weights[slot]),*bits),'Exact active/inactive target identity')
     counts['exact_target_identities']=counts.get('exact_target_identities',0)+3
     counts['exact_tag_chart_identities']=counts.get('exact_tag_chart_identities',0)+9
    record=dict(N=N,cleanup=cleanup,mode=mode,order=list(order),sharing=sharing,algebra=algebra,ledger=ledger,source_sha256=digest(p['polynomial_source']),exact_degree=p['exact_degree'],leading_residuals=leaders)
    census.append(record);counts['complete_sources']+=1
    if mode=='gated'and(best is None or(ledger['operations'],ledger['M'],order)<(best['polynomial_ledger']['operations'],best['polynomial_ledger']['M'],tuple(best['order']))):best=p
    if N==8 and cleanup and(mode in('weighted','hybrid')or not sharing and not algebra and order==(0,1,2)):selected.append(p)
   selected.append(best)
 # Finite evidence supplements the shell proof, not a bounded proof of it.
 for order in ORDERS:
  seen={}
  for xyz in itertools.product(range(13),repeat=3):
   value=C(xyz,order);need(value not in seen,'Natural triple code injectivity');seen[value]=xyz;counts['injective_codes']+=1
  need(seen[0]==(0,0,0),'Zero-preserving code')
 # Actual tag/pointer premises: active0/all pointers0 or active1/one pointer1.
 for order in ORDERS:
  for xyz in itertools.product(range(4),repeat=3):
   for target in itertools.product(range(4),repeat=3):
    need((C(xyz,order)==C(target,order))==(xyz==target),'Active lookup equivalence');counts['local_natural_equivalences']+=1
  need(C((0,0,0),order)==0,'Inactive lookup zero')

 fixtures=[];tags=set();counts['genuine_complete_zeros']=0;counts['mutated_complete_zero_equivalences']=0
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
   values=flatten_records(records,keys,(x,y,z));old=oldforms[N,True];v={f:values[f]for f in old['free']};need(run(old['polynomial_source'],v)[old['output']]==0,'Independent original complete zero')
   for mode in('gated','hybrid','weighted'):
    order=(0,1,2)if mode=='weighted'else(2,0,1);p=_build(old,mode,order,True,mode!='weighted')
    need(run(p['polynomial_source'],v)[p['output']]==0,'Same-tuple complete coded zero');counts['genuine_complete_zeros']+=1
    for coordinate in p['free']:
     w=dict(v);w[coordinate]+=1
     need((run(old['polynomial_source'],w)[old['output']]==0)==(run(p['polynomial_source'],w)[p['output']]==0),'Single-coordinate natural zero equivalence');counts['mutated_complete_zero_equivalences']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(tags==set(range(5)),'All five eager Tree root rules')
 # Local domain limits: neither signed nor nonnegative rational injectivity.
 need(P(-1,0)==P(0,0)==0 and P(Fraction(7,16),Fraction(5,16))==P(0,1)==1,'Exact domain counterexamples')
 counts['guards']=0
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Malformed accepted')
 for n in(True,False,0,-1,9,1.0,'1',None):reject(lambda n=n:build(n,root=root))
 for field in('cleanup','sharing','algebra'):
  for value in(0,1,None,'true'):reject(lambda field=field,value=value:build(2,root=root,**{field:value}))
 for order in([2,0,1],(2,False,1),(2,0,0),(0,1),None):reject(lambda order=order:build(2,root=root,order=order))
 reject(lambda:build(2,root=root,mode='hybrid',order=(0,1,2)))
 p=build(2,root=root)
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root))
 for key in('N','witnesses','residual_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:checked(q,root=root))
 counts['copies']=0
 for key in('source','polynomial_source','lookup_map','target_code_ports','parent_pins'):
  q=build(2,root=root);q[key].clear();need(exact(build(2,root=root),p),'Independent rebuilt copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='tree_coded_pins_')as temp:
  base=Path(temp);data={name:(Path(root)/name).read_bytes()for name in PINS}
  for name,blob in data.items():(base/name).write_bytes(blob)
  build(2,root=base)
  for name,blob in data.items():
   (base/name).write_bytes(blob+b'\n');reject(lambda:build(2,root=base));(base/name).write_bytes(blob)
 counts['warm_pin_rejections']=len(PINS)
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'Optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_CODED_LOOKUP_SCOUT',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=PINS,counts=counts,genuine_fixtures=fixtures,census=census,selected_full_packets=selected,scope='Bounded paid-source scout, saved parent N1..8, natural zero equivalence theorem generalizes the same templates to external N. No general optimization or fixed-arity universality claim.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt')
 if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(out['status'],out['counts']);print('best',[(p['N'],p['cleanup'],p['order'],p['polynomial_ledger'])for p in out['selected_full_packets']if p['mode']=='gated'and p['algebra']])
if __name__=='__main__':main()

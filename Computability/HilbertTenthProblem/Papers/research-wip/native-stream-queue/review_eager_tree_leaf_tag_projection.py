#!/usr/bin/env python3
"""Independent complete-source review of the finite Tree leaf-tag projection."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT={
'eager_tree_terminal_projection.py':'edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd',
'eager_tree_terminal_projection.json':'25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95',
'eager_tree_terminal_projection.md':'ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def pins(root,manifest):
 out={}
 for n,h in manifest.items():
  b=(Path(root)/n).read_bytes();need(sha(b)==h,'Pinned blob '+n);out[n]=b
 return out
def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs):
 known=set(free);defs={};degree={x:1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
def diagonal(rows,free):
 def add(a,b,s=1):
  c=[0]*max(len(a),len(b))
  for i,x in enumerate(a):c[i]+=x
  for i,x in enumerate(b):c[i]+=s*x
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e={x:[0,1]for x in free}
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else[a];b=e[b]if type(b)is str else[b];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

def simple_zero(old,tag=0):
 N=old['N'];v={n:0 for n in old['free']}
 for i in range(N):v[f'r{i}_t0']=1;v[f'r{i}_z']=1
 if tag==0:v.update(program=0,argument=0,output=1)
 elif N==1:
  v['r0_t0']=0;v[f'r0_t{tag}']=1
  if tag==1:
   a,y=2,3;z=(a+y)*(a+y+1)+2*y+2
   v.update(r0_a=a,r0_x=2*a+1,r0_y=y,r0_z=z,program=2*a+1,argument=y,output=z)
  else:
   b,y=2,3;x=b*(b+1)+2*b+2
   v.update(r0_b=b,r0_x=x,r0_y=y,r0_z=b,program=x,argument=y,output=b)
 else:raise ValueError('only last leaf alternatives at N1')
 need(numeric(old['polynomial_source'],v)[old['output']]==0,'handwritten complete parent zero')
 return v


class RingDAG:
 # Linear combinations of opaque product atoms. Addition normalizes exact
 # coefficients; multiplication extracts scalar signs but never expands sums.
 def __init__(self):self.ids={('one',):0}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.node(('var',x)),1),)
 def scale(self,e,c):return tuple((k,v*c)for k,v in e)if c else()
 def add(self,a,b,sign=1):
  e=dict(a)
  for n,c in b:e[n]=e.get(n,0)+sign*c
  return tuple(sorted((n,c)for n,c in e.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return self.scale(b,a[0][1])
  if len(b)==1 and b[0][0]==0:return self.scale(a,b[0][1])
  sa=-1 if a[0][1]<0 else 1;sb=-1 if b[0][1]<0 else 1
  a=self.scale(a,sa);b=self.scale(b,sb)
  if a>b:a,b=b,a
  return((self.node(('mul',a,b)),sa*sb),)
 def run(self,rows,free,replacements=None):
  e={n:self.val(n)for n in free};e.update(replacements or{})
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else -1)
  return e

def literal(old):
 N=old['N'];defs={n:(o,a,b)for n,o,a,b in old['source']};pos={r[0]:i for i,r in enumerate(old['source'])};remove=set();inserts={};leafmap={};maps=[]
 for i in range(N):
  tag=f'r{i}_t0';root=old['residuals'][5*i];leaf=old['residuals'][5*i+2];chain=set()
  def cone(name):
   if type(name)is int or name in old['free']:return
   o,a,b=defs[name];need(o in('+','-'),'affine one-hot cone');chain.add(name);cone(a);cone(b)
  cone(root);order=sorted(chain,key=pos.get);first=order[0]
  need(len(chain)==(3 if i==N-1 else 5),'complete original one-hot gate count')
  need(defs[root][0]=='-'and defs[root][2]==1 and defs[first]==('+',tag,f'r{i}_t1'),'actual original one-hot endpoints')
  need([n for n,o,a,b in old['source']if tag in(a,b)]==[first,leaf],'private tag consumers')
  need(defs[leaf][0]=='*'and defs[leaf][1]==tag,'actual old leaf multiplier')
  for j,n in enumerate(order[:-1]):need([r[0]for r in old['source']if n in r[2:]]==[order[j+1]],'private one-hot chain')
  pair=f'leaf_tag_pair_{i}';sm=f'leaf_tag_sum_{i}';minus=f'leaf_tag_minus_{i}';guard=f'leaf_tag_guard_{i}';new=[[pair,'+',f'r{i}_t1',f'r{i}_t2']];active=None
  if i<N-1:
   found=[n for n,o,a,b in old['source']if(o,a,b)==('+',f'r{i}_t3',f'r{i}_t4')];need(len(found)==1,'one existing active addition');active=found[0];need(pos[active]<pos[first],'active already paid before use');new.append([sm,'+',pair,active])
  else:sm=pair
  new.extend([[minus,'-',sm,1],[guard,'*',sm,minus]]);inserts[first]=new;remove.update(chain);leafmap[leaf]=minus
  maps.append(dict(row=i,parent_tag=tag,parent_tag_residual=root,parent_leaf_residual=leaf,active_port=active,tag_sum=sm,sum_minus_one=minus,guard=guard,removed_chain=order))
 rows=[]
 for n,o,a,b in old['source']:
  rows.extend(inserts.get(n,[]))
  if n not in remove:rows.append([n,o,leafmap.get(n,a),b])
 terms=[dict(kind='integer_nonnegative_guard',port=maps[j//5]['guard'])if j<5*N and j%5==0 else dict(kind='square',port=r)for j,r in enumerate(old['residuals'])]
 free=[n for n in old['free']if n not in{m['parent_tag']for m in maps}];poly=copy.deepcopy(rows);ports=[]
 for i,t in enumerate(terms):
  n=t['port']
  if t['kind']=='square':n=f'leaf_square_{i}';poly.append([n,'*',t['port'],t['port']])
  ports.append(n)
 out=ports[0]
 for i,n in enumerate(ports[1:],1):nxt=f'leaf_sum_{i}';poly.append([nxt,'+',out,n]);out=nxt
 return rows,poly,out,free,terms,maps

def restore(p,v):
 out=dict(v)
 for i in range(p['N']):out[f'r{i}_t0']=1-sum(v[f'r{i}_t{j}']for j in range(1,3 if i==p['N']-1 else 5))
 return out

AUTHOR={
'eager_tree_leaf_tag_projection.py':'e491a2dd852fca307d1c5f7138b078a0b815a0cea271ef05000cf001be1f6015',
'eager_tree_leaf_tag_projection.json':'1f786cd77987db5892ac40b4329f7bce1b6ad3ff26aa7cf15e0a25dde21114eb',
'eager_tree_leaf_tag_projection.md':'9f6e8d07accec6eb33ee402427e7fd795ff91487174fc47248653e855447ea8f',
}
def application_zero(old,tag):
 N=old['N'];need(N>=3 and tag in(3,4),'small complete application fixture');v=simple_zero(old);v['r0_t0']=0;v[f'r0_t{tag}']=1
 x,z,y2=(4,6,1)if tag==3 else(8,2,0)
 v.update(program=x,argument=0,output=z,r0_x=x,r0_z=z,r0_u=1,r0_v=1 if tag==3 else 0,r2_t0=0,r2_t1=1,r2_x=1,r2_y=y2,r2_z=z)
 need(numeric(old['polynomial_source'],v)[old['output']]==0,'hand-derived Tree application parent zero')
 return v

def verify(root,artifacts):
 raw=pins(root,PARENT);ab=pins(artifacts,AUTHOR);oldjson=json.loads(raw['eager_tree_terminal_projection.json']);saved=json.loads(ab['eager_tree_leaf_tag_projection.json'])
 need(oldjson['source_sha256']==PARENT['eager_tree_terminal_projection.py']and saved['source_sha256']==AUTHOR['eager_tree_leaf_tag_projection.py'],'source receipt linkage')
 olds={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in oldjson['forms']};children={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in saved['forms']}
 family={(N,c)for N in range(1,9)for c in(False,True)};need(len(oldjson['forms'])==len(saved['forms'])==16 and set(olds)==set(children)==family,'exact finite family coverage')
 path=Path(artifacts)/'eager_tree_leaf_tag_projection.py';mod=types.ModuleType('_authenticated_leaf_tag');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 counts=dict(literal_complete_sources=0,whole_ring_corrections=0,ordinary_residuals=0,zero_tag_rows=0,leaf_signs=0,guard_identities=0,paid_live_gates=0,exact_degrees=0,numeric_corrections=0,rational_corrections=0,natural_zero_bijections=0,offzero_negative_pullbacks=0,real_counterexamples=0,guards=0,copies=0,warm_pins=0)
 rng=random.Random(611305);results=[]
 for N,cleanup in sorted(family):
  old=olds[N,cleanup];p=mod.build(N,cleanup=cleanup,root=root);need(exact(p,children[N,cleanup]),'saved entire child source');need(exact(mod.canonical_parent(N,cleanup=cleanup,root=root),old),'canonical exact parent')
  need(exact(mod.rewrite(copy.deepcopy(old),root=root),p)and exact(mod.checked(p,root=root),p),'public rewrite/check canonical')
  rows,poly,out,free,terms,maps=literal(old)
  need(exact(p['source'],rows)and exact(p['polynomial_source'],poly)and exact(p['free'],free)and p['output']==out,'entire independent literal schedule')
  need(exact(p['finalizer_terms'],terms)and exact(p['row_map'],maps),'current mixed finalizer and all source maps')
  guards=[t['port']for t in terms if t['kind']=='integer_nonnegative_guard'];ordinary=[t['port']for t in terms if t['kind']=='square']
  need(exact(p['ordinary_residuals'],ordinary)and exact(p['integer_guard_ports'],guards),'distinct ordinary residuals and unsquared guards')
  need(p['squared_residual_count']==len(ordinary)==7*N and p['unsquared_guard_count']==len(guards)==N and p['nonnegative_term_count']==len(terms)==8*N,'mixed term counts')
  ring=RingDAG();post=ring.run(poly,free);replacements={}
  for i in range(N):
   s=()
   for j in range(1,3 if i==N-1 else 5):s=ring.add(s,ring.val(f'r{i}_t{j}'))
   replacements[f'r{i}_t0']=ring.add(ring.val(1),s,-1)
   need(post[maps[i]['tag_sum']]==s and post[guards[i]]==ring.mul(s,ring.add(s,ring.val(1),-1)),'literal s(s-1) guard identity');counts['guard_identities']+=1
  before=ring.run(old['polynomial_source'],old['free'],replacements)
  for m in maps:
   need(before[m['parent_tag_residual']]==(),'actual old one-hot chain vanishes, no assumed cut');counts['zero_tag_rows']+=1
   leaf=m['parent_leaf_residual'];need(before[leaf]==ring.scale(post[leaf],-1),'exact leaf sign from actual expressions');counts['leaf_signs']+=1
  leaves={m['parent_leaf_residual']for m in maps}
  for r in ordinary:
   need(before[r]==ring.scale(post[r],-1)if r in leaves else before[r]==post[r],'entire retained residual identity');counts['ordinary_residuals']+=1
  correction=()
  for g in guards:correction=ring.add(correction,post[g])
  need(post[out]==ring.add(before[old['output']],correction),'whole exact ring polynomial correction without supplied cuts');counts['whole_ring_corrections']+=1
  M,A,upper=ledger(poly,free,[out]);cm,ca,cu=ledger(rows,free,[t['port']for t in terms]);om,oa,_=ledger(old['polynomial_source'],old['free'],[old['output']]);ocm,oca,_=ledger(old['source'],old['free'],old['residuals'])
  need((M,A)==((3*N*N+81*N-46)//2,(3*N*N+(127-2*int(cleanup))*N-76)//2),'independent general full ledger')
  need(om==M and oa-A==2*N-1 and cm-ocm==N and oca-ca==2*N-1,'full versus certificate deltas')
  need(p['polynomial_ledger']==dict(M=M,A=A,operations=M+A,degree_upper_bound=upper,all_live=True)and p['certificate_ledger']==dict(M=cm,A=ca,operations=cm+ca,degree_upper_bound=cu,all_live=True),'current full/certificate metadata')
  need(len(free)-3==p['witnesses']==12*N-5 and set(old['free'])-set(free)=={f'r{i}_t0'for i in range(N)},'all removed coordinates precisely leaf tags')
  coeff=diagonal(poly,free)[out];degree=6 if N==1 else 10*N-8;leading=17 if N==1 else 8*2**(10*(N-1))+2**(8*(N-1))
  need(len(coeff)-1==upper==p['exact_degree']==degree and coeff[-1]==leading==p['degree_certificate']['diagonal_leading_coefficient'],'actual exact full degree')
  need(p['full_polynomial_identity']is False and p['natural_zero_bijection']is True and p['unconditional_natural_pullback']is False and p['sos_finalizer']is False and exact(p['parent_pins'],PARENT),'precise current domain/finalizer/provenance metadata')
  counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A;counts['exact_degrees']+=1
  for k in range(8):
   v={n:rng.randrange(4)if k<3 else rng.randrange(-3,5)for n in free}
   if k==7:v={n:Fraction(x,3)for n,x in v.items()};counts['rational_corrections']+=1
   restored=restore(p,v);e=numeric(poly,v);beforeval=numeric(old['polynomial_source'],restored)[old['output']];need(e[out]==beforeval+sum(e[g]for g in guards),'complete numeric correction');counts['numeric_corrections']+=1
   if k<7:need(exact(mod.integer_pullback(p,v,root=root),restored)and mod.evaluate(p,v,signed=k>=3,root=root)==e[out],'public signed/natural algebra')
   if k<3:need(all(e[g]>=0 for g in guards)and e[out]>=0,'nonnegative integer finalizer')
  one={n:1 for n in free};need(min(mod.integer_pullback(p,one,root=root).values())<0 and mod.evaluate(p,one,root=root)>0,'natural inverse is not unconditional');counts['offzero_negative_pullbacks']+=1
  fixtures=[simple_zero(old)]
  if N==1:fixtures.extend([simple_zero(old,1),simple_zero(old,2)])
  if N>=3:fixtures.extend([application_zero(old,3),application_zero(old,4)])
  for v in fixtures:
   q={n:v[n]for n in free};need(exact(mod.project_parent_zero(p,v,root=root),q)and mod.evaluate(p,q,root=root)==0,'natural zero projection')
   need(exact(mod.restore_zero(p,q,root=root),v)and exact(restore(p,q),v),'full natural zero inverse, no normalized-slice omission');counts['natural_zero_bijections']+=1
  results.append(dict(N=N,cleanup=cleanup,M=M,A=A,operations=M+A,witnesses=p['witnesses'],squares=7*N,unsquared_guards=N,exact_degree=degree,diagonal_leading_coefficient=leading,coefficient_sha256=sha(json.dumps(coeff,separators=(',',':')).encode())))
 # Genuine whole-polynomial nonnegative rational counterexample, not merely a negative guard.
 p=mod.build(1,root=root);old=olds[1,True];v={n:Fraction(0)for n in p['free']};v.update(r0_x=Fraction(1),r0_t2=Fraction(1,2),program=Fraction(1))
 need(numeric(p['polynomial_source'],v)[p['output']]==0 and numeric(old['polynomial_source'],restore(p,v))[old['output']]==Fraction(1,4),'full nonnegative-real zero nonequivalence');counts['real_counterexamples']=1
 signed={n:0 for n in old['free']};signed.update(r0_t0=-1,r0_t2=2,r0_b=1,r0_z=1,r0_x=12,program=12,output=1)
 projected={n:signed[n]for n in p['free']}
 need(numeric(old['polynomial_source'],signed)[old['output']]==0 and numeric(p['polynomial_source'],projected)[p['output']]==2,'actual full signed-parent zero lacks child zero');counts['signed_counterexamples']=1
 # General integer guard argument has no finite bound; this census checks representative signs and roots.
 for s in range(41):need(s*(s-1)>=0 and(s*(s-1)==0)==(s in(0,1)),'integer guard roots')
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed call accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,N=N:fn(N,root=root))
 for c in(0,1,None,'true'):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,c=c:fn(2,cleanup=c,root=root))
 p=mod.build(2,root=root);old=olds[2,True];v={n:0 for n in p['free']};parentzero=simple_zero(old);childzero={n:parentzero[n]for n in p['free']}
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:mod.checked(q,root=root))
 for key in('N','witnesses','squared_residual_count','unsquared_guard_count','nonnegative_term_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('full_polynomial_identity','natural_zero_bijection','unconditional_natural_pullback','sos_finalizer','cleanup'):
  q=copy.deepcopy(p);q[key]=int(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('free','source','polynomial_source','row_map','finalizer_terms'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['finalizer_terms'][0]['kind']='square';reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:mod.checked(q,root=root))
 for key in old:
  q=copy.deepcopy(old);del q[key];reject(lambda q=q:mod.rewrite(q,root=root))
 for val in(True,0.0,Fraction(0),-1):
  bad=dict(v,program=val)
  for fn in(mod.evaluate,mod.restore_zero):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
  if val!=-1 or type(val)is not int:reject(lambda bad=bad:mod.integer_pullback(p,bad,root=root))
 for bad in({},dict(v,extra=0),list(v)):
  for fn in(mod.evaluate,mod.integer_pullback,mod.restore_zero):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:mod.evaluate(p,v,signed=mode,root=root))
 reject(lambda:mod.restore_zero(p,v,root=root));reject(lambda:mod.restore_zero(p,{n:1 for n in p['free']},root=root))
 for bad in({n:0 for n in old['free']},dict(parentzero,program=True),dict(parentzero,program=0.0),dict(parentzero,extra=0)):reject(lambda bad=bad:mod.project_parent_zero(p,bad,root=root))
 for key,val in p.items():
  if type(val)in(dict,list):
   q=mod.build(2,root=root);q[key].clear();need(exact(mod.build(2,root=root),p),'every mutable metadata/source copy');counts['copies']+=1
 for fn in(lambda:mod.canonical_parent(2,root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(mod.build(2,root=root),p)and exact(mod.canonical_parent(2,root=root),old),'canonical accessor isolated');counts['copies']+=1
 q=mod.polynomial_source(p,root=root);q.clear();need(exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'source accessor isolated');counts['copies']+=1
 for fn,original in[(lambda:mod.integer_pullback(p,v,root=root),v),(lambda:mod.restore_zero(p,childzero,root=root),childzero),(lambda:mod.project_parent_zero(p,parentzero,root=root),parentzero)]:
  q=fn();q['program']=99;need(original['program']==0,'map return copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='leaf_tag_independent_')as temp:
  temp=Path(temp)
  for n,b in raw.items():(temp/n).write_bytes(b)
  mod.build(2,root=temp)
  for n,b in raw.items():
   (temp/n).write_bytes(b+b'\n')
   for fn in(lambda:mod.build(2,root=temp),lambda:mod.canonical_parent(2,root=temp),lambda:mod.rewrite(old,root=temp),lambda:mod.checked(p,root=temp),lambda:mod.polynomial_source(p,root=temp),lambda:mod.evaluate(p,v,root=temp),lambda:mod.integer_pullback(p,v,root=temp),lambda:mod.restore_zero(p,childzero,root=temp),lambda:mod.project_parent_zero(p,parentzero,root=temp)):reject(fn);counts['warm_pins']+=1
   (temp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'explicit optimized-Python reject');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_EAGER_TREE_LEAF_TAG_PROJECTION',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PARENT,author_pins=AUTHOR,counts=counts,forms=results,scope='All16 full mixed-finalizer sources, exact signed graph correction, natural zero bijection only with terminal parent, exact degree and guarded API. No unconditional natural pullback, real zero equivalence, historical parent bijection, or fixed-arity universal bound.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact independent receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()

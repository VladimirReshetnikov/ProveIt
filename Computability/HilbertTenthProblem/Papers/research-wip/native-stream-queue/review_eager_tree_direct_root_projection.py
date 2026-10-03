#!/usr/bin/env python3
"""Independent complete-source review of the finite Tree direct-root projection."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT={
'eager_tree_leaf_tag_projection.py':'e491a2dd852fca307d1c5f7138b078a0b815a0cea271ef05000cf001be1f6015',
'eager_tree_leaf_tag_projection.json':'1f786cd77987db5892ac40b4329f7bce1b6ad3ff26aa7cf15e0a25dde21114eb',
'eager_tree_leaf_tag_projection.md':'9f6e8d07accec6eb33ee402427e7fd795ff91487174fc47248653e855447ea8f',
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


ALIASES={'r0_x':'program','r0_y':'argument','r0_z':'output'}
def parent_zero(old,tag=0):
 N=old['N'];v={n:0 for n in old['free']}
 for i in range(N):v[f'r{i}_z']=1
 v.update(program=0,argument=0,output=1)
 if tag in(1,2):
  need(N==1,'one-row terminal alternatives');v[f'r0_t{tag}']=1
  if tag==1:v.update(r0_a=2,r0_x=5,r0_y=3,r0_z=38,program=5,argument=3,output=38)
  else:v.update(r0_b=2,r0_x=12,r0_y=3,r0_z=2,program=12,argument=3,output=2)
 if tag in(3,4):
  need(N>=3,'recursive examples need3rows');x,z,y2=(4,6,1)if tag==3 else(8,2,0)
  v.update(program=x,argument=0,output=z,r0_x=x,r0_z=z,r0_u=1,r0_v=1 if tag==3 else 0,r2_t1=1,r2_x=1,r2_y=y2,r2_z=z);v[f'r0_t{tag}']=1
 need(numeric(old['polynomial_source'],v)[old['output']]==0,'handwritten complete mixed-parent natural zero')
 return v

def literal(old):
 bindings=[]
 for x,y in ALIASES.items():
  matches=[r[0]for r in old['source']if r[1:]==['-',x,y]];need(len(matches)==1,'unique literal binding');bindings.extend(matches)
 need([t for t in old['finalizer_terms']if t['port']in bindings]==[dict(kind='square',port=r)for r in bindings],'three binding squares')
 need(all(not any(r in row[2:]for row in old['source'])for r in bindings),'binding ports private to finalizer')
 rows=[[n,o,ALIASES.get(a,a),ALIASES.get(b,b)]for n,o,a,b in old['source']if n not in bindings]
 terms=[copy.deepcopy(t)for t in old['finalizer_terms']if t['port']not in bindings]
 free=[n for n in old['free']if n not in ALIASES]
 return rows,free,terms,bindings

AUTHOR={
'eager_tree_direct_root_projection.py':'1c2b52002c04ada2187c1ef4f1e28b5d5648a8bfc7f93e540f18c86543ecbb84',
'eager_tree_direct_root_projection.json':'31cd205ca1faed80d20e3db68e8288884243f0f1c43c5d319a4f6cfe94810c7d',
'eager_tree_direct_root_projection.md':'4ad2b339b67a75ce7941437a3b3edd4d70c00a35e8269daf0a340b307fa267f6',
}
def verify(root,artifacts):
 raw=pins(root,PARENT);ab=pins(artifacts,AUTHOR);oldjson=json.loads(raw['eager_tree_leaf_tag_projection.json']);saved=json.loads(ab['eager_tree_direct_root_projection.json'])
 need(oldjson['source_sha256']==PARENT['eager_tree_leaf_tag_projection.py']and saved['source_sha256']==AUTHOR['eager_tree_direct_root_projection.py'],'source/receipt links')
 olds={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in oldjson['forms']};children={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in saved['forms']};family={(N,c)for N in range(1,9)for c in(False,True)}
 need(len(oldjson['forms'])==len(saved['forms'])==16 and set(olds)==set(children)==family,'exact16form family coverage')
 path=Path(artifacts)/'eager_tree_direct_root_projection.py';mod=types.ModuleType('_authenticated_direct_root');mod.__file__=str(path);exec(compile(ab[path.name],str(path),'exec'),mod.__dict__)
 counts=dict(literal_complete_sources=0,complete_graph_identities=0,retained_gate_identities=0,retained_square_residuals=0,retained_guards=0,zero_bindings=0,paid_live_gates=0,exact_degrees=0,full_diagonal_identities=0,numeric_identities=0,rational_identities=0,unconditional_natural_restorations=0,natural_zero_bijections=0,inherited_rational_boundary=0,guards=0,copies=0,warm_pins=0)
 rng=random.Random(399946);results=[]
 for N,cleanup in sorted(family):
  old=olds[N,cleanup];p=mod.build(N,cleanup=cleanup,root=root)
  need(exact(p,children[N,cleanup])and exact(mod.canonical_parent(N,cleanup=cleanup,root=root),old),'whole saved/current sources')
  need(exact(mod.rewrite(old,root=root),p)and exact(mod.checked(p,root=root),p),'canonical public rewrite/check')
  rows,free,terms,bindings=literal(old);need(exact(p['source'],rows)and exact(p['free'],free)and exact(p['finalizer_terms'],terms),'literal certificate projection')
  poly=copy.deepcopy(rows);ports=[]
  for i,t in enumerate(terms):
   n=t['port']
   if t['kind']=='square':n=f'direct_root_square_{i}';poly.append([n,'*',t['port'],t['port']])
   ports.append(n)
  out=ports[0]
  for i,n in enumerate(ports[1:],1):nxt=f'direct_root_sum_{i}';poly.append([nxt,'+',out,n]);out=nxt
  need(exact(poly,p['polynomial_source'])and out==p['output'],'literal complete mixed finalizer')
  ordinary=[t['port']for t in terms if t['kind']=='square'];guards=[t['port']for t in terms if t['kind']=='integer_nonnegative_guard']
  binding_map=[dict(parent_field=x,ordinary_port=y,parent_residual=r,parent_term_index=next(i for i,t in enumerate(old['finalizer_terms'])if t['port']==r))for (x,y),r in zip(ALIASES.items(),bindings)]
  need(exact(p['root_binding_map'],binding_map)and exact(p['root_aliases'],ALIASES),'entire source mapping')
  need(exact(p['ordinary_residuals'],ordinary)and exact(p['integer_guard_ports'],guards),'retained mixed ports')
  for item in binding_map:
   need([r[0]for r in old['source']if item['ordinary_port']in r[2:]]==[item['parent_residual']],'ordinary port previously had only binding consumer')
  ring=RingDAG();before=ring.run(old['polynomial_source'],old['free'],{x:ring.val(y)for x,y in ALIASES.items()});after=ring.run(poly,free)
  need(before[old['output']]==after[out],'whole polynomial graph identity without cuts');counts['complete_graph_identities']+=1
  for n,o,a,b in rows:need(before[n]==after[n],'every retained actual gate expression');counts['retained_gate_identities']+=1
  for r in ordinary:need(before[r]==after[r],'entire retained square residual');counts['retained_square_residuals']+=1
  for g in guards:need(before[g]==after[g],'entire retained guard');counts['retained_guards']+=1
  for r in bindings:need(before[r]==(),'removed binding identically zero');counts['zero_bindings']+=1
  M,A,d=ledger(poly,free,[out]);cm,ca,cd=ledger(rows,free,[t['port']for t in terms]);om,oa,_=ledger(old['polynomial_source'],old['free'],[old['output']]);ocm,oca,_=ledger(old['source'],old['free'],[t['port']for t in old['finalizer_terms']])
  need((om-M,oa-A,ocm-cm,oca-ca)==(3,6,0,3),'complete and certificate paid saving')
  need((M,A)==((3*N*N+81*N-52)//2,(3*N*N+(127-2*int(cleanup))*N-88)//2),'full general count')
  need(p['polynomial_ledger']==dict(M=M,A=A,operations=M+A,degree_upper_bound=d,all_live=True)and p['certificate_ledger']==dict(M=cm,A=ca,operations=cm+ca,degree_upper_bound=cd,all_live=True),'current whole/certificate ledgers')
  need(len(free)-3==p['witnesses']==12*N-8 and p['squared_residual_count']==len(ordinary)==7*N-3 and p['unsquared_guard_count']==len(guards)==N and p['nonnegative_term_count']==len(terms)==8*N-3,'full interface and term formula')
  coefficients=diagonal(poly,free)[out];oldcoeff=diagonal(old['polynomial_source'],old['free'])[old['output']]
  degree=6 if N==1 else 10*N-8;leading=17 if N==1 else 8*2**(10*(N-1))+2**(8*(N-1))
  need(coefficients==oldcoeff,'entire diagonal polynomial survives variable identification');counts['full_diagonal_identities']+=1
  need(d==p['exact_degree']==len(coefficients)-1==degree and coefficients[-1]==leading==p['degree_certificate']['diagonal_leading_coefficient'],'exact upper bound attained')
  need(p['full_polynomial_graph_identity']is True and p['natural_zero_bijection']is True and p['unconditional_natural_restoration']is True and p['sos_finalizer']is False and exact(p['parent_pins'],PARENT),'current exact scope/provenance')
  counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A;counts['exact_degrees']+=1
  for case in range(8):
   v={n:rng.randrange(5)if case<3 else rng.randrange(-3,5)for n in free}
   if case==7:v={n:Fraction(x,5)for n,x in v.items()};counts['rational_identities']+=1
   restored=dict(v,**{x:v[y]for x,y in ALIASES.items()});value=numeric(poly,v)[out]
   need(numeric(old['polynomial_source'],restored)[old['output']]==value,'full numeric graph identity');counts['numeric_identities']+=1
   if case<7:need(mod.evaluate(p,v,signed=case>=3,root=root)==value and exact(mod.restore_assignment(p,v,signed=case>=3,root=root),restored),'public graph/evaluation')
   if case<3:need(min(restored.values())>=0,'unconditional natural restoration');counts['unconditional_natural_restorations']+=1
  fixtures=[parent_zero(old)]
  if N==1:fixtures.extend([parent_zero(old,1),parent_zero(old,2)])
  if N>=3:fixtures.extend([parent_zero(old,3),parent_zero(old,4)])
  for v in fixtures:
   q={n:v[n]for n in free};need(exact(mod.project_parent_zero(p,v,root=root),q)and mod.evaluate(p,q,root=root)==0,'complete natural zero projection')
   need(exact(mod.restore_assignment(p,q,root=root),v),'full zero inverse');counts['natural_zero_bijections']+=1
  results.append(dict(N=N,cleanup=cleanup,M=M,A=A,operations=M+A,witnesses=p['witnesses'],squares=len(ordinary),guards=N,exact_degree=degree,diagonal_leading_coefficient=leading,coefficient_sha256=sha(json.dumps(coefficients,separators=(',',':')).encode())))
 # The previous real-witness obstruction is still an actual full zero after aliases.
 p=mod.build(1,root=root);old=olds[1,True];v={n:Fraction(0)for n in p['free']};v.update(program=Fraction(1),r0_t2=Fraction(1,2));restored=dict(v,**{x:v[y]for x,y in ALIASES.items()})
 need(numeric(p['polynomial_source'],v)[p['output']]==numeric(old['polynomial_source'],restored)[old['output']]==0,'inherited nonnegative-real false evaluation remains');counts['inherited_rational_boundary']=1
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed API accepted')
 for N in(True,False,0,-1,9,1.0,'1',None):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,N=N:fn(N,root=root))
 for c in(0,1,None,'true'):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,c=c:fn(2,cleanup=c,root=root))
 p=mod.build(2,root=root);old=olds[2,True];v={n:0 for n in p['free']};zero=parent_zero(old)
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:mod.checked(q,root=root))
 for key in('N','witnesses','squared_residual_count','unsquared_guard_count','nonnegative_term_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('full_polynomial_graph_identity','natural_zero_bijection','unconditional_natural_restoration','sos_finalizer','cleanup'):
  q=copy.deepcopy(p);q[key]=int(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('free','source','polynomial_source','root_binding_map','finalizer_terms'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['root_aliases']['r0_x']='argument';reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['finalizer_terms'][0]['kind']='square';reject(lambda:mod.checked(q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:mod.checked(q,root=root))
 for key in old:
  q=copy.deepcopy(old);del q[key];reject(lambda q=q:mod.rewrite(q,root=root))
 for val in(True,0.0,Fraction(0),-1):
  bad=dict(v,program=val)
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for bad in({},dict(v,extra=0),list(v)):
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for mode in(0,1,None):
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,mode=mode:fn(p,v,signed=mode,root=root))
 for bad in({n:0 for n in old['free']},dict(zero,program=True),dict(zero,program=0.0),dict(zero,extra=0),dict(zero,program=1)):
  reject(lambda bad=bad:mod.project_parent_zero(p,bad,root=root))
 for key,val in p.items():
  if type(val)in(dict,list):
   q=mod.build(2,root=root);q[key].clear();need(exact(mod.build(2,root=root),p),'fresh mutable field');counts['copies']+=1
 for fn in(lambda:mod.canonical_parent(2,root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(mod.build(2,root=root),p)and exact(mod.canonical_parent(2,root=root),old),'canonical accessor copy');counts['copies']+=1
 q=mod.polynomial_source(p,root=root);q.clear();need(exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'source copy');counts['copies']+=1
 q=mod.restore_assignment(p,v,root=root);q['program']=99;need(v['program']==0,'restoration copy');counts['copies']+=1
 q=mod.project_parent_zero(p,zero,root=root);q['program']=99;need(zero['program']==0,'projection copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='root_projection_independent_')as temp:
  temp=Path(temp)
  for n,b in raw.items():(temp/n).write_bytes(b)
  mod.build(2,root=temp)
  for n,b in raw.items():
   (temp/n).write_bytes(b+b'\n')
   for fn in(lambda:mod.build(2,root=temp),lambda:mod.canonical_parent(2,root=temp),lambda:mod.rewrite(old,root=temp),lambda:mod.checked(p,root=temp),lambda:mod.polynomial_source(p,root=temp),lambda:mod.evaluate(p,v,root=temp),lambda:mod.restore_assignment(p,v,root=temp),lambda:mod.project_parent_zero(p,zero,root=temp)):reject(fn);counts['warm_pins']+=1
   (temp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(path)],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and'Run without -O'in proc.stderr,'optimized reject');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_TREE_DIRECT_ROOT_PROJECTION',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PARENT,author_pins=AUTHOR,counts=counts,forms=results,scope='All16 complete direct-root sources, full graph identity and natural zero bijection with immediate leaf-tag parent, unconditional natural restoration, exact degrees and full guarded API. External finiteN1..8; no universal fixed-arity/compiler/decoder claim.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact saved independent receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()

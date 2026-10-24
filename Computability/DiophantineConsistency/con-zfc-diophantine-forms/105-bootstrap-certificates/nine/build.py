from pathlib import Path
import json,collections,hashlib
ROOT=Path(__file__).resolve().parent
BASE=ROOT
class DAG:
 def __init__(self):self.nodes=[];self.memo={};self.names={}
 def node(self,k,**kw):
  ky=(k,*sorted(kw.items()))
  if ky not in self.memo:self.memo[ky]=len(self.nodes);self.nodes.append(dict(kind=k,**kw))
  return self.memo[ky]
 def c(self,x):return self.node('literal',value=x)
 def v(self,x):return self.node('variable',name=x)
 def f(self,x):return self.node('fixed',name=x)
 def b(self,k,x,y):
  if self.nodes[x]['kind']=='literal' and self.nodes[y]['kind']=='literal':
   a,b=self.nodes[x]['value'],self.nodes[y]['value'];return self.c(a+b if k=='add' else a-b if k=='sub' else a*b)
  if k=='mul':
   if self.nodes[x]==dict(kind='literal',value=1):return y
   if self.nodes[y]==dict(kind='literal',value=1):return x
   if self.nodes[x]==dict(kind='literal',value=0) or self.nodes[y]==dict(kind='literal',value=0):return self.c(0)
  if k=='add':
   if self.nodes[x]==dict(kind='literal',value=0):return y
   if self.nodes[y]==dict(kind='literal',value=0):return x
  if k=='sub':
   if x==y:return self.c(0)
   if self.nodes[y]==dict(kind='literal',value=0):return x
  if k in ['add','mul'] and x>y:x,y=y,x
  return self.node(k,left=x,right=y)
 def add(self,*xs):
  z=self.c(0)
  for x in xs:z=self.b('add',z,x)
  return z
 def sub(self,x,y):return self.b('sub',x,y)
 def mul(self,*xs):
  z=self.c(1)
  for x in xs:z=self.b('mul',z,x)
  return z
 def sq(self,x):return self.mul(x,x)
 def save(self,n,x):self.names[n]=x;return x
 def export(self,o):
  live=set()
  def walk(i):
   if i in live:return
   live.add(i);n=self.nodes[i]
   if 'left' in n:walk(n['left']);walk(n['right'])
  walk(o);order=sorted(live);rr={v:i for i,v in enumerate(order)};ns=[]
  for k in order:
   n=self.nodes[k].copy()
   if 'left'in n:n['left']=rr[n['left']];n['right']=rr[n['right']]
   ns.append(n)
  counts=dict(collections.Counter(n['kind'] for n in ns if n['kind'] in ['add','sub','mul']))
  return dict(nodes=ns,output=rr[o],named_nodes={k:rr[v] for k,v in self.names.items() if v in live},operation_counts=counts,total_operations=sum(counts.values()),variables=[n['name'] for n in ns if n['kind']=='variable'])
def build(parent,source,variant='laurent'):
 d=DAG();c,add,sub,mul,sq,N=d.c,d.add,d.sub,d.mul,d.sq,d.save
 env={};Cvar=None
 def clone(i):
  if i in env:return env[i]
  n=parent['nodes'][i];k=n['kind']
  if k=='literal':z=c(n['value'])
  elif k=='fixed':z=d.f(n['name'])
  elif k=='variable':z=add(d.v('c'),c(1)) if n['name']=='C' else d.v(n['name'])
  else:z=d.b(k,clone(n['left']),clone(n['right']))
  env[i]=z;return z
 wanted=['A','B1','C','J','V0','a0','Omega','E0','R','N','capbase','B','Gsource','Usource','ell','targets']
 reg={k:N(k,clone(parent['named_nodes'][k])) for k in wanted}
 A,C,J=reg['A'],reg['C'],reg['J'];ii=d.v('i');jj=d.v('j')
 am=N('Am1',sub(sq(A),c(1)));C2=N('C2',sq(C));D=N('D',add(c(1),mul(am,C2)))
 iiC2=N('iC2',mul(ii,C2));e0=N('e0',mul(iiC2,J));F=N('F',add(c(1),mul(mul(am,D),sq(e0))))
 Lam=N('Lambda',sub(add(c(1),mul(C,D)),A));G=N('G',add(A,mul(F,Lam)))
 Z=N('Z',add(reg['B1'],mul(sub(jj,c(1)),C)));H=N('H',add(C,mul(F,Z)));GH=N('GH',mul(G,H))
 I=N('I',add(c(1),sub(sq(GH),sq(H))));raw=N('raw_a1',mul(D,F,I));a1=N('a1',mul(c(4),raw))
 TT=N('Tmajor',mul(iiC2,add(mul(A,J,sub(mul(c(2),D),C2)),sub(mul(c(3),C2),c(4)))))
 V1=N('V1',mul(TT,GH));Omega,E0,V0,a0=[reg[k] for k in ['Omega','E0','V0','a0']]
 theta=N('Theta',sub(E0,mul(Omega,add(V0,V1))));theta2=N('Theta2',sq(theta));omega2=N('Omega2',sq(Omega))
 inn=N('polar_inner',add(theta2,mul(omega2,sub(a0,a1))));out=N('output',sub(sq(inn),mul(c(4),omega2,a0,theta2)))
 obj=d.export(out);obj.update(source=source,construction='positive C successor and local Laurent majorant',domain='strictly positive integers',parent_source_hash=hashlib.sha256(json.dumps(parent,sort_keys=True,separators=(',',':')).encode()).hexdigest())
 obj['prefix_map']={str(i):v for i,v in env.items()}
 obj['fixed_binding']=parent.get('fixed_binding')
 obj['coefficient_recipes']=parent.get('coefficient_recipes')
 return obj
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
 args.output.mkdir(parents=True,exist_ok=True)
 for label,degree in [('compact2082',1520186),('h1868',1376378)]:
  par=json.loads((ROOT/'parents'/(label+'.json')).read_text());o=build(par,'parents/'+label+'.json');o.pop('prefix_map')
  o.update(exact_degree=degree,fixed_binding='fixed/'+label+'/BINDING.json',source_parameters=json.loads((ROOT/'fixed'/label/'BINDING.json').read_text())['source_parameters'],variables=['b','g','h','s','w','c','i','j','n'],proof='PROOF.md')
  (args.output/(label+'.json')).write_text(json.dumps(o,indent=2)+'\n')
  print(label,o['total_operations'],o['exact_degree'])

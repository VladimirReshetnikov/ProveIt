import json,collections,pathlib
HERE=pathlib.Path(__file__).resolve().parent
SRC=HERE/'provenance'
class DAG:
 def __init__(self):self.nodes=[];self.cache={}
 def node(self,*a):
  if a[0] in ['add','mul'] and a[1]>a[2]:a=(a[0],a[2],a[1])
  if a not in self.cache:self.cache[a]=len(self.nodes);self.nodes.append(list(a))
  return self.cache[a]
 def i(self,x):return self.node('integer',x)
 def add(self,a,b):return self.node('add',a,b)
 def sub(self,a,b):return self.node('sub',a,b)
 def mul(self,a,b):return self.node('mul',a,b)
 def scale(self,k,a):return self.mul(self.i(k),a)
 def sq(self,a):return self.mul(a,a)
 def copy(self,d,end,decouple=False,reduce_k=False,scale_only=False,radical_scale=False):
  rem={}
  for i,n in enumerate(d['nodes'][:end]):
   if decouple and i==83:n=['mul',81,4]
   if (decouple or scale_only) and i==111:n=['mul',82,39 if radical_scale else 110]
   if reduce_k and i in range(103,108):n={103:['mul',31,30],104:['mul',38,8],105:['sub',103,104],106:['mul',30,105],107:['sub',106,31]}[i]
   rem[i]=self.node(n[0],*(rem[j] for j in n[1:])) if n[0] in ['add','sub','mul'] else self.node(*n)
  return {k:rem[v] for k,v in d['named_registers'].items() if v in rem}
 def finish(self,r,out,name):
  live=set()
  def visit(i):
   if i in live:return
   live.add(i)
   if self.nodes[i][0] in ['add','sub','mul']:
    for j in self.nodes[i][1:]:visit(j)
  visit(out);rem={v:i for i,v in enumerate(sorted(live))};nn=[]
  for j in sorted(live):
   n=self.nodes[j];nn.append([n[0],*(rem[v] for v in n[1:])] if n[0] in ['add','sub','mul'] else n)
  cnt=collections.Counter(n[0] for n in nn if n[0] in ['add','sub','mul']);degs=[]
  for n in nn:degs.append(1 if n[0]=='variable' else 0 if n[0] in ['integer','coefficient'] else sum(degs[j] for j in n[1:]) if n[0]=='mul' else max(degs[j] for j in n[1:]))
  d={'schema':'literal_integer_arithmetic_dag_v1','name':name,'variables':parent['variables'],'variable_count':12,'domain':'unrestricted integers','nodes':nn,'output':rem[out],'named_registers':{k:rem[v] for k,v in r.items() if v in rem},'operations':sum(cnt.values()),'operation_counts':dict(cnt),'syntactic_bound':degs[rem[out]],'exact_degree':(768 if 'combined' in name else 800) if 'radical' in name else 1120 if 'combined' in name else (1152 if 'doubled' in name or 'rational' in name else 1168) if 'scale' in name else 1184 if 'doubled' in name or 'rational' in name else 1200,'coefficient_binding':parent['coefficient_binding'],'proof_status':'Ordinary zero-existence reduction; inherited calibrated finite-refutation endpoint. See PROOF.md and ../radicals/PROOF.md. No new proof-assistant endpoint.','ordinary_proof':'PROOF.md'}
  (HERE/('equation_reduced.json' if 'reduced' in name else 'equation.json')).write_text(json.dumps(d,indent=2)+'\n');print(name,d['operations'],d['syntactic_bound'],cnt)
  print({k:degs[v] for k,v in d['named_registers'].items() if k in ['S','Bcenter','Lcenter','center_defect','q0','v0','n0','n1','output']})
  return d

def norm(d,r,Z,a,b,e,c,q0=None,delta=None):
 add,sub,mul,sq,scale=d.add,d.sub,d.mul,d.sq,d.scale
 z2=sq(Z);ze=add(z2,e);qm2=scale(-2,Z);ab=add(a,b)
 if delta is None:
  q0=q0 if q0 is not None else sub(sub(ze,ab),c);q1=qm2;ap=mul(a,b);cp=c
 else:
  q0=q0 if q0 is not None else sub(mul(delta,sub(ze,ab)),c);q1=mul(delta,qm2);ap=mul(mul(a,sq(delta)),b);cp=mul(delta,c)
 v0=sub(add(sq(q0),mul(mul(e,q1),q1)),scale(4,add(ap,mul(cp,ab))))
 v1=mul(q1,scale(2,q0));z64=mul(cp,scale(64,ap))
 n0=sub(add(sq(v0),mul(mul(e,v1),v1)),mul(ze,z64))
 n1=sub(mul(v1,scale(2,v0)),mul(qm2,z64))
 out=sub(sq(n0),mul(mul(e,n1),n1));r.update(q0=q0,v0=v0,n0=n0,n1=n1,output=out)
 return out
parent=json.loads((SRC/'scalar_parent.json').read_text())
for variant in ['radical_combined_integral_shift_min','radical_combined_integral_shift_reduced']:
 d=DAG();r=d.copy(parent,123,decouple='combined' in variant,reduce_k=variant.startswith(('combined','scale','radical')),scale_only=variant.startswith(('scale','radical')),radical_scale=variant.startswith('radical'));add,sub,mul,sq,scale=d.add,d.sub,d.mul,d.sq,d.scale
 S,S2,Q,V,delta,A,n=(r[k] for k in ['S','S2','Q','V','delta','Acarrier','n'])
 B=sub(mul(S,n),A);r['Bcenter']=B
 a=mul(scale(9,S2),r['Df']);b=mul(scale(81,S2),r['Dt']);e=mul(scale(729,S2),r['Dg'])
 q0=None;delarg=None
 if 'rational' in variant:
  center=V;c=mul(S2,r['Cy']);delarg=delta
  Z=sub(mul(S,add(n,center)),A)
  if 'reduced' in variant:
   L=mul(S,V);Z=add(B,L)
   q0=add(mul(delta,add(add(sq(B),scale(2,mul(L,B))),sub(e,add(a,b)))),mul(S2,sub(d.i(1),sq(V))))
 elif 'doubled' in variant:
  center=sub(scale(2,mul(Q,V)),V);Z=sub(mul(S,add(n,center)),A)
  c=scale(4,mul(mul(S2,r['Cy']),delta))
  if 'shared' in variant:
   V2=scale(2,V);QV2=mul(Q,V2);center=sub(QV2,V);Z=sub(mul(S,add(n,center)),A);c=mul(mul(S2,sub(mul(V2,QV2),d.i(4))),delta)
  if 'reduced' in variant:
   L=mul(S,center);Z=add(B,L);E=mul(S2,add(sq(V),scale(4,delta)))
   c=sub(sq(L),E);q0=add(add(sq(B),scale(2,mul(L,B))),add(E,sub(e,add(a,b))))
   r.update(Lcenter=L,center_defect=E)
 else:
  center=mul(Q,V);Z=sub(mul(S,add(n,center)),A);c=mul(mul(S2,r['Cy']),delta)
  if 'reduced' in variant:
   L=mul(S,center);Z=add(B,L);E=mul(S2,sub(mul(Q,add(sq(V),d.i(1))),d.i(1)))
   c=sub(sq(L),E);q0=add(add(sq(B),scale(2,mul(L,B))),add(E,sub(e,add(a,b))))
   r.update(Lcenter=L,center_defect=E)
 r.update(center=Z,ra=a,rb=b,re=e,rn=c)
 out=norm(d,r,Z,a,b,e,c,q0,delarg);d.finish(r,out,variant)

"""Authored literal nine-variable composition. Adapted to the coherent compact54-sharp tuple; only JSON/gzip inputs are read."""
from pathlib import Path
from functools import lru_cache
import json,gzip,hashlib,collections
ROOT=Path(__file__).resolve().parent
VARS=['b','g','h','s','w','C','i','j','n']
class Circuit:
 def __init__(self):self.nodes=[];self.memo={};self.names={}
 def node(self,kind,**kw):
  key=(kind,*sorted(kw.items()))
  if key not in self.memo:self.memo[key]=len(self.nodes);self.nodes.append(dict(kind=kind,**kw))
  return self.memo[key]
 def lit(self,v):return self.node('literal',value=v)
 def var(self,n):return self.node('variable',name=n)
 def fixed(self,n):return self.node('fixed',name=n)
 def islit(self,x,v):return self.nodes[x]=={'kind':'literal','value':v}
 def binary(self,k,a,b):
  if k=='mul':
   if self.islit(a,0) or self.islit(b,0):return self.lit(0)
   if self.islit(a,1):return b
   if self.islit(b,1):return a
  if k=='add':
   if self.islit(a,0):return b
   if self.islit(b,0):return a
  if k=='sub':
   if a==b:return self.lit(0)
   if self.islit(b,0):return a
  if k in ('add','mul') and a>b:a,b=b,a
  return self.node(k,left=a,right=b)
 def add(self,*xs):
  out=self.lit(0)
  for x in xs:out=self.binary('add',out,x)
  return out
 def mul(self,*xs):
  out=self.lit(1)
  for x in xs:out=self.binary('mul',out,x)
  return out
 def sub(self,a,b):return self.binary('sub',a,b)
 def power(self,a,n):
  if n<0:raise ValueError('negative power')
  if n==0:return self.lit(1)
  if n==1:return a
  u=self.power(a,n//2);u=self.mul(u,u)
  return self.mul(u,a) if n%2 else u
 def save(self,n,v):self.names[n]=v;return v
 def export(self,out):
  live=set()
  def visit(i):
   if i in live:return
   live.add(i);n=self.nodes[i]
   if n['kind'] in ('add','sub','mul'):visit(n['left']);visit(n['right'])
  visit(out);order=sorted(live);ren={v:i for i,v in enumerate(order)};nodes=[]
  for i in order:
   n=self.nodes[i].copy()
   if 'left'in n:n['left']=ren[n['left']];n['right']=ren[n['right']]
   nodes.append(n)
  return dict(nodes=nodes,output=ren[out],named_nodes={n:ren[v] for n,v in self.names.items() if v in ren})

def build(refined=True,natural=False,powmode='binary',profile='H2068'):
 data=ROOT/'data'/profile
 code=json.loads((data/'layout.json').read_text());ks=json.loads((data/'kernels.json').read_text())
 ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients/compact_tuple'/f'{n}.bin.gz').read_bytes()),'little') for n in ['beta','K','MC','MF_source']]
 d=Circuit();c=d.lit;a=d.add;m=d.mul;s=d.sub;p=d.power;save=d.save
 vs={v:d.var(v) for v in VARS}
 if natural:
  for v in VARS:
   if v!='j':vs[v]=a(vs[v],c(1))
 else:vs['j']=s(vs['j'],c(1))
 fixed={};recipes={}
 def coef(terms):
  rec=sorted([(tuple(t.get('port_powers',t.get('powers'))),t.get('integer',t.get('coefficient'))) for t in terms])
  if len(rec)==1 and not any(rec[0][0]):return c(rec[0][1])
  key=json.dumps(rec)
  if key not in recipes:
   name='c_'+hashlib.sha256(key.encode()).hexdigest()[:16];value=sum(z*__import__('math').prod(q**e for q,e in zip(ports,ex)) for ex,z in rec)
   recipes[key]=(name,rec);fixed[name]=value
  return d.fixed(recipes[key][0])
 # Coherent compact54-sharp tuple; all85 weighted coefficients are certified separately.
 kap=864026;b=save('b',vs['b']);fixed['base_scale']=1<<kap
 B=save('B',m(d.fixed('base_scale'),p(b,2)));known={0:c(1),1:B}
 W=max(code['weights']);height=max(max(t['exponent'] for t in r['terms'])+r['degree']*W for r in ks['kernels']);Ec=height+W+2
 hp=Ec+W+23;delta=(hp-15)%2;lp=(22-hp*kap)%2;ne=(hp-15-delta)//2;ce=((15+delta)*kap+lp-22)//2
 required=set(code['weights'])|{1,W+1,Ec,ne,W}
 for xs in [[t['exponent'] for t in r['terms']] for r in ks['kernels']]+[code['targets']]:
  ex=sorted(set(xs));required.add(ex[0]);required.update(b-a for a,b in zip(ex,ex[1:]))
 plan={};todo=required-{0}
 while len(todo)>1:
  aa=max(todo);bb=max(todo-{aa});todo.remove(aa)
  pairs=[(v,aa-v) for v in todo if aa-v in todo]
  if pairs:x,y=min(pairs,key=lambda t:abs(t[0]-t[1]))
  elif 2*bb<aa:
   x,y=(aa//2,aa//2) if aa%2==0 else (aa-1,1)
  else:x,y=bb,aa-bb
  plan[aa]=(x,y);todo.update([x,y])
 @lru_cache(None)
 def bp(e):
  if e<0:raise ValueError('negative source exponent')
  if powmode=='binary':return p(B,e)
  if e in known:return known[e]
  if powmode=='global':
   x,y=plan[e];known[e]=m(bp(x),bp(y));return known[e]
  pairs=[(i,e-i) for i in known if i and e-i and e-i in known]
  if pairs:
   i,j=min(pairs,key=lambda ij:(abs(ij[0]-ij[1]),ij[0]));out=m(known[i],known[j])
  else:
   t=bp(e//2);out=m(t,t)
   if e%2:out=m(out,B)
  known[e]=out;return out
 def sparse(terms):
  groups=collections.defaultdict(list)
  for e,z in terms:groups[e].append(z)
  tt=sorted((e,a(*zs)) for e,zs in groups.items());ex,out=tt.pop()
  while tt:
   ex2,z=tt.pop();out=a(m(out,bp(ex-ex2)),z);ex=ex2
  return m(out,bp(ex))
 kernels={r['degree']:save('Dcode'+str(r['degree']),sparse([(t['exponent'],coef(t['coefficient'])) for t in r['terms']])) for r in ks['kernels']}
 W=max(code['weights']);height=max(max(t['exponent'] for t in r['terms'])+r['degree']*W for r in ks['kernels']);Ec=height+W+2
 ell=save('ell',a(*(bp(x) for x in code['weights'])));targets=save('targets',sparse([(x,c(1)) for x in code['targets']]))
 N0=save('N0',bp(W+1));mask=save('mask',s(s(N0,c(1)),m(s(b,c(1)),ell)))
 Tc=save('Tcode',a(mask,m(s(B,c(2)),targets,N0)))
 Us=save('Usource',a(ell,vs['g']));Gs=save('Gsource',a(m(a(m(kernels[2],Us),kernels[1]),Us),kernels[0]))
 Jc=save('Jcode',a(m(c(2),Gs),targets));Sc=save('Scode',a(vs['g'],m(N0,Jc)))
 hp=Ec+W+23;delta=(hp-15)%2;lp=(22-hp*kap)%2;ne=(hp-15-delta)//2;ce=((15+delta)*kap+lp-22)//2
 threshold_name='threshold_'+str(ce);fixed[threshold_name]=1<<ce
 L=save('L',m(c(1<<lp),b,bp(Ec)));N=save('N',m(d.fixed(threshold_name),p(b,delta),bp(ne)))
 R=save('R',s(s(m(L,a(Sc,Tc,c(1))),Sc),c(1)));cap=save('capbase',m(b,bp(W)))
 U=save('U',m(p(N,2),vs['w']));Y=save('Y',m(p(N,2),vs['s']));M=save('M',m(R,Y));P=save('P',m(c(2),p(M,2),U))
 K=save('K',a(R,c(1),m(vs['h'],s(P,c(1)))));A=save('A',m(M,a(U,c(1))));B1=save('B1',a(m(c(2),R),c(1)));W1=save('W1',m(b,vs['w']));C=save('C',vs['C'])
 J=save('J',s(m(c(4),A),c(5)));Q=save('Q',a(m(W1,s(m(c(3),C),m(c(2),W1))),c(2)))
 am1=s(p(A,2),c(1));D=save('D',a(m(am1,p(C,2)),c(1)));k=save('k',m(vs['i'],J,C));E=save('E',m(k,D,C))
 F=save('F',a(m(am1,p(E,2)),c(1)));lam=save('Lambda',s(a(m(C,D),c(1)),A));G=save('G',a(A,m(F,lam)));H=save('H',a(C,m(F,a(B1,m(vs['j'],C)))))
 GH=save('GH',m(G,H));I=save('I',a(s(p(GH,2),p(H,2)),c(1)));V0=save('V0',m(P,K));a0=save('a0',a(s(p(V0,2),p(K,2)),c(1)));a1=save('a1',m(D,F,I))
 margin=save('margin',s(m(p(K,2),s(m(c(4),cap),vs['g'])),m(c(16),cap,p(s(C,m(K,Y)),2))))
 B8=s(s(m(c(8),p(D,2)),m(c(4),D)),c(1))
 if refined:
  ns=a(m(c(2),G),lam)
  t6=m(k,a(s(m(c(128),B8,ns),m(p(k,2),s(m(c(16),a(B8,D)),c(8)),lam)),m(C,s(m(c(14),p(k,2)),c(192)))))
  correction=a(m(C,s(m(C,s(m(c(576),A),c(2151))),a(s(m(c(896),p(A,2)),m(c(4256),A)),c(8442)))),c(1024))
  T=save('Tmajor',a(t6,m(p(vs['i'],3),correction),m(c(288),vs['i']),c(2048)));V1=save('V1',m(T,H));q=2048**2
 else:T=save('Tmajor',m(k,B8));V1=save('V1',m(T,GH));q=64
 Om=save('Omega',m(J,margin));E0=save('E0',a(m(J,a(vs['n'],p(W1,2))),Q));theta=save('Theta',s(E0,m(Om,a(V0,V1))))
 inner=save('inner',s(p(theta,2),m(p(Om,2),a(a0,m(c(q),a1)))));out=save('F9',s(p(inner,2),m(c(4*q),p(Om,4),a0,a1)))
 obj=d.export(out);counts=collections.Counter(n['kind'] for n in obj['nodes'] if n['kind'] in ('add','sub','mul'))
 obj.update(variables=VARS,domain='natural' if natural else 'positive',refined_majorant=refined,total_operations=sum(counts.values()),operation_counts=dict(counts),power_method=powmode,profile=profile,W=W,height=height,Ecode=Ec,base_scale_exponent=kap,threshold_b_power=delta,threshold_B_power=ne,threshold_scale_exponent=ce,block_scale_power_of_two=lp,source_sha256=ks['source_sha256'],layout_sha256=hashlib.sha256((data/'layout.json').read_bytes()).hexdigest(),coefficient_recipes=[dict(name=n,terms=[dict(port_powers=e,integer=v) for e,v in rr]) for n,rr in recipes.values()])
 return obj,fixed

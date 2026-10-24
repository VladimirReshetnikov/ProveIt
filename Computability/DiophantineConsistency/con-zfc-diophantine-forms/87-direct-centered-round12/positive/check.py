"""Independent arithmetic and finite checks, not a consistency or kernel proof."""
import json,pathlib,random,collections,gzip,hashlib,math
P=pathlib.Path(__file__).resolve().parent
out={}
def need(c,s):
 if not c:raise RuntimeError(s)
def evaluate(x,e):
 e=dict(e)
 for d,o,a,b in x['source']:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[d]=a+b if o=='+' else a-b if o=='-' else a*b
 return e
for name,n in [('p11_degree211.json',113),('p12_degree70.json',100)]:
 x=json.loads((P/name).read_text()); names=set(x['witnesses']+x['fixed_numerals']); deps={}
 for d,o,a,b in x['source']:
  need(d not in names and all(isinstance(v,int) or v in names for v in(a,b)),'topology')
  need(o in ('+','-','*'),'operation');names.add(d);deps[d]=[v for v in(a,b) if isinstance(v,str)]
 live=set();todo=[x['output']]
 while todo:
  v=todo.pop()
  if v not in live:live.add(v);todo+=deps.get(v,[])
 need(len(x['source'])==n and all(r[0] in live for r in x['source']),'live count')
 out[name]={'operations':n,'breakdown':dict(collections.Counter(r[1] for r in x['source']))}
rng=random.Random(12211);x=json.loads((P/'p11_degree211.json').read_text())
for _ in range(300):
 e=evaluate(x,{k:rng.randrange(1,12) for k in x['witnesses']+x['fixed_numerals']})
 q=e['q'];a=e['a'];I=e['I'];Told=e['T']+q+e['alpha'];M=e['M'];L=e['k']*Told+e['F'];V=e['Df']*(e['c']*Told-e['R'])-e['c'];D=(a+2)*I
 z=M*(e['ell']+e['k']+e['n']+L)+(q-1)*e['Y']-q**3*(1+(q-1)*L)*e['Bt']
 zz=z+M*(V+D);d=e['delta'];A=e['A'];B=e['Bf'];C=e['Cnum']
 center=d*d*((zz*zz-A-B)**2-4*A*B)-2*d*C*(zz*zz+A+B)+C*C
 need(e['Zbar']==zz and e['L']==L,'literal formula')
 need(e['N8']==center*center-64*d**3*A*B*C*zz*zz,'universal norm')
 need(e['P11']==(1+e['N8'])*(1+e['A1'])-1,'finalizer')
 # Exact canceled norm center identity, valid for every substitution.
 h=z*z+2*M*D*z+M*M*(I*I-1)-A;K=d*h-M*M*(V*V-1)
 c2=K*K+4*d*M*V*(z+M*D)*K+4*d*d*M*M*V*V*h-4*d*M*M*V*V*(A+B)-4*d*d*A*B+4*d*M*M*(A+B)
 need(center==c2,'double-centered cancellation')
out['independent_norm_and_center_cases']=300
for _ in range(300):
 beta=rng.randrange(10,40);j=rng.randrange(1,5);q=beta*(3*j+1)+1
 inp={k:rng.randrange(1,30) for k in x['witnesses']};inp.update(beta=beta,j=j,K0=rng.randrange(1,30),MC=rng.randrange(1,beta),MF=rng.randrange(1,2*beta),Y=q**3*rng.randrange(1,5))
 e=evaluate(x,inp);q=e['q'];c=e['c'];V=e['V'];d=e['delta'];Q=e['Q'];L=e['L'];Df=e['Df'];D=e['Dcenter'];I=e['I']
 need(e['R']<q**3*(q+e['alpha']) and e['R']>-e['F']*q**3,'mask estimates')
 need(e['g50']>c*e['T'] and V>1 and L>e['k'],'positive bootstrap')
 need(d>(e['Delta']-1)*Df,'gap denominator')
 need(Q*V*V-1<d*(V+L)**2,'auxiliary gap bound')
 need(D*D>Df and Df>(D-I)**2,'strong gap bound')
out['early_divisibility_gap_cases']=300
# Cofinal orbit arithmetic for small illustrative moduli.
for Q in range(2,10):
 B=(2*Q-1,2*(Q-1),2*Q,2*Q-1)
 for m in range(1,7):
  def mul(a,b):return tuple(v%m for v in (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3]))
  cur=(1%m,0,0,1%m);identity=cur;order=0
  while True:
   cur=mul(cur,B);order+=1
   if cur==identity:break
   need(order<10000,'finite-group sample budget')
  V=y=1
  for _ in range(order):V,y=B[0]*V+B[1]*y,B[2]*V+B[3]*y
  need(V>1 and y>V and V%m==1%m and y%m==1%m,'cofinal orbit')
  need(Q*V*V-(Q-1)*y*y==1,'norm preservation')
out['cofinal_orbit_samples']=48
# Literal polynomial degree replay over a finite field on random lines.
p=1000003
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,sgn=1):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]=v
 for i,v in enumerate(b):c[i]=(c[i]+sgn*v)%p
 return trim(c)
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,v in enumerate(a):
  for j,w in enumerate(b):c[i+j]=(c[i+j]+v*w)%p
 return trim(c)
for fn,expect in [('p11_degree211.json',{'Ncenter':99,'N8':198,'A1':13,'P11':211}),('p12_degree70.json',{'A0':15,'A1':13,'N':42,'P12':70})]:
 xx=json.loads((P/fn).read_text())
 for trial in range(6):
  ev={k:[rng.randrange(1,50),rng.randrange(1,50)] for k in xx['witnesses']};ev.update({k:[rng.randrange(1,50)] for k in xx['fixed_numerals']})
  for d,o,a,b in xx['source']:
   a=ev[a] if isinstance(a,str) else [a%p];b=ev[b] if isinstance(b,str) else [b%p]
   ev[d]=add(a,b) if o=='+' else add(a,b,-1) if o=='-' else mul(a,b)
  need(all(len(ev[k])-1==v for k,v in expect.items()),'exact modular line degree '+fn)
  w={k:ev[k][-1] for k in xx['witnesses']};beta=ev['beta'][0];K0=ev['K0'][0]
  q0=(3 if fn.startswith('p11') else 6)*beta*w['j'];k0=w['eta']+w['zeta'];X=w['X'];Y=w['Y'];F=w['F'];al=w['alpha'];g=w['gamma']
  R0=q0**3*(q0-F);Bt0=(K0*q0+X)*(q0-F-al)-q0*F
  if fn.startswith('p11'):
   i=w['i'];Q0=i*i*k0**4*X**4*Y**8;M0=q0**4;V0=-i*i*k0**4*X**2*Y**6*R0;D0=i*k0*k0*X*Y**3;ell0=k0*X*Y*Y;L0=k0*(w['T']+q0+al);z0=M0*(ell0-L0*Bt0)
   nh=64*Q0**4*M0**6*V0**4*D0**2*(z0*z0-M0*M0*ell0*ell0)
   ah=32*q0*q0*k0*X*X*Y**4*(4*q0*q0*Y*g+R0)
   need(ev['N8'][-1]==nh%p and ev['A1'][-1]==ah%p and ev['P11'][-1]==(nh*ah)%p,'leading-form certificate11')
  else:
   ah0=-2*q0**8*k0*k0*X*Y*Y*Bt0;ah1=8*q0*q0*k0*X*X*Y**4*(q0*q0*Y*g+R0);nh=4*k0**8*X**4*Y**12*w['t']**8*R0*R0*w['n']**2
   need(ev['A0'][-1]==ah0%p and ev['A1'][-1]==ah1%p and ev['N'][-1]==nh%p and ev['P12'][-1]==ah0*ah1*nh%p,'leading-form certificate12')

 out[fn]['modular_line_degrees']=expect
# Incoming twelve-variable identity on independently chosen integer tuples.
y=json.loads((P/'p12_degree70.json').read_text())
for _ in range(100):
 e=evaluate(y,{k:rng.randrange(1,10) for k in y['witnesses']+y['fixed_numerals']})
 d=e['c']**4;Q=e['Q'];V=e['V'];n=e['n'];h=(1-Q)*n*n+2*(1-Q)*V*n+V*V-1;bn=2*(1-Q)*(n+V)
 need(e['N']==(d*h+(1-Q)*Q)**2-d*bn*bn*Q,'ordinary norm')
 need(e['P12']==(1+e['A0'])*(1+e['A1'])*(1+e['N'])-1,'ordinary finalizer')
out['ordinary_norm_cases']=100
binding=json.loads((P/'native/ACTIVE_BINDING.json').read_text());nums={}
for k,b in binding['ports'].items():
 rawfile=(P/'native'/b['file']).read_bytes();raw=gzip.decompress(rawfile)
 need(hashlib.sha256(rawfile).hexdigest()==b['sha256_gzip'] and hashlib.sha256(raw).hexdigest()==b['sha256_raw'],'binding hash')
 nums[k]=int.from_bytes(raw,'little');need(nums[k].bit_length()==b['bits'],'binding bits')
need(nums['beta']==2**590069-1 and 0<nums['MC']<nums['beta'] and 0<nums['MF']<2*nums['beta'] and nums['K0']>=1,'actual masks')
out['actual_tuple_verified']=True
out['scope']='Finite tests and exact identities; not a new kernel certificate or finite verification of consistency equivalence.'
(P/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

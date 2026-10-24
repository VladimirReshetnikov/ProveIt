"""Independent compact-formula replay. Only stdlib; no imports from builder."""
import ast,gzip,hashlib,json,random,math
from pathlib import Path
R=Path(__file__).resolve().parent

def need(b,s):
 if not b:raise ValueError(s)
def evaluate(text,v,p):
 def f(x):
  if isinstance(x,ast.Constant) and isinstance(x.value,int):return x.value%p
  if isinstance(x,ast.Name):return v[x.id]%p
  if isinstance(x,ast.UnaryOp) and isinstance(x.op,ast.USub):return -f(x.operand)%p
  if isinstance(x,ast.BinOp):
   a=f(x.left)
   if isinstance(x.op,ast.Pow):
    need(isinstance(x.right,ast.Constant) and isinstance(x.right.value,int) and 0<=x.right.value<=20,'power');return pow(a,x.right.value,p)
   b=f(x.right)
   if isinstance(x.op,ast.Add):return(a+b)%p
   if isinstance(x.op,ast.Sub):return(a-b)%p
   if isinstance(x.op,ast.Mult):return a*b%p
  raise ValueError('unsupported expression')
 return f(ast.parse(text,mode='eval').body)

binding=json.loads((R/'BINDING.json').read_text()); actual={}
for name,data in binding['ports'].items():
 raw=gzip.decompress((R/data['path']).read_bytes())
 need(hashlib.sha256(raw).hexdigest()==data['raw_sha256'],name+' hash')
 actual[name]=int.from_bytes(raw,'little');need(actual[name].bit_length()==data['bits'],name+' bits')
need(actual['beta']==(1<<1064921)-1,'beta')
need(actual['cone_A']==1<<1113 and actual['cone_B']==1<<666104,'cone scales')
need(actual['beta']%3==1,'parity')
for n,h in json.loads((R/'INHERITED_HASHES.json').read_text()).items():need(hashlib.sha256((R/n).read_bytes()).hexdigest()==h,'inherited '+n)

Pos=lambda p,q,r:1+p*p+q*q+r*(r+1)
G=lambda x,y,t:x*y-(t*t-x-y+1)**2

def compact_oct(v,joint=False,pivot=False):
 b,K,MC,MF,A,B=[v[n] for n in ['beta','K0','MC','MF','cone_A','cone_B']]
 J=3*v['J3']+1;q=b*J+1;W=4*(3*v['w3']+1)
 if pivot:
  C=v['C'];F=(K+W)*C-v['z']*(q-1);alpha=q-F-C
 else:F=v['F'];alpha=v['alpha'];C=q-F-alpha
 E,a,c,eta,V,j,h,gamma,tau,f,o,I,r,y=[v[n] for n in ['E','a','c','eta','V','j','h','gamma','tau','f','o','I','r','y']]
 k=1-V+j*c+h*E;X=W*q;H=4*a+3;delta=a*a+4*a+3;D=X+a*c+gamma*H;P=k+E*(c-eta)
 pack=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 rows=[a-E-(2*v['v_scale']+1)*q**3,E+X*(E-a),c-eta+(E-a)*k,tau*tau-P*E*(c-eta)-1,D*D-delta*c*c-1,k-1-h*E-pack]
 if not pivot:rows.append((K+W)*C-F-v['z']*(q-1))
 rows += [V+c-f*o,I-(2*r+1)*c*c,I*I-delta*(f*f-1),I*I*(V*V-y*y)+y*y-1]
 cone=A*F*B*C-(q-A*F-B*C)**2;ez=eta*(k-eta)
 if joint:rows.append(G(cone,ez,v['t'])-Pos(v['p'],v['qpos'],v['rpos']))
 else:rows += [cone-Pos(*(v['cone_pos'+str(i)] for i in [1,2,3])),ez-Pos(*(v['eta_zeta_pos'+str(i)] for i in [1,2,3]))]
 return rows

def compact_sextic(v):
 b,K,MC,MF,A,B=[v[n] for n in ['beta','K0','MC','MF','cone_A','cone_B']]
 J=3*v['J3']+1;q=b*J+1;W=4*(3*v['w3']+1);X=W*q
 F,alpha,E,a,c,eta,zeta,j,h,gamma,tau,f,o,I,r,y,L,D,F2,g=[v[n] for n in ['F','alpha','E','a','c','eta','zeta','j','h','gamma','tau','f','o','I','r','y','L','D','F2','g']]
 C=q-F-alpha;k=eta+zeta;H=4*a+3
 pack=((q-1)*(q-F)+alpha)*L+(MC+q*MF)*J
 cone=A*F*B*C-(q-A*F-B*C)**2
 return [L-q*q+1,a-E-(2*v['v_scale']+1)*q*(L+1),E+X*(E-a),c-eta+(E-a)*k,tau*tau+(2*tau-k)*E*(c-eta)-1,D-X-gamma*H,D*D+2*a*c*D-H*c*c-1,k-1-h*E-pack,(K+W)*C-F-v['z']*(q-1),F2-f*f,f*o-c-c*j+k-1-h*E,g+F2*o*o-2*f*o*c+c*c-y*y,I-(2*r+1)*c*c,I*I-(a*a+4*a+3)*(F2-1),y*y-I*I*g-1,cone-Pos(*(v['cone_pos'+str(i)] for i in [1,2,3])),eta*zeta-Pos(*(v['eta_zeta_pos'+str(i)] for i in [1,2,3]))]

src=json.loads((R/'inherited/quartic38.json').read_text());rng=random.Random(112306);count=0
for name in ['quartic37','quartic37_direct','sextic30','octic26','degree10_25','degree12_24','degree16_23']:
 x=json.loads((R/(name+'.json')).read_text())
 for prime in [1009,10007,1000003]:
  for _ in range(30):
   v={n:rng.randrange(-1000,1001) for n in x['variables']};v.update({n:z%prime for n,z in actual.items()})
   got=[evaluate(s,v,prime) for s in x['residuals']]
   if name.startswith('quartic'):
    old=dict(v);old['u']=0
    if name=='quartic37':old['J']=3*v['J3']+1;old['w_scale']=3*v['w3']+1
    else:old['X']=3*v['X3']-1
    want=[evaluate(s,old,prime) for i,s in enumerate(src['residuals']) if i!=22]
   elif name=='sextic30':want=compact_sextic(v)
   else:want=compact_oct(v,joint=name in ['degree12_24','degree16_23'],pivot=name in ['degree10_25','degree16_23'])
   need(got==[n%prime for n in want],name+' independent literal formula');count+=1

positive=0;signed=0
for x in range(1,101):
 for y in range(1,101):
  n=x+y-1;m=math.isqrt(n);t=min([m,m+1],key=lambda t:abs(t*t-n))
  need(G(x,y,t)>0,'nearest square existence');positive+=1
for x in range(-20,21):
 for y in range(-20,21):
  for t in range(-10,11):
   if G(x,y,t)>0:need(x>0 and y>0,'signed guard soundness')
   signed+=1
receipt={'status':'PASS','literal_signed_modular_cases':count,'nearest_square_positive_pairs':positive,'signed_guard_triples':signed,'payloads':len(actual),'scope':'Finite transcription, actual payload and algebra checks; not unbounded compiler semantics.'}
(R/'CHECK_RESULTS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

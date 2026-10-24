"""Independent, read-only audit of the round11 shortened Lucas circuit.
Only standard-library code; imports no producer/checker modules.
"""
import collections,gzip,hashlib,json,math,pathlib,random,sys
R=pathlib.Path(__file__).resolve().parent; companion='--h1868' in sys.argv; N=R.parent/('lucas_h1868' if companion else 'lucas'); O=R/'inherited'
expected_ops=480 if companion else 481;expected_degree=1245324 if companion else 1248364
def require(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
a=json.loads((N/'integer10.json').read_text());old=json.loads((O/'integer10.json').read_text());nodes=a['nodes'];names=a['named_nodes'];manifest=json.loads((N/'FIXED_COEFFICIENTS.json').read_text())
baseline=json.loads((O/'FIXED_COEFFICIENTS.json').read_text())
for fn,h in json.loads((R/'BASELINE_PIN.json').read_text())['files'].items():require(sha((O/fn).read_bytes())==h,('baseline file',fn))
fixed={};payloads=[]
for name,row in manifest.items():
 g=(N/row['file']).read_bytes();b=gzip.decompress(g)
 require(sha(g)==row['gzip_sha256'] and sha(b)==row['raw_sha256'],('payload hash',name))
 require(b[0] in [0,1],('sign',name));v=int.from_bytes(b[1:],'little')*(-1 if b[0] else 1)
 require(abs(v).bit_length()==row['bit_length'],('bits',name))
 if not companion:require(sha(g)==baseline[name]['gzip_sha256'] and sha(b)==baseline[name]['raw_sha256'],('changed source numeral',name))
 fixed[name]=v;payloads.append({'name':name,'raw_sha256':sha(b),'compressed_sha256':sha(g)})
require(set(fixed)=={n['name'] for n in nodes if n['kind']=='fixed'},'unused or missing coefficient')
if not companion:
 require(nodes[:460]==old['nodes'][:460],'unchanged source and guard prefix')
 for p in ['data/code.json','data/kernels.json']:
  require((N/p).read_bytes()==(O/p).read_bytes(),('changed source',p))
ports=[int.from_bytes(gzip.decompress((N/'data'/f'{k}.bin.gz').read_bytes()),'little') for k in ['beta','K','MC','MF_source']]
for name,recipe in a['fixed_recipes'].items():
 actual=sum(row['coefficient']*math.prod(v**e for v,e in zip(ports,row['powers'])) for row in recipe)
 require(actual==fixed[name],('recipe versus actual leaf',name))
require(fixed['radix']==2**a['base_exponent'],'radix value')
require(fixed['threshold']==2**a['threshold_exponent'],'threshold value')
code=json.loads((N/'data/code.json').read_text());kernels=json.loads((N/'data/kernels.json').read_text())
ops=collections.Counter();degrees=[]
for i,node in enumerate(nodes):
 k=node['kind']
 if k in ['add','sub','mul']:
  u,v=node['left'],node['right'];require(0<=u<i and 0<=v<i,('topology',i));ops[k]+=1
  degrees.append(degrees[u]+degrees[v] if k=='mul' else max(degrees[u],degrees[v]))
 elif k in ['literal','fixed']:degrees.append(0)
 elif k=='variable':degrees.append(1)
 else:raise ValueError(('operator',k))
live=set();todo=[a['output']]
while todo:
 i=todo.pop()
 if i in live:continue
 live.add(i);n=nodes[i]
 if n['kind'] in ['add','sub','mul']:todo.extend([n['left'],n['right']])
require(len(live)==len(nodes),'dead nodes');require(sum(ops.values())==expected_ops,'operation count')
require(degrees[a['output']]==expected_degree,'degree upper bound')
require(degrees[names['A']]==(16384 if companion else 16424),'A degree')
# Actual fixed leaves, not independent indeterminate ports. A nonzero leading
# coefficient after x_i = slope_i*t modulo a prime attains the upper bound.
primes=[1000000007,1000000009,998244353];rng=random.Random(20261024);leading=[]
for p in primes:
 slopes={v:rng.randrange(1,p) for v in a['variables']};values=[]
 for i,n in enumerate(nodes):
  k=n['kind']
  if k=='variable':v=slopes[n['name']]
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  else:
   u,w=n['left'],n['right'];du,dw=degrees[u],degrees[w]
   if k=='mul':v=values[u]*values[w]
   elif du>dw:v=values[u]
   elif dw>du:v=values[w]*(1 if k=='add' else -1)
   else:v=values[u]+(values[w] if k=='add' else -values[w])
  values.append(v%p)
 require(values[a['output']]!=0,('degree attainment',p))
 leading.append({'prime':p,'slopes':slopes,'leading_coefficient':values[a['output']]})
def dag(inp,p):
 vs=[]
 for n in nodes:
  k=n['kind']
  if k=='variable':v=inp[n['name']]
  elif k=='literal':v=n['value']
  elif k=='fixed':v=fixed[n['name']]
  else:
   u,w=vs[n['left']],vs[n['right']];v=u*w if k=='mul' else u+w if k=='add' else u-w
  vs.append(v%p)
 return vs
def prefix(v,inp,p):
 get=lambda n:v[names[n]]
 b=(6*inp['t']+4)%p;g=b*inp['g0']%p;k=b*(3*inp['k0']+2)%p
 B=fixed['radix']*b*b%p;W=max(code['weights']);H=max(t['exponent']+layer['degree']*W for layer in kernels['kernels'] for t in layer['terms'])
 ell=sum(pow(B,w,p) for w in code['weights'])%p;word=(ell+g)%p;ds={}
 for layer in kernels['kernels']:
  z=0
  for term in layer['terms']:
   c=0
   for row in term['coefficient']:
    t=row['coefficient']
    for port,exponent in zip(ports,row['powers']):t=t*pow(port,exponent,p)%p
    c=(c+t)%p
   z=(z+c*pow(B,term['exponent'],p))%p
  ds[layer['degree']]=z
 coded=(ds[2]*word*word+ds[1]*word+ds[0])%p
 target=sum(pow(B,w,p) for w in code['targets_by_row'])%p
 n0=pow(B,W+1,p);nn=pow(B,W+H+2,p);mask=(n0-1-(b-1)*ell)%p
 sc=(g+n0*(2*coded+target))%p;tc=(mask+n0*(B-2)*target-2)%p
 X=(nn*(sc+tc+1)-sc-1)%p;Y=fixed['threshold']*b*pow(B,H+2*W+9,p)%p;cap=b*pow(B,W,p)%p
 L=inp['l']*Y%p;U=2*L*X%p;V=4*g*inp['w']*Y%p;Wb=b*inp['w']%p;A=U*(V+1)%p
 Phalf=(L*X)*U*V%p;K=(X+1+k*(2*Phalf-2))%p
 Q=((Phalf*Phalf-1)*K*K+1)%p
 C=(6*inp['c0']-1)%p
 Delta=(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))%p
 for name,z in [('b',b),('g',g),('k',k),('base',B),('ell',ell),('word',word),('coded',coded),('targets',target),('n0',n0),('nn',nn),('mask',mask),('sc',sc),('tc',tc),('X',X),('Y',Y),('cap',cap),('L',L),('U',U),('V',V),('W',Wb),('A',A),('Phalf',Phalf),('K',K),('Q',Q),('C',C),('Delta',Delta)]:require(get(name)==z,('prefix register',name))
 require(W==a['W'] and H==a['H'],'layout dimensions')
def tail(v,inp,p):
 get=lambda n:v[names[n]]
 A,C,B,xi=get('A'),get('C'),get('B1'),inp['x']*inp['z']
 D=((A*A-4)*C*C+4)%p
 F=(4*(A*A-4)*C**4*D*xi**2+1)%p
 G=(2*(A+2)*(A-2)**2*C**4*D*xi**2-1)%p
 Om=16*C*C*D*xi%p;H=(C+(B-C)*F+Om*F*inp['y'])%p;I=((G*G-1)*H*H+1)%p
 S,T=get('S'),get('T');rho=(T+S*inp['y'])%p;Sig=xi*pow(S,5,p)%p
 Theta=(rho**3-rho*S*S-S**3)*(rho*rho+23*S*S)%p
 seed=get('b')*get('Q')%p;guard=(seed+(9*get('Delta')-3)*(seed*inp['z'])**2)%p
 lucas=D*F*I%p;center=(Sig*inp['m']-Theta)%p
 result=((center*center-Sig*Sig*(guard+lucas))**2-4*Sig**4*guard*lucas)%p
 for n,z in [('D',D),('F',F),('G',G),('Omega',Om),('H',H),('I',I),('Sigma',Sig),('Theta',Theta),('guard',guard),('lucas',lucas),('F10',result)]:require(get(n)==z,('tail register',n))
 return result
for p in primes:
 for j in range(160):
  inp={v:rng.randrange(-10000,10001) for v in a['variables']}
  if j<10:inp[a['variables'][j]]=0
  v=dag(inp,p);prefix(v,inp,p);require(v[a['output']]==tail(v,inp,p),'tail mismatch')
# Universal polynomial/congruence identities over a signed finite grid.
local_count=0
for A in range(-20,21,2):
 if abs(A)<=2:continue
 for C in range(-9,10,2):
  for xi in [-3,-2,-1,1,2,3]:
   D=(A*A-4)*C*C+4;F=4*(A*A-4)*C**4*D*xi*xi+1
   G=(A//2-1)*(F-1)-1;Om=16*C*C*D*xi
   require(2*G==(A-2)*F-A,'G identity')
   require((F-1)%(Om*xi)==0 and (2*G+2)%(Om*xi)==0,'interpolation congruences')
   require(math.gcd(F,Om)==1 and math.gcd(F,D)==1,'coprimality')
   for B,y in [(3,-2),(7,0),(11,3)]:
    H=C+(B-C)*F+Om*F*y;I=(G*G-1)*H*H+1
    require(D>0 and F>0 and I>0,'positivity')
    require(math.gcd(D,I)==math.gcd(F,I)==1,'square separation')
    require((4*I-D)%F==0,'residue identity')
   local_count+=1
# Matrix arithmetic for modular full-residue interpolation diagnostics.
def mm(a,b,m=None):
 c=(a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
 return tuple(x%m for x in c) if m else c
def mp(A,n,m=None):
 a=(A,-1,1,0);r=(1,0,0,1)
 while n:
  if n&1:r=mm(r,a,m)
  a=mm(a,a,m);n//=2
 return r
crt=[]
for A in [4,6,8,10]:
 for modulus_multiple in [1,2,3]:
  B=C=1;d=A;M=4*modulus_multiple*C*C*d;mat=(1,0,0,1)
  for n in range(1,100001):
   mat=mm(mat,(A,-1,1,0),M)
   if mat==(1,0,0,1):break
  else:raise ValueError('period search budget')
  mat=mp(A,n);u=mat[2];vn=mat[0]+mat[3];xi=u//(4*C*C*d)
  require(xi>0 and xi%modulus_multiple==0 and u==4*C*C*d*xi,'period witness')
  F=(vn//2)**2;G=(A//2-1)*(F-1)-1;Om=4*d*u;lam=4*n*(vn//2);period=lam//math.gcd(lam,Om)
  require(math.gcd(period,xi)==1,'CRT independence')
  require(mp(A,lam,F)==(1,0,0,1),'period modulo F')
  for residue in [0,1,xi-1]:
   L=period*((residue*pow(period,-1,xi))%xi)+period*xi
   j=B+Om*L;modulus=Om*F*xi
   Hmod=mp(2*G,j,modulus)[2];base=C+(B-C)*F
   require((Hmod-base)%(Om*F)==0,'H CRT assembly')
   y=(Hmod-base)//(Om*F)
   require((y-residue)%xi==0,'full y residue')
  crt.append({'A':A,'B':B,'N':modulus_multiple,'matrix_period':n,'xi_bits':xi.bit_length(),'residue_classes_tested':3})
# Countercontrol: dropping the new |C|>1 guard invalidates reliability.
A,B,C,n=72,31,-1,8
mat=mp(A,n);u=mat[2];r=(mat[0]+mat[3])//2;d=A
xi=u//(4*d);D=d*d;F=r*r;G=(A//2-1)*(F-1)-1;Om=4*d*u;lam=4*n*r
require(u==4*d*xi and xi>0,'countercontrol xi')
require(math.gcd(lam,Om)==32 and (B+1)%32==0,'countercontrol CRT compatibility')
# j=-1+lambda*h=B (mod Omega).
h=((B+1)//32)*pow(lam//32,-1,Om//32)%(Om//32)
j=-1+lam*h
if j<=0:j+=lam*(Om//32)
require((j+1)%lam==0 and (j-B)%Om==0 and j%2==1,'countercontrol j')
mod=Om*F;Hmod=mp(2*G,j,mod)[2];base=C+(B-C)*F
require((Hmod-base)%mod==0,'countercontrol integer y')
require(1<B<abs(A)//2-1 and A%3==0 and B%4==3 and C%3==2,'countercontrol slice')
require(mp(A,B)[2]!=C,'countercontrol false index')
exception={'A':A,'B':B,'C':C,'n':n,'xi':xi,'F':F,'G':G,'Omega':Om,'lambda':lam,'j':j,'CRT_gcd':32,'H_definition':'u_j(2G)','y_definition':'(H-C-(B-C)*F)/(Omega*F)','scope':'A false-index solution of the shortened standalone Lucas certificate; not a solution of the full consistency polynomial. The Delta guard excludes it.'}
receipt={'status':'PASS','scope':'Independent literal counts, actual-coefficient degree attainment, unchanged source binding, modular tail and local arithmetic regressions; not a proof-assistant certificate.','circuit_sha256':sha((N/'integer10.json').read_bytes()),'operations':dict(ops),'total_operations':sum(ops.values()),'exact_degree':degrees[a['output']],'unchanged_prefix_nodes':0 if companion else 460,'fixed_payloads':payloads,'degree_attainment':leading,'tail_cases':480,'local_parameter_cases':local_count,'crt_cases':crt,'exceptional_index_countercontrol':exception}
(R/('INDEPENDENT_H1868_CHECKS.json' if companion else 'INDEPENDENT_CHECKS.json')).write_text(json.dumps(receipt,indent=2)+'\n');print('PASS:',expected_ops,'operations, exact degree',expected_degree,',480 prefix/tail cases,',local_count,'signed local cases,12 CRT instances')

#!/usr/bin/env python3
"""Independent arithmetic reviewer: no builder or upstream imports."""
from pathlib import Path
import json,gzip,hashlib,random,itertools
ROOT=Path(__file__).resolve().parent

def need(c,m):
 if not c:raise RuntimeError(m)
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
class Poly:
 def __init__(self,a,p):self.a=trim([x%p for x in a]);self.p=p
 def cv(self,b):return b if isinstance(b,Poly) else Poly([b],self.p)
 def __add__(self,b):
  b=self.cv(b);a=self.a;c=b.a
  return Poly([(a[i] if i<len(a) else 0)+(c[i] if i<len(c) else 0) for i in range(max(len(a),len(c)))],self.p)
 __radd__=__add__
 def __sub__(self,b):return self+-self.cv(b)
 def __rsub__(self,b):return -self+b
 def __neg__(self):return Poly([-x for x in self.a],self.p)
 def __mul__(self,b):
  b=self.cv(b);a=self.a;c=b.a;o=[0]*(len(a)+len(c)-1)
  for i,x in enumerate(a):
   if x:
    for j,y in enumerate(c):
     if y:o[i+j]+=x*y
  return Poly(o,self.p)
 __rmul__=__mul__

def ports():
 b=json.loads((ROOT/'coefficients/BINDING.json').read_text());out={};hs={}
 for n,row in b['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/row['file']).read_bytes());h=hashlib.sha256(raw).hexdigest();need(h==row['raw_sha256'],('port hash',n));x=int.from_bytes(raw,'little');need(x.bit_length()==row['bits'],('port bits',n));out[n]=x;hs[n]=h
 need(out['beta']==(1<<1064921)-1,'beta literal');need(out['cone_A']==1<<1113,'cone_A literal');need(out['cone_B']==1<<666104,'cone_B literal')
 return out,hs

def replay(pack,env,p=None):
 e=dict(env)
 def get(x):return x if isinstance(x,int) else e[x]
 for n in pack['nodes']:
  a,b=map(get,n['args']);x={'add':lambda:a+b,'sub':lambda:a-b,'mul':lambda:a*b}[n['op']]();e[n['id']]=x%p if p else x
 return e[pack['output']],e

def tensor_norm(x,rs,p):
 """All-sign product in the independent square-root algebra, numeric mod p."""
 m=len(rs);size=1<<m
 def mul(a,b):
  o=[0]*size
  for i,x in enumerate(a):
   if not x:continue
   for j,y in enumerate(b):
    if not y:continue
    f=x*y;both=i&j
    for k,r in enumerate(rs):
     if both>>k&1:f=f*r%p
    o[i^j]=(o[i^j]+f)%p
  return o
 val=[1]+[0]*(size-1)
 for sg in itertools.product((-1,1),repeat=m):
  a=[0]*size;a[0]=x
  for k,s in enumerate(sg):a[1<<k]=s
  val=mul(val,a)
 need(all(v==0 for v in val[1:]),'formal conjugate product not scalar')
 return val[0]

def prefix(v):
 j,C,z,h,r,vs,w,T,c,n,t,p2,p3=[v[x] for x in ['j','C','z','h','r','v','w','T','c','n','t','p2','p3']]
 J=6*j+1;q=v['beta']*J+1;W=12*w+4;X=q*W;Y=q*vs;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H;F=(v['K0']+W)*C-z*(q-1);R=(q*(q-F)-C)*(q*q-1)+(v['MC']+q*v['MF'])*J;k=R+1+h*E;eta=c-Y*k;zeta=k-eta;u=E*Y*k;At=u*(u+k)+1;Am=1+Delta*c*c;b0=X+a*c;dc=v['cone_A']*F;cc=v['cone_B']*C;dg=dc*cc-(q-dc-cc)**2;Ag=dg*eta*zeta-(t*t-dg-eta*zeta+1)**2-1-p2*p2-p3*(p3+1);I=(2*r+1)*c*c;M=2*q*q;defect=vs-q*q
 if 'f' in v:
  f=v['f'];Q=I*I;S=Q-Delta*(f*f-1);V=f*c*T-f*f*R-c
 else:
  Af=1+Delta*I*I;Q=Delta*Delta*I*I;V=Af*(c*T-R)-c
 delta=Q-1;Cy=Q*V*V-1;U=M*H
 return locals()

def direct(pack,v,p):
 e=prefix(v);get=lambda k:e[k]%p
 name=pack['name'];M,H,U,At,Am,Ag,Cy,delta,V,defect,b0=[get(k) for k in ['M','H','U','At','Am','Ag','Cy','delta','V','defect','b0']];n=v['n']
 if delta==0:return None
 inv=pow(delta,-1,p)
 if name.startswith('integer13_'):
  Z=(U*(n+V)+M*b0+H*defect)%p;rs=[81*U*U*get('Af'),9*U*U*At,M*M*Am,729*U*U*Ag,U*U*Cy*inv];power=16
 elif name.startswith('integer14_'):
  Z=(U*(n+V)+M*b0+H*defect)%p;rs=[9*U*U*At,81*U*U*Ag,M*M*Am,U*U*Cy*inv];power=8
 elif name.startswith('integer15_'):
  Z=(M*(n+V)+defect)%p;rs=[9*M*M*At,81*M*M*Ag,M*M*Cy*inv];power=4
 elif name.startswith('integer15c_'):
  t0=get('u')*2+get('k');Z=(U*(n+3*t0+2*V)+2*M*b0+H*defect)%p;rs=[36*U*U*At,4*M*M*Am,4*U*U*Cy*inv];power=4
 else:
  t0=get('u')*2+get('k');Z=(M*(n+3*t0+2*V)+defect)%p;rs=[36*M*M*At,4*M*M*Cy*inv];power=2
 N=tensor_norm(Z,[x%p for x in rs],p)*pow(delta,power,p)%p
 if 'f' not in v:return N
 out=(1+N)*(1+get('S'))
 if 'gamma' in v:D=(b0+H*v['gamma'])**2-Am;out*=1+D
 if 'p1' in v:G=Ag-v['p1']**2;out*=1+4*G
 return (out-1)%p

def structure(pack):
 ids=set(pack['inputs']);need(len(ids)==len(pack['inputs']),'duplicate input');need(set(pack['variables']+pack['fixed_ports'])==ids,'input closure');by={}
 for row in pack['nodes']:
  need(row['op'] in ['add','sub','mul'],'operation');need(row['id'] not in ids,'node collision');need(len(row['args'])==2,'binary');need(all(isinstance(x,int) or x in ids for x in row['args']),'topology');ids.add(row['id']);by[row['id']]=row
 seen=set();todo=[pack['output']]
 while todo:
  x=todo.pop()
  if isinstance(x,int) or x in seen:continue
  seen.add(x)
  if x in by:todo+=by[x]['args']
 need(set(by)<=seen,'dead operation');need(set(pack['inputs'])<=seen,'dead input');need(len(by)==pack['live_binary_operations'],'count');return len(by)

def main():
 fixed,hashes=ports();rng=random.Random(131078);results=[]
 for path in sorted(ROOT.glob('integer*.json')):
  pack=json.loads(path.read_text());ops=structure(pack);num=0
  for p in [65521,65519,65497]:
   fp={k:x%p for k,x in fixed.items()}
   for z in range(24):
    env={**fp,**{x:rng.randrange(-9,10)%p for x in pack['variables']}}
    if z<4:env['v']=0 if z&1 else env['v'];env['c']=0 if z&2 else env['c']
    expect=direct(pack,env,p)
    if expect is None:continue
    got,_=replay(pack,env,p);need(got==expect,(path.name,'conjugate regression',p,z));num+=1
  cert=[]
  for p in [65521,65519]:
   slopes={x:2+i*i+3*i for i,x in enumerate(pack['variables'])};env={k:Poly([x%p],p) for k,x in fixed.items()};env.update({x:Poly([0,s],p) for x,s in slopes.items()});out,e=replay(pack,env);degree=len(out.a)-1;need(degree==pack['exact_degree'],(path.name,'exact degree attained',degree,pack['exact_degree']));norm=e[pack['named_registers']['norm']]
   cert.append({'prime':p,'slopes':slopes,'fixed_port_residues':{k:x%p for k,x in fixed.items()},'degree':degree,'leading_coefficient':out.a[-1],'norm_degree':len(norm.a)-1,'norm_leading_coefficient':norm.a[-1]})
  results.append({'name':pack['name'],'operations':ops,'signed_modular_conjugate_checks':num,'degree_certificates':cert});print(path.name,'ok',ops,cert[0]['degree'],flush=True)
 # Exhaustive residue statement behind finalizers.
 for a,c,r,f,g in itertools.product(range(4),repeat=5):
  if a%2:continue
  H=4*a+3;delta=a*a+H;I=(2*r+1)*c*c;S=I*I-delta*(f*f-1);D=g*g-delta*c*c-1
  need(S%4!=2,'S residue');need(D%4!=2,'D residue')
 for N,S,D,G in itertools.product(range(-5,6),repeat=4):
  if S==-2 or D==-2:continue
  need(((1+N)*(1+S)*(1+D)*(1+4*G)==1)==(N==S==D==G==0),'unit-product lemma')
 receipt={'status':'PASS','fixed_payload_raw_hashes':hashes,'packets':results,'scope':'Literal arithmetic, exact attained lower-degree certificates, modular transcription diagnostics; unbounded upper bounds and source equivalence are proved in PROOF.md.'};(ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':main()

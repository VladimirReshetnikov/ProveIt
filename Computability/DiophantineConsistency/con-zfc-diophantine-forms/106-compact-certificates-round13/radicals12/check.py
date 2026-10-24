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

def direct(v,p):
 j,C,z,h,r,vs,w,T,c,n,t,s0=[v[x] for x in ['j','C','z','h','r','v','w','T','c','n','t','s0']]
 J=6*j+1;q=v['beta']*J+1;W=12*w+4;X=q*W;Y=q*vs;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H;F=(v['K0']+W)*C-z*(q-1);R=(q*(q-F)-C)*(q*q-1)+(v['MC']+q*v['MF'])*J;k=R+1+h*E;eta=c-Y*k;zeta=k-eta;dg=v['cone_A']*F*v['cone_B']*C-(q-v['cone_A']*F-v['cone_B']*C)**2;P=dg*eta*zeta-(t*t-dg-eta*zeta+1)**2;s=3*s0;Dg=(3*P-4)*s*s+1;I=s*r*c*c;Df=1+Delta*I*I;Q=Delta*Delta*I*I;delta=Q-1;V=Df*(c-R+4*I*T)-c;Da=delta*(Q*V*V-1);Dt=1+X*Y*Y*(X*Y*Y+1)*k*k;Dm=1+Delta*c*c;b0=X+a*c;M=2*q*q;L=M*H;e=vs-q*q;u=L*T-M*b0-H*e;D=M*M*Dm
 # Independently obtain the quintic remainder by binomial expansion.
 from math import comb
 A=B=0
 for power,co in [(5,1),(3,32),(2,1),(1,31),(0,31)]:
  for i in range(power+1):
   val=co*L**(5-power)*comb(power,i)*u**(power-i)*D**(i//2)
   if i%2:B+=val
   else:A+=val
 S=I*L**5;Z=S*(n+(2*Q-1)*V)-A
 rs=[B*B*D,4*S*S*Da,36*S*S*Df,324*S*S*Dt,2916*S*S*Dg]
 return tensor_norm(Z%p,[x%p for x in rs],p)

def structure(pack):
 ids=set(pack['inputs']);by={}
 need(set(pack['variables']+pack['fixed_ports'])==ids,'inputs')
 for row in pack['nodes']:
  need(row['op'] in ['add','sub','mul'] and len(row['args'])==2,'binary operation')
  need(row['id'] not in ids and all(isinstance(x,int) or x in ids for x in row['args']),'topology')
  ids.add(row['id']);by[row['id']]=row
 todo=[pack['output']];seen=set()
 while todo:
  x=todo.pop()
  if isinstance(x,int) or x in seen:continue
  seen.add(x)
  if x in by:todo+=by[x]['args']
 need(set(by)<=seen and set(pack['inputs'])<=seen,'liveness');need(len(by)==pack['live_binary_operations']==233,'operation count');need(len(pack['variables'])==12,'12 coordinates')

def main():
 fixed,hashes=ports();pack=json.loads((ROOT/'integer12_degree2048.json').read_text());structure(pack);rng=random.Random(122048);count=0
 for p in [65521,65519,65497]:
  fp={k:x%p for k,x in fixed.items()}
  for i in range(24):
   v={**fp,**{n:rng.randrange(-5,6)%p for n in pack['variables']}}
   if i<8:
    if i&1:v['s0']=0
    if i&2:v['r']=0
    if i&4:v['c']=0
   got,_=replay(pack,v,p);want=direct(v,p);need(got==want,('independent binomial and32sign norm',p,i));count+=1
 cert=[]
 for p in [65521,65519]:
  slopes={x:3+i*i+2*i for i,x in enumerate(pack['variables'])};e={k:Poly([x%p],p) for k,x in fixed.items()};e.update({k:Poly([0,s],p) for k,s in slopes.items()});out,env=replay(pack,e);need(len(out.a)-1==2048,('degree',len(out.a)-1));cert.append({'prime':p,'slopes':slopes,'fixed_port_residues':{k:x%p for k,x in fixed.items()},'attained_degree':2048,'leading_coefficient':out.a[-1]})
 # Exact scalar check of the selected coefficient's power accounting.
 # q0=6 beta j, a0=12 w v q0^2, I0=3s0 r c^2.
 coefficient=108**16*8**160*2**16*27**8*4**16*12**288*3**112*6**928
 need(coefficient==2**2064*3**1400,'selected coefficient')
 result={'status':'PASS','variables':12,'operations':233,'signed_modular_full_conjugate_checks':count,'I_zero_slices':'s0,r,c individually and all intersections included','fixed_payload_hashes':hashes,'degree_certificates':cert,'universal_upper_bound':'Paired auxiliary factor has weights98,128,110;16 factors give2048. See PROOF.md.','selected_coefficient':{'monomial':{'j':928,'w':288,'v':320,'h':32,'s0':128,'r':112,'c':224,'T':16},'value':'2^2064 * 3^1400 * beta^928','degree':2048}}
 (ROOT/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','operations':233,'degree':2048,'checks':count,'leading_coefficients':[x['leading_coefficient'] for x in cert]},indent=2))
if __name__=='__main__':main()

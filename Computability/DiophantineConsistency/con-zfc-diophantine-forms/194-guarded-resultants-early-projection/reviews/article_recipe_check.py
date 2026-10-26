"""Reconstruct the two entire positive tuples from the printed TeX recipes.
Handwritten implementation; no producer or native checker imported.
"""
from pathlib import Path
from collections import defaultdict
import json,re,gzip,hashlib
ROOT=Path(__file__).resolve().parents[1]
def require(x,m):
 if not x:raise ValueError(m)
def check(tag,tex):
 txt=tex.read_text();lines=txt.split('\\begingroup\\fontsize{7.7}{8.2}\\selectfont\\ttfamily\n')[1].split('\\endgroup')[0]
 seed=''.join(re.findall(r'([A-Za-z0-9]+)\\par',lines));require(len(seed)==436,'seed length');alphabet='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
 A=0
 for ch in seed:A=62*A+alphabet.index(ch)
 N=A%(1<<636);T=(A>>636)%(1<<1675);E=A>>2311
 digit=lambda a,b,k:(a//b**k)%b
 actions=[];sigma=0;tau=0
 for q in range(215):
  m=digit(N,2,430+q);F=14+m*(digit(E,16,tau)-14)
  for b in range(2):
   j=2*q+b;nu=digit(N,2,j);u=nu*(1+sigma)+(1-nu)*digit(T,216,j-sigma);sigma+=nu
   actions.append((u,digit(F,2,2*b),digit(F,2,2*b+1)))
  tau+=m
 require(actions[0]==(1,1,1),'initializer')
 S={d:sorted({u for u,v,dd in actions if dd==d}) for d in (0,1)}
 rank=lambda d,q:205-199*d+sum(x<q for x in S[d])
 ts={}
 def put(i,t):
  require(i not in ts,'tile overlap');ts[i]=t
 if tag=='low2963':
  put(0,(2,435,3,1))
  for j,(u,v,d) in enumerate(actions):put(j+1,((1-d)*rank(0,u),j+2,d*rank(1,u),v))
  for a in range(2):
   for b in range(2):put(433-2*a+b,(0,432*a+b,0,432*a+b))
  for d in range(2):
   for q in S[d]:
    for b in range(2):r=rank(d,q);put(423+2*r+b,(d*r,b,(1-d)*r,2*q+b+2))
  for a in range(2):
   for b in range(2):put(923+2*a+b,(0,432*a+b,0,438))
  for i,t in [(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))]:put(i,t)
  for t in (434,435,436):put(496+t,(1,438,1,t))
  for a in range(3):
   for b in range(3):put(933+3*a+b,(a*a,437,b,437))
  require(set(ts)==set(range(942)),'new tile support');rho=1<<47;B=rho**2963;beta=B-1
  def psi(t):
   p=defaultdict(int)
   for i in range(8):p[978+i]+=t**i;p[969+i]+=t**(17+i)
   for i in range(9):p[960+i]+=t**(8+i);p[942+i]+=t**(25+i)
   p[1005]+=2-t;return p
  MC=beta-rho**977-sum(rho**j for j in range(942))-sum(co*rho**j for j,co in psi(1).items())
  MF=beta+4*sum(rho**j for j in range(917))+((1<<44)-2)*rho**1956+sum(rho**j for j in range(960,969))+sum(rho**j for j in range(987,995))+rho**1005
  phi=defaultdict(int)
  for j,(w,n,p,ss) in ts.items():phi[j]+=1+2**10*(1+w+2**8*n+2**17*p+2**25*ss)
  for j,co in psi(2).items():phi[j]+=2**10*co
  K=rho**18+rho**1005+rho**2972+sum(co*rho**(1956-j) for j,co in phi.items())
 else:
  put(0,(2,435,3,1));put(1,(5,0,0,0))
  for j,(u,v,d) in enumerate(actions):put(j+2,((1-d)*rank(0,u),j+2,d*rank(1,u),v))
  for b in range(2):put(432+b,(0,432+b,0,432+b));put(434+b,(0,b,0,b))
  for d in range(2):
   for q in S[d]:
    for b in range(2):r=rank(d,q);put(424+2*r+b,(d*r,b,(1-d)*r,2*q+b+2))
  for j in range(4):put(924+j,(0,j+430*(j//2),0,438))
  for i,t in [(928,(2,434,2,0)),(929,(3,436,4,4)),(930,(4,436,4,0))]:put(i,t)
  for t in (434,435,436):put(497+t,(1,438,1,t))
  for a in (0,1,4):
   for b in range(3):put(934+3*a+b-6*(a//4),(a,437,b,437))
  require(set(ts)==set(range(943)),'old tile support');rho=1<<67;B=rho**8807;beta=B-1
  support=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
  MC=beta-sum(rho**e for e in support-{1})-2*rho**1063
  MF=beta+4+((1<<51)-2)*(rho**4393+rho**5495)+sum(rho**e for e in range(1013,1023))+sum(rho**e for e in range(1065,1074))+rho**2195+rho**3296+((1<<65)-1)*sum(rho**e for e in range(8792,8805))+((1<<19)-1)*rho**8805
  phi=defaultdict(int)
  for j,(w,n,e,ss) in ts.items():phi[j]+=1+2**51-2**10*(w+2**8*n+2**17*e+2**25*ss+127*2**34)
  for b,e,m in [(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]:
   for j in range(m):phi[e+j]+=2**(b+j)
  K=sum(rho**e for e in [30,62,1100,2201,8849])+sum(co*(rho**(4393-j)+rho**(5495-j)) for j,co in phi.items())
 bind=json.loads((ROOT/f'positive/quotient_t_{tag}.json').read_text())['coefficient_binding'];recon={'beta':beta,'K0':K,'MC':MC,'MF':MF};rows={}
 for name,x in recon.items():
  raw=gzip.decompress((ROOT/'positive'/bind['path']/bind['ports'][name]['file']).read_bytes());require(x==int.from_bytes(raw,bind['endianness']),tag+' '+name)
  rows[name]=hashlib.sha256(raw).hexdigest()
 return {'tuple':tag,'printed_recipe_sha256':hashlib.sha256(tex.read_bytes()).hexdigest(),'seed_characters':len(seed),'tiles':len(ts),'every_actual_integer_matches':True,'raw_sha256':rows}
print(json.dumps({'status':'PASS','results':[check('low2963',ROOT/'positive/coefficients_low2963.tex'),check('radix67',ROOT/'positive/coefficients_radix67.tex')]},indent=2,sort_keys=True))

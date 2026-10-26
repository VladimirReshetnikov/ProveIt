#!/usr/bin/env python3
"""Independent reconstruction transcribed from the two printed TeX recipes.
Only the seed is extracted from TeX. No producer or supplied checker is imported.
"""
import pathlib,re,json,gzip,hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def seed(path):
 text=path.read_text();s=''.join(re.findall(r'^([A-Za-z0-9]+)\\par$',text,re.M));need(len(s)==436,'seed length')
 A=0
 for ch in s:A=62*A+'0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'.index(ch)
 return A,s
A,s=seed(ROOT/'positive/coefficients.tex');A2,s2=seed(ROOT/'positive/start_marker_coefficients.tex');need(A==A2,'same decoder seed')
N=A%(1<<636);T=(A>>636)%(1<<1675);E=A>>2311
nu=[(N>>j)&1 for j in range(430)];mask=[(N>>(430+q))&1 for q in range(215)]
actions=[]
for j in range(430):
 q,b=divmod(j,2);sigma=sum(nu[:j]);tau=sum(mask[:q]);F=14 if mask[q]==0 else (E>>(4*tau))&15
 target=1+sigma if nu[j] else (T//(216**(j-sigma)))%216
 actions.append((target,(F>>(2*b))&1,(F>>(2*b+1))&1))
need(actions[0]==(1,1,1),'first action')
sets={d:{u for u,v,e in actions if e==d} for d in [0,1]}
ranks={(d,q):205-199*d+sum(u<q for u in sets[d]) for d in [0,1] for q in range(216)}
tiles={}
def put(i,t):
 need(i not in tiles,'duplicate tile index');tiles[i]=t
put(0,(2,435,3,1));put(1,(5,0,0,0))
for j,(u,v,d) in enumerate(actions):
 q,b=divmod(j,2);put(j+2,((1-d)*ranks[0,u],2*q+b+2,d*ranks[1,u],v))
for a in range(2):
 for b in range(2):put(434-2*a+b,(0,432*a+b,0,432*a+b))
for d in [0,1]:
 for q in sets[d]:
  for b in [0,1]:
   r=ranks[d,q];put(424+2*r+b,(d*r,b,(1-d)*r,2*q+b+2))
for a in range(2):
 for b in range(2):put(924+2*a+b,(0,432*a+b,0,438))
for i,t in [(928,(2,434,2,0)),(929,(3,436,4,4)),(930,(4,436,4,0))]:put(i,t)
for t in [434,435,436]:put(497+t,(1,438,1,t))
for a in range(3):
 for b in range(3):put(934+3*a+b,(a*a,437,b,437))
need(set(tiles)==set(range(943)),'all 943 tile slots')
# Historical table is algebraically the same indexed tiles.
for j in range(4):need(tiles[924+j]==(0,j+430*(j//2),0,438),'historical constructor equivalence')
for a in [0,1,4]:
 for b in range(3):need(tiles[934+3*a+b-6*(a//4)]==(a,437,b,437),'historical final table equivalence')
receipts=[]
for current in [False,True]:
 radix,L=(47,4177) if current else (67,8807)
 rp=lambda e:1<<(radix*e)
 geom=lambda e,m:sum(rp(e+j) for j in range(m))
 B=rp(L);beta=B-1
 if current:
  def psi(t):
   return sum(t**j*rp(1002+j)+t**(17+j)*rp(992+j) for j in range(8))+sum(t**(8+j)*rp(973+j)+t**(25+j)*rp(943+j) for j in range(9))+t**34*(2-t)*rp(1048)
  MC=beta+rp(1)-(rp(1)+3)*rp(990)-geom(0,943)-psi(1)
  MF=B+3+((1<<44)-2)*(rp(2059)+rp(3108))+geom(973,9)+geom(1012,8)+rp(1048)+(1<<29)*rp(4175)-rp(4157)
  weights={i:1+(1<<10)*(1+w+(1<<8)*n+(1<<17)*p+(1<<25)*ss) for i,(w,n,p,ss) in tiles.items()}
  for j in range(8):weights[1002+j]=(1<<10)*(1<<j);weights[992+j]=(1<<10)*(1<<(17+j))
  for j in range(9):weights[973+j]=(1<<10)*(1<<(8+j));weights[943+j]=(1<<10)*(1<<(25+j))
  K=rp(20)+rp(30)+rp(1048)+rp(4187)+sum(v*(rp(2059-e)+rp(3108-e)) for e,v in weights.items())
  ports=ROOT/'positive/start_marker4177/coefficients';endian='big'
 else:
  indices=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
  MC=B-1-sum(rp(e) for e in indices-{1})-2*rp(1063)
  MF=B-1+4+((1<<51)-2)*(rp(4393)+rp(5495))+geom(1013,10)+geom(1065,9)+rp(2195)+rp(3296)+((1<<65)-1)*geom(8792,13)+((1<<19)-1)*rp(8805)
  weights={i:1+(1<<51)-(1<<10)*(w+(1<<8)*n+(1<<17)*p+(1<<25)*ss+127*(1<<34)) for i,(w,n,p,ss) in tiles.items()}
  for b,e,m in [(10,1023,8),(18,1013,9),(27,1003,8),(35,983,9),(44,1031,1),(45,1022,1),(46,1011,1),(47,992,1),(48,1095,1),(49,2195,1),(50,3296,1)]:
   for j in range(m):weights[e+j]=weights.get(e+j,0)+(1<<(b+j))
  K=rp(30)+rp(62)+rp(1100)+rp(2201)+rp(8849)+sum(v*(rp(4393-e)+rp(5495-e)) for e,v in weights.items())
  ports=ROOT/'positive/parent/inherited_trace/coefficients';endian='little'
 result={'tuple':'Start-marker4177' if current else 'BFS943/radix67','seed_sha256':hashlib.sha256(s.encode()).hexdigest(),'seed_characters':len(s),'tiles':len(tiles),'ports':[]}
 for name,value,fn in [('beta',beta,'beta.bin.gz'),('K0',K,'K.bin.gz'),('MC',MC,'MC.bin.gz'),('MF',MF,'MF_source.bin.gz')]:
  raw=gzip.decompress((ports/fn).read_bytes());got=value.to_bytes((value.bit_length()+7)//8,endian)
  need(raw==got,'printed recipe reconstruction '+result['tuple']+' '+name)
  result['ports'].append({'name':name,'bits':value.bit_length(),'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest()})
 result['raw_total']=sum(x['raw_bytes'] for x in result['ports']);receipts.append(result)
out={'status':'PASS','scope':'Independent exact reconstruction from the printed TeX recipes; no producer/checker imports. This does not establish inherited unbounded calibration.','tuples':receipts}
print(json.dumps(out,indent=2))

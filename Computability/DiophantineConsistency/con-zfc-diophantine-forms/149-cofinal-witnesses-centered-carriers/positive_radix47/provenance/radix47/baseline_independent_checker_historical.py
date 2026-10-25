"""Independent bounded radix47 data/number checks; no incoming code executed."""
from pathlib import Path
import json,gzip,hashlib,math
ROOT=Path(__file__).resolve().parent
P=ROOT/'intake/conzfc_common_remainders_20261025/radix47'
F=P/'radix47'
def need(b,m):
 if not b:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
tiles=json.loads((P/'sources/research/indexed-tile-enumeration/TILES.json').read_text())
need(len(tiles)==943,'tile count')
rho=1<<47;d=47*8807;B=1<<d;beta=B-1
cs=[0]*3297
for i,(w,n,e,s) in enumerate(tiles):
 need(0<=w<256 and 0<=e<256 and 0<=n<512 and 0<=s<512,'field range')
 u=w+(n<<8)+(e<<17)+(s<<25)
 cs[i]=1+1024*(u+1)
for j in range(8):cs[1023+j]=1<<(10+j);cs[1003+j]=1<<(27+j)
for j in range(9):cs[1013+j]=1<<(18+j);cs[983+j]=1<<(35+j)
for e in [992,1011,1022,1031,1095,2195,3296]:cs[e]=1<<44
need(cs==json.loads((F/'phi_coefficients.json').read_text()),'all Phi coefficients')
need(sum(cs)==3953059820717999 and max(cs)==rho//8,'coefficient aggregates')
phys=set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296}
powr=lambda e:1<<(47*e)
DC=sum(powr(e) for e in [30,62,1100,2201])+sum(c*(powr(4393-e)+powr(5495-e)) for e,c in enumerate(cs) if c)
K0=DC+B*powr(42)
MC=beta-sum(powr(e) for e in phys if e!=1)-2*powr(1063)
lam=powr(4393)+powr(5495)
Ccore=sum(powr(e) for e in range(1013,1023))+sum(powr(e) for e in range(1065,1074))+powr(2195)+powr(3296)
Z=(rho-1)*sum(powr(e) for e in range(8792,8807))+(rho-1)*sum(powr(e) for e in range(7691,7694))+((1<<28)-4)*powr(7694)
MFn=4+(rho-2)*lam+Ccore+Z;MF=MFn+beta
need(0<MC<beta<MF<2*beta and DC<B,'port boxes')
need(MC.bit_count()==d-986 and MFn.bit_count()==986,'mask populations')
need(MC%4==2 and MFn%8==4,'phase residues')
ports=json.loads((F/'polynomial.json').read_text())['coefficient_binding']['ports'];bindings=[]
for k,value in [('beta',beta),('K0',K0),('MC',MC),('MF',MF)]:
 blob=(F/ports[k]['file']).read_bytes();raw=gzip.decompress(blob)
 need(int.from_bytes(raw,'little')==value,'whole raw port '+k)
 need(sha(raw)==ports[k]['raw_sha256'] and sha(blob)==ports[k]['gzip_sha256'],'port hashes')
 bindings.append({'port':k,'raw_bytes':len(raw),'gzip_bytes':len(blob),'raw_sha256':sha(raw),'gzip_sha256':sha(blob)})
need(sum(cs)+5+2*max(cs)+3*rho//4+29<30*rho,'carry29 inequality')
need(88*max(cs)+(rho-1024)+2*max(cs)+5+3*rho//4+29<13*rho,'carry12 inequality')
controls=[]
for p,o,factors in [(47,23,[23]),(8807,4403,[7,17,37]),(1012691,1012690,[2,5,7,17,23,37])]:
 need(all(p%i for i in range(2,math.isqrt(p)+1)),'primality')
 need(pow(B,o,p)==1 and all(pow(B,o//l,p)!=1 for l in factors),'exact order')
 h=(1+B*K0+B*B)%p
 need(math.gcd(h,p)==1 and math.gcd(B*B-1,p)==1,'units')
 controls.append({'prime':p,'exact_order':o,'B':B%p,'K0':K0%p,'Hctrl':h})
p=1012691;lift=pow(B,p-1,p*p)
need(lift==1+282338*p,'valuation-one lift')
r={'status':'PASS','scope':'Independent tile-table to entire Phi/tuple reconstruction, literal port hashes, mask populations and port boxes, numeric carry bounds, primality/exact orders/units/lift. Does not replay tile seed decoder, 51 geometry identities, polynomial degree or unbounded proof.','ports':bindings,'raw_bytes':sum(x['raw_bytes'] for x in bindings),'gzip_bytes':sum(x['gzip_bytes'] for x in bindings),'controller':controls,'lift_quotient':282338,'proof_sha256':sha((F/'radix47_proof.md').read_bytes())}
(ROOT/'baseline_radix47.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

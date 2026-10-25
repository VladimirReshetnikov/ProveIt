#!/usr/bin/env python3
"""Independent arithmetic/geometry audit of the complemented radix47 tuple."""
import argparse,base64,gzip,hashlib,json,math
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]/'agent_math');a=p.parse_args();root=a.root;out=root/'radix47'
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(p.read_text())
tiles=read(root/'sources/research/indexed-tile-enumeration/TILES.json')
need(len(tiles)==943 and len(set(map(tuple,tiles)))==943,'943 distinct tiles')
need(tiles[0]==[2,435,3,1] and tiles[1]==[5,0,0,0] and tiles[929]==[3,436,4,4],'distinguished tiles')
comp=[[255-w,511-n,255-e,511-s] for w,n,e,s in tiles]
for t,z in zip(tiles,comp):
 need([255-z[0],511-z[1],255-z[2],511-z[3]]==t,'label involution')
 for v,b in zip(z,[8,9,8,9]):need(0<=v<2**b,'label bounds')
# Full pairwise equality preservation is algebraic; check each color map once.
for col,width in [(0,8),(1,9),(2,8),(3,9)]:
 values={t[col] for t in tiles};need(len({2**width-1-v for v in values})==len(values),'bijection')
phi=[0]*3297
for i,(w,n,e,s) in enumerate(tiles):phi[i]=1+1024*(w+256*n+2**17*e+2**25*s+1)
for j in range(8):phi[1023+j]=2**(10+j);phi[1003+j]=2**(27+j)
for j in range(9):phi[1013+j]=2**(18+j);phi[983+j]=2**(35+j)
markers=[992,1011,1022,1031,1095,2195,3296]
for e in markers:phi[e]=2**44
need(phi==read(out/'phi_coefficients.json'),'entire complemented Phi')
# Recover every old coefficient independently from the pinned old K integer.
cp=root/'sources/research/indexed-tile-enumeration/coefficients'
oldgz=base64.b64decode((cp/'K.bin.gz.base64').read_bytes());oldraw=gzip.decompress(oldgz);pin=read(cp/'BINDING.json')['ports']['K0']
need(hashlib.sha256(oldraw).hexdigest()==pin['raw_sha256'],'old K raw binding')
need(hashlib.sha256(oldgz).hexdigest()==pin['gzip_sha256'],'old K gzip binding')
oldK=int.from_bytes(oldraw,'little');r67=2**67
oldrev,rem=divmod(oldK-sum(1<<(67*e) for e in [30,62,1100,2201,8849]),(1<<(67*1097))+(1<<(67*2199)))
need(rem==0,'old reversed polynomial division');oldphi=[(oldrev>>(67*(3296-e)))&(r67-1) for e in range(3297)]
need(oldrev>>(67*3297)==0,'old polynomial length')
for e in range(3297):
 expected=2**44+1026-oldphi[e] if e<943 else (2**44 if e in markers else oldphi[e])
 need(phi[e]==expected,'independent old-K coefficient route at '+str(e))
b=47;L=8807;rho=1<<b;d=b*L;B=1<<d;beta=B-1
support={i for i,c in enumerate(phi) if c}|{1063,1064}
need(len(support)==986 and sum(c!=0 for c in phi)==984,'support sizes')
need(max(phi)==2**44 and max(phi[:943])<2**44,'actual coefficient maximum')
need(sum(phi)==3953059820717999,'actual complete coefficient sum')
need(sum(phi[943:])==rho-1024,'nonselector coefficient sum')
DC={e:1 for e in [30,62,1100,2201]}
for e,c in enumerate(phi):
 if c:
  for j in [4393-e,5495-e]:
   need(j not in DC,'DC coefficient collision');DC[j]=c
K=sum(c<<(b*e) for e,c in DC.items())+(1<<(b*8849))
MC=beta-sum(1<<(b*e) for e in support if e!=1)-2*(1<<(b*1063))
core=sum(1<<(b*e) for e in list(range(1013,1023))+list(range(1065,1074))+[2195,3296])
Z=(rho-1)*sum(1<<(b*e) for e in range(8792,8807))+(rho-1)*sum(1<<(b*e) for e in range(7691,7694))+(2**28-4)*(1<<(b*7694))
MFn=4+(rho-2)*((1<<(b*4393))+(1<<(b*5495)))+core+Z
ports={'beta':beta,'K0':K,'MC':MC,'MF':MFn+beta}
report=read(out/'construction_report.json')
for name,n in ports.items():
 raw=gzip.decompress((out/'coefficients'/f'{name}.bin.gz').read_bytes())
 need(n==int.from_bytes(raw,'little'),'complete tuple integer '+name)
 need(len(raw)==(n.bit_length()+7)//8,'minimal integer bytes '+name)
 need(hashlib.sha256(raw).hexdigest()==report['binding'][name]['raw_sha256'],'binding '+name)
need(0<MC<beta<MFn+beta<2*beta and K>0 and beta%2==1,'scalar port boxes')
need(MC%4==2 and MFn%8==4,'origin residues')
need(MC.bit_count()==d-986 and MFn.bit_count()==986 and Z.bit_count()==872,'mask populations')
# Exact basis geometry of every constrained or reset current-cell digit.
def hits(t):return {e:DC[t-e] for e in support if t-e in DC}
for j in range(10):need(hits(1013+j)=={983+j:1},'north-copy geometry')
for j in range(9):need(hits(1065+j)=={1003+j:1},'spatial-copy geometry')
for t in [2195,3296]:need(hits(t)=={1095:1},'anchor geometry')
need(hits(2194)=={} and hits(3295)=={2195:1},'anchor reset geometry')
need(hits(1012)=={} and hits(1064)=={},'copy reset geometry')
full={e:c for e,c in enumerate(phi) if c}
for t in [4393,5495]:need(hits(t)==full,'clause geometry')
adj={e:phi[e+1] for e in support if e+1<len(phi) and phi[e+1]}
need(hits(4392)==adj,'first clause reset geometry');adj2=dict(adj);adj2[3296]=adj2.get(3296,0)+2**44
need(hits(5494)==adj2,'second clause reset geometry')
need(hits(7690)=={2195:phi[0]} and hits(8791)=={3296:phi[0]},'padding reset geometry')
for t in list(range(7691,7696))+list(range(8792,8807)):need(not hits(t),'padding zero geometry')
for delta in [1097,1098,1102,2198,2199]:need(not any(e+delta in support for e in support),'support exclusion '+str(delta))
need([(e,e+1101) for e in sorted(support) if e+1101 in support]==[(2195,3296)],'unique anchor difference')
# Strict numeric carry premises; no sample run substitutes for these inequalities.
pre=sum(phi)+5+2*max(phi)+3*rho//4+29
post=88*max(phi)+(rho-1024)+2*max(phi)+5+3*rho//4+29
need(pre<30*rho and 943+29<1024,'predecoded bound')
need(post<13*rho,'decoded bound')
need(7*2**44-1024+12<rho,'clause reset bound')
need(max(phi)+12<rho and 1+3*rho//4+12<rho and 18+12<rho,'padding anchor copy resets')
# All occupied canonical aggregate digits are rho+1, hence digit1/carry1.
for i,t in enumerate(comp):
 u=t[0]+256*t[1]+2**17*t[2]+2**25*t[3]
 aggregate=phi[i]+1024*u+7*2**44
 need(aggregate==rho+1,'occupied aggregate '+str(i))
need(((rho+1)%rho)&(rho-2)==0,'occupied clause mask')
# Independent prime, order and lift certificates for the new controller.
lam=1012691
for prime in [47,8807,lam]:need(all(prime%z for z in range(2,math.isqrt(prime)+1)),'primality')
need(lam>d and (lam-1)%101269==0,'controller size/order multiplier')
def factors(n):
 fs=[];p=2
 while p*p<=n:
  if n%p==0:
   fs.append(p)
   while n%p==0:n//=p
  p+=1
 if n>1:fs.append(n)
 return fs
rows=[]
for prime,order in [(47,23),(8807,4403)]:
 bb=pow(2,d,prime);need(pow(bb,order,prime)==1,'order annihilation')
 for p in factors(order):need(pow(bb,order//p,prime)!=1,'exact order')
for prime in [47,8807,lam]:
 bb=pow(2,d,prime);kk=K%prime;hh=(1+bb*kk+bb*bb)%prime
 need(hh and (bb*bb-1)%prime,'controller units')
 rows.append({'prime':prime,'B':bb,'K0':kk,'Hctrl':hh})
lift=pow(2,d*(lam-1),lam*lam);need(lift==1+282338*lam,'valuation-one lift');need(0<282338<lam,'nonzero lift quotient')
print(json.dumps({'status':'PASS','producer_modules_imported':False,'tile_count':len(tiles),'coefficient_count':len(phi),'support_count':len(support),'raw_bytes':sum((n.bit_length()+7)//8 for n in ports.values()),'selector_max':max(phi[:943]),'coefficient_sum':sum(phi),'predecoded_carry':29,'decoded_carry':12,'occupied_clause_digit':1,'occupied_clause_outgoing_carry':1,'controller':rows,'lambda':lam,'lift_quotient':282338,'scope':'Independent complete coefficients, full tuple bytes, masks, exact target/reset basis geometry, carry inequalities, controller arithmetic. The unbounded semantic proof is reviewed separately.'},indent=2))

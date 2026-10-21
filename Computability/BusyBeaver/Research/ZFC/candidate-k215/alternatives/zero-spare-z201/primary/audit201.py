import sys
if not __debug__: raise SystemExit("Run without -O: assertions are required for verification.")
from pathlib import Path
import json,gzip,hashlib
P=Path(__file__).resolve().parent
F=P/'inherited'
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t
T=table(P/'201.tm');states=sorted({q for q,b in T});assert len(states)==215 and set(T)=={(q,b)for q in states for b in(0,1)}
raw='#! start 74\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))
assert (P/'z201.native.tm').read_text()==raw
order=[74]+[q for q in states if q!=74];mapping={q:i for i,q in enumerate(order)};mapping[254]=215
raw='#! start 0\n'+''.join(f'{mapping[q]} {b} {w} {"R" if d==1 else "L"} {mapping[z]}\n'for q in order for b in(0,1)for w,d,z in[T[q,b]])
assert (P/'z201.tm').read_text()==raw;D=table(P/'z201.tm');assert all(D[mapping[q],b]==(w,d,mapping[z])for(q,b),(w,d,z)in T.items())
a=json.loads(gzip.decompress((P/'discharge201.json.gz').read_bytes()));q=74;h=0;ones=set();dq=0;dh=0;dones=set()
assert len(a['trace'])==a['steps']==570263
for expected in a['trace']:
 b=int(h in ones);w,d,z=T[q,b];assert expected==[q,h,b,w,d,z]
 db=int(dh in dones);dw,dd,dz=D[dq,db];assert(dw,dd,dz)==(w,d,mapping[z])
 if w:ones.add(h)
 else:ones.discard(h)
 if dw:dones.add(dh)
 else:dones.discard(dh)
 q=z;h+=d;dq=dz;dh+=dd
assert(q,h)==(a['state'],a['head'])and q==84 and dq==mapping[q]and dh==h and ones==dones==set(a['one_cells'])
r=a['registers'];assert r==[5,0,0,0,1,0,0,0,0];phy=(6,2,0,4,3,7,8,5,1);values=[None]*9
for i,j in enumerate(phy):values[j]=r[i]
values+=a['spares'];header=h+64+a['gap'];expected={h-1,header};pos=header+1
for n in values:
 assert type(n)is int and n>=0
 expected.update(range(pos+1,pos+n+2));pos+=n+2
assert expected==ones and min(ones)==h-1 and min(ones-{h-1})==header

def canonical(t,start,mirror=False):
 m={start:0};todo=[start];out=[]
 for q in todo:
  for b in(0,1):
   w,d,z=t[q,b]
   if z!=254 and z not in m:m[z]=len(m);todo.append(z)
   out.append([m[q],b,w,-d if mirror else d,'H'if z==254 else m[z]])
 assert len(todo)==len(t)//2
 return out
refs=[(F/'machine/z215.native.tm',74)]+[(F/'research/command_family'/n/'candidate.native.tm',0)for n in ['012','021','102','120','201','210','partialcb120']]+[(p,0)for p in sorted((F/'research/command_family/comparisons').glob('*.tm'))]
c=canonical(T,74);checks=[]
for p,start in refs:
 t=table(p);same=c==canonical(t,start);reflected=c==canonical(t,start,True);assert not same and not reflected
 checks.append(dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),isomorphic=same,isomorphic_reflected=reflected))
report=dict(status='PASS',steps=a['steps'],head=h,gap=a['gap'],header=header,registers=r,spare_count=len(a['spares']),spares=a['spares'],one_count=len(ones),complete_frame=True,zero_exterior=True,states=len(states),native_start=74,dense_start=0,dense_dispatcher=mapping[84],native_sha256=hashlib.sha256((P/'z201.native.tm').read_bytes()).hexdigest(),dense_sha256=hashlib.sha256((P/'z201.tm').read_bytes()).hexdigest(),comparisons=checks)
assert json.loads((P/'audit201.json').read_text())==report;print(json.dumps({k:v for k,v in report.items()if k not in('comparisons','spares')},indent=2))

import sys,os
if not __debug__ or os.environ.get("PYTHONOPTIMIZE"):raise SystemExit("Disable Python optimization")
from pathlib import Path
import json,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
from source_graph import guarded_graph
R=Path(__file__).resolve().parents[1];D=Path(__file__).resolve().parent
sites=json.loads((R/'companion217/source.sites.json').read_text());G=guarded_graph(sites)
v=[1,0,3,0,0,0,0,0,0];j=25;trace=[]
for k in range(172):
 trace.append([j,v.copy()]);a=G[j]
 if a[0]=='CI':v[a[1]]+=1;j=a[2]
 elif a[0]=='CD':b=bool(v[a[1]]);v[a[1]]-=int(b);j=a[3 if b else 2]
 elif a[0]=='CONTROL':j=a[1]
 else:raise AssertionError(a)
assert j==64 and v==[1,4,0,0,0,0,3,10,0],(j,v)
T={}
for line in (R/'companion217/global217.native.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,a,w,d,r=line.split();T[int(q),int(a)]=(int(w),1 if d=='R' else -1,int(r))
q=74;h=0;ones=set();lo=-20000;dense=bytearray(40001);qd=74;hd=0
for k in range(69744):
 w,d,q=T[q,int(h in ones)];wd,dd,qd=T[qd,dense[hd-lo]]
 assert(w,d,q)==(wd,dd,qd)
 if w:ones.add(h)
 else:ones.discard(h)
 dense[hd-lo]=wd;h+=d;hd+=dd
assert q==84 and h==-2 and hd==h
assert ones=={i+lo for i,x in enumerate(dense)if x}
physical=[None]*9
for i,z in enumerate((6,2,0,4,3,7,8,5,1)):physical[z]=v[i]
pos=63;regs=[]
while any(x>=pos for x in ones):
 assert pos not in ones and pos+1 in ones
 end=pos+1
 while end in ones:end+=1
 regs.append(end-pos-2);pos=end
assert regs[:9]==physical
spares=regs[9:];assert len(spares)==65
expected={h-1,h+64}|{h+i for i,b in enumerate(sites[j][0])if b=='1'};pos=h+65
for x in regs:
 expected.update(range(pos+1,pos+x+2));pos+=x+2
assert expected==ones
out=dict(status='PASS',table_sha256=hashlib.sha256((R/'companion217/global217.native.tm').read_bytes()).hexdigest(),source_sha256=hashlib.sha256((R/'companion217/source.sites.json').read_bytes()).hexdigest(),blank_steps=69744,head=h,source_ordinal=j,source_address=sites[j][0],registers=v,spares=spares,ones=sorted(ones),source_bridge_steps=172,source_entry=25,source_seed=[1,0,3,0,0,0,0,0,0],source_trace=trace)
assert out==json.loads((R/'companion217/STARTUP.json').read_text());print({k:v for k,v in out.items()if k not in ('source_trace','ones')})

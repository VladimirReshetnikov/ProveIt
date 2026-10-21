#!/usr/bin/env python3
"""Independent exact local certificate for simultaneous FT215 row-26 shortcuts.
An inductive sliding-window abstraction covers ALL tapes initially at state 0.
All joins have positive old/new durations, exact tape/head/control equality,
and no further patched row is executed in the new block before its join.
This certificate does not remove a state or replace the logical calibration.
"""
import argparse,hashlib,json,time
from pathlib import Path
from collections import Counter
def read(p):
 T={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();k=int(q),int(b);assert k not in T and d in ('L','R')
   T[k]=int(w),(1 if d=='R' else -1),int(z)
 states={q for q,b in T};assert set(T)=={(q,b)for q in states for b in(0,1)}
 assert {z for w,d,z in T.values()}-states=={254}
 return T,start
def dump(T,start):
 return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))
def invariant(T,start,r):
 width=2*r+1;W=1<<width;mask=W-1;seen=bytearray((max(q for q,b in T)+1)*W);todo=[]
 def add(q,v):
  if q==254:return
  k=q*W+v
  if not seen[k]:seen[k]=1;todo.append(k)
 for v in range(W):add(start,v)
 i=0
 while i<len(todo):
  q,v=divmod(todo[i],W);i+=1;w,d,z=T[q,(v>>r)&1];v=(v&~(1<<r))|(w<<r)
  if d==1:v>>=1;add(z,v);add(z,v|(1<<(width-1)))
  else:v=(v<<1)&mask;add(z,v);add(z,v|1)
 return seen,len(todo)
def path(T,p,v,r,cap,changed=None):
 q,h=p,0;trace=[]
 for t in range(cap):
  if q==254 or not(-r<=h<=r):break
  b=(v>>(h+r))&1
  if t and changed and(q,b)in changed:break
  w,d,z=T[q,b];v=(v&~(1<<(h+r)))|(w<<(h+r));h+=d;q=z;trace.append((q,h,v))
 return trace
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('input3.tm'));ap.add_argument('--output',type=Path,default=Path(__file__).with_name('ft-frontier'));a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 assert __debug__
 T,start=read(a.input);assert start==0 and T[26,0]==(0,1,134)and T[26,1]==(1,1,38)
 N=dict(T);N[26,0]=(0,1,194);N[26,1]=(1,-1,114);changed={k for k in T if T[k]!=N[k]}
 assert changed=={(26,0),(26,1)}
 r,cap=7,192;tic=time.monotonic();seen,total=invariant(T,start,r);W=1<<(2*r+1);cases=[];rows=[]
 for b in(0,1):
  cs=[v for v in range(W)if seen[26*W+v]and((v>>r)&1)==b];hist=Counter();example=None
  for v in cs:
   old=path(T,26,v,r,cap);targets={c:i+1 for i,c in enumerate(old)};new=path(N,26,v,r,cap,changed)
   found=next(((targets[c],j+1,c)for j,c in enumerate(new)if c in targets),None)
   assert found is not None,('No exact positive join',b,v)
   ot,nt,end=found;hist[ot,nt]+=1;cases.append([b,v,ot,nt,*end])
   if example is None:example={'window_lsb_first':''.join(str((v>>i)&1)for i in range(2*r+1)),'old_path':old[:ot],'new_path':new[:nt]}
  fixed=[{'offset':i-r,'bit':(cs[0]>>i)&1}for i in range(2*r+1)if all(((v>>i)&1)==((cs[0]>>i)&1)for v in cs)]
  rows.append({'read':b,'contexts':len(cs),'old_row':T[26,b],'new_row':N[26,b],'fixed_bits':fixed,'join_duration_counts':[[u,v,c]for(u,v),c in sorted(hist.items())],'example':example})
 raw=(json.dumps(cases,separators=(',',':'))+'\n').encode();(a.output/'join-certificate.json').write_bytes(raw)
 modified=dump(N,start).encode();(a.output/'machine.native.tm').write_bytes(modified)
 H=lambda x:hashlib.sha256(x).hexdigest()
 report={'status':'EXACT_POSITIVE_LOCAL_JOINS_PASS','table_sha256':H(a.input.read_bytes()),'modified_table_sha256':H(modified),'certificate_sha256':H(raw),'checker_sha256':H(Path(__file__).read_bytes()),'radius':r,'path_cap':cap,'invariant_contexts':total,'initial_cylinder':'all 2^15 local windows at control state 0; all initial tapes covered','invariant_bytes_sha256':H(seen),'simultaneous_changed_rows':[[q,b,*N[q,b]]for q,b in sorted(changed)],'join_rows':len(cases),'changes_excluded_from_strict_new_interior':True,'rows':rows,'working_states':len(N)//2,'scope':'Ordinary executable mathematical certificate relative to an inductive invariant; not a proof-assistant theorem. No state deletion or fresh Con(ZFC) calibration claimed.','seconds':time.monotonic()-tic}
 (a.output/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items()if k!='rows'},indent=2))
if __name__=='__main__':main()

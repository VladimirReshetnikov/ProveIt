#!/usr/bin/env python3
"""Independent literal-table census and dual sparse/dense complete blank run.
No compiler or runtime proof-engine import; a finite-prefix certificate only.
"""
from pathlib import Path
import argparse,hashlib,json,struct
PHY=(6,2,0,4,3,7,8,5,1)
def need(x,m):
 if not x:raise ValueError(m)
def parse(path):
 out={};start=None
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in out,'duplicate row');need(b in(0,1)and w in(0,1)and d in('L','R'),'bad row');out[q,b]=(w,-1 if d=='L'else 1,z)
 S={q for q,b in out};need(start==0 and 254 not in S,'wrong start/halt');need(set(out)=={(q,b)for q in S for b in(0,1)},'missing row');need({z for w,d,z in out.values()}-S=={254},'bad successor')
 reach={start};work=[start]
 while work:
  q=work.pop()
  for b in(0,1):
   z=out[q,b][2]
   if z in S and z not in reach:reach.add(z);work.append(z)
 return out,S,reach

def rootframe(q,h,ones):
 if q!=84 or not ones or min(ones)!=h-1:return None
 right=sorted(x for x in ones if x>h-1)
 if not right or right[0]<h+64:return None
 header=right[0];p=header+1;last=max(ones);values=[]
 while p<=last:
  if p in ones or p+1 not in ones:return None
  p+=1;begin=p
  while p in ones:p+=1
  values.append(p-begin-1)
 if len(values)<10:return None
 regs=[values[j]for j in PHY];gap=header-h-64
 expected={h-1,header};p=header+1
 for n in values:
  p+=1;expected.update(range(p,p+n+1));p+=n+1
 need(expected==ones,'root parse does not reconstruct the whole tape')
 return dict(registers=regs,physical_values=values[:9],spares=values[9:],gap=gap,header=header)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--limit',type=int,default=10000000);a=ap.parse_args()
 t,S,reach=parse(a.table);need(len(S)==215,'Expected215 working states');before=a.table.read_bytes();dense=bytearray(400001);origin=200000;ones=set();q=h=0;lo=hi=0;hashtrace=hashlib.sha256();used=set()
 for tick in range(a.limit+1):
  frame=rootframe(q,h,ones)
  if frame is not None:
   need([i-origin for i,b in enumerate(dense)if b]==sorted(ones),'dense/sparse complete-tape mismatch')
   frame.update(status='EXACT_COMPLETE_BLANK_PREFIX_PASS',steps=tick,state=q,head=h,one_cells=sorted(ones),ones_count=len(ones),visited_interval=[lo,hi],trace_sha256=hashtrace.hexdigest(),states=len(S),rows=len(t),graph_reachable_states=len(reach),visited_rows=len(used),table_sha256=hashlib.sha256(before).hexdigest(),auditor_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Finite exact blank-prefix certificate only. Dense and sparse executions agree at every step; entire tape equals directly reconstructed frame and is zero everywhere else. Source simulation and foundational calibration are separate obligations.')
   need(before==a.table.read_bytes(),'table changed during audit');a.output.write_text(json.dumps(frame,indent=2)+'\n');print(json.dumps({k:v for k,v in frame.items()if k not in('one_cells','spares')},indent=2));return
  need(tick<a.limit,'step bound exhausted');need(0<=h+origin<len(dense),'dense buffer exceeded');b=int(h in ones);need(b==dense[h+origin],'dense/sparse read mismatch');need((q,b)in t,'premature halt');w,d,z=t[q,b];used.add((q,b));hashtrace.update(struct.pack('>qqbbbbq',tick,h,b,w,d,0,q)+struct.pack('>q',z));dense[h+origin]=w
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;q=z;lo=min(lo,h);hi=max(hi,h)
if __name__=='__main__':main()

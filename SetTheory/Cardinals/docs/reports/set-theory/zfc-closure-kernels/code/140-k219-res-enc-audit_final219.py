#!/usr/bin/env python3
"""Independent literal-table and blank-boot audit of the final native219 table.

This script does not import the parent compiler, source interpreter, simulator,
or symbolic runtime. It is a finite, exact audit; the unbounded runtime proof
and source calibration are separate artifacts.
"""
from pathlib import Path
import argparse,hashlib,json,time
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('table',type=Path);ap.add_argument('sites',type=Path);ap.add_argument('output',type=Path);args=ap.parse_args()
args.output.parent.mkdir(parents=True,exist_ok=True)
raw=args.table.read_bytes();T={}
for line in raw.decode().splitlines():
 if not line.strip()or line.startswith('#'):continue
 q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R');T[q,b]=(w,1 if d=='R'else-1,z)
Q={q for q,b in T};assert len(Q)==219 and len(T)==438 and 254 not in Q and all((q,b)in T for q in Q for b in(0,1));assert{z for w,d,z in T.values()}-Q=={254}
reach={0};todo=[0]
for q in todo:
 for b in(0,1):
  z=T[q,b][2]
  if z!=254 and z not in reach:reach.add(z);todo.append(z)
assert reach==Q
rows=json.loads(args.sites.read_text());leaves={r[0]for r in rows};prefix={p[:i]for p in leaves for i in range(len(p))};assert len(leaves)==len(rows)==4744 and not(leaves&prefix) and all(p+b in leaves|prefix for p in prefix for b in('0','1'))
# The 108/1 shortcut is separately audited from exact source paths: old CB1
# leaves have suffix001, while newly shared CC2 leaves have suffix101.
source_at={p:(op,arg)for p,op,arg in rows}
shared=[]
for pc,op,arg in rows:
 q=84;h=0;prefix_ones={-1}|{i for i,b in enumerate(pc)if b=='1'}
 for tick in range(200):
  if h==len(pc)-1:
   if q==108 and pc[-1]=='1':
    shared.append((pc,op,arg));assert (op,arg,pc[-3:])in(('CB',1,'001'),('CC',2,'101'))
   break
  w,d,z=T[q,int(h in prefix_ones)]
  if w:prefix_ones.add(h)
  else:prefix_ones.discard(h)
  h+=d;q=z
 else:raise AssertionError(('Prefix decoder did not reach leaf',pc))
assert sum(op=='CB'for pc,op,arg in shared)==86 and sum(op=='CC'for pc,op,arg in shared)==8

def parse_frame(q,h,ones):
 if q!=84 or not ones or min(ones)!=h-1:return None
 candidates=[p for p in ones if p>=h+52]
 if not candidates:return None
 header=min(candidates)
 if header<h+64:return None
 pos=header+1;last=max(ones);values=[]
 while pos<last:
  if pos in ones or pos+1 not in ones:return None
  pos+=1;count=0
  while pos in ones:count+=1;pos+=1
  values.append(count-1)
 if pos!=last+1 or len(values)<10:return None
 return header,values
q=0;h=0;ones=set();start=time.monotonic();trace6=[]
for steps in range(1000001):
 frame=parse_frame(q,h,ones)if steps and q==84 else None
 if frame is not None and not any(h<=p<h+52 for p in ones):break
 assert steps<1000000 and q!=254
 b=int(h in ones);w,d,z=T[q,b]
 if steps<6:trace6.append([steps,q,h,b,w,d,z])
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d;q=z
header,values=frame;phy=(6,2,0,4,3,7,8,5,1);regs=[values[i]for i in phy];spares=values[9:]
assert steps==312617 and h==-5 and regs==[3,0,0,0,3,0,0,0,0]and header-h==144 and len(spares)==130 and set(spares)=={1};assert not any(h<=p<h+52 for p in ones)
result={'status':'INDEPENDENT_LITERAL_AUDIT_PASS','working_states':len(Q),'rows':len(T),'graph_reachable_working_states':len(reach),'start_state':0,'halt_state':254,'alphabet':[0,1],'table_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(args.sites.read_bytes()).hexdigest(),'source_leaf_occurrences':len(rows),'complete_source_tree':True,'shared108_CB1_suffix001':86,'shared108_CC2_suffix101':8,'boot':{'steps':steps,'state':q,'head':h,'pc_all_zero':True,'logical_registers':regs,'header_position':header,'header_distance':header-h,'gap':header-h-64,'spare_count':len(spares),'spare_values':spares,'ones':sorted(ones),'first_six_transitions':trace6},'seconds':time.monotonic()-start}
args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='boot'}));print('BOOT',steps,h,regs,header-h,len(spares))

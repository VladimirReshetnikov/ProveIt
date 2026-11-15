#!/usr/bin/env python3
"""Decode the actual complete startup frames used by the quadratic bound."""
from pathlib import Path
import argparse,json,hashlib
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'comparison'))
from verify_novelty import parse
ap=argparse.ArgumentParser();ap.add_argument('directories',nargs='+',type=Path);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=[]
PHY=(6,2,0,4,3,7,8,5,1)
for d in a.directories:
 rows,states,halt=parse(d/'machine.native.tm');receipt=json.loads((d/'receipt.json').read_text());n=receipt['startup']['steps'];q=74;head=0;ones=set()
 for _ in range(n):
  assert q!=halt
  w,m,q=rows[q,int(head in ones)]
  if w:ones.add(head)
  else:ones.discard(head)
  head+=1 if m=='R'else-1
 sites=json.loads((d/'sites.json').read_text());pc=sites[25][0]
 assert q==84 and head==-2 and head-1 in ones
 assert ''.join(str(int(head+j in ones))for j in range(len(pc)))==pc
 assert all(head+j not in ones for j in range(len(pc),48)) and head+48 in ones
 i=head+49;values=[]
 while i<=max(ones):
  assert i not in ones;i+=1;c=0
  while i in ones:c+=1;i+=1
  assert c>=1;values.append(c-1)
 primary=values[:9];logical=[primary[PHY[j]]for j in range(9)];spares=values[9:]
 assert logical==[2]+[0]*8 and spares==[1]*26
 expected={head-1,head+48}|{head+j for j,b in enumerate(pc)if b=='1'};i=head+49
 for v in values:expected.update(range(i+1,i+v+2));i+=v+2
 assert ones==expected
 out.append({'directory':str(d),'native_table_sha256':hashlib.sha256((d/'machine.native.tm').read_bytes()).hexdigest(),'literal_transitions':n,'native_state':q,'head':head,'source_instruction':25,'address':pc,'gap':0,'primary_registers':logical,'register_sum':sum(logical),'spare_count':len(spares),'first_spare':spares[0],'tail_width':sum(v+2 for v in spares[1:]),'whole_finite_support_checked':True,'ones':sorted(ones)})
r={'status':'PASS','results':out};a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({**r,'results':[{k:v for k,v in r.items()if k!='ones'}for r in out]},indent=2))

#!/usr/bin/env python3
"""Reach a site in the exact source execution and replay its literal frame."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent

def need(ok, msg):
 if not ok: raise ValueError(msg)
def load(name, path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
 lib=load('witness',HERE/'source_witness.py');rot=load('rot',lib.SOURCE/'scan_rotations.py');zero=load('zero',lib.SOURCE/'verify_zero_transfer.py')
 need(hashlib.sha256(lib.TABLE.read_bytes()).hexdigest()==lib.TABLE_HASH,'changed table')
 for file,digest in zero.PINS.items():need(hashlib.sha256((zero.UPSTREAM/file).read_bytes()).hexdigest()==digest,'changed source seed')
 physical_pins={
  'PA196/Startup/Data.lean':'25d47f0d22f6cfcf21f5f1a248b2a555fbe7ff1d8a6a8fd66ad3f8bb8f8c2690',
  'M6/Source/PhysicalRegisters.lean':'102490b3a2ca6b3b57f4e5b52b0409a66f8067b3231e9f48751a4162ecc7627f',
  'M6/Runtime.lean':'e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e',
  'PA196/PhysicalEndpoint.lean':'20cc824e2b18ba53e1c1a29b98d475bb9199e515312355d691a43e45bd34f94b'}
 for file,digest in physical_pins.items():need(hashlib.sha256((zero.UPSTREAM/file).read_bytes()).hexdigest()==digest,'changed physical runtime')
 graph=rot.graph(rot.root);other,_=zero.interval_graph(rot,rot.root);need(graph==other,'source resolvers differ')
 leaves=list(rot.leaf_occurrences(rot.root));pc=25;regs=[2]+[0]*8;inc=dec=0;source_trace=[]
 for step in range(32038):
  source_trace.append((pc,*regs))
  if pc==604:break
  row=graph[pc];op=row[0]
  if op=='dec':
   reg=row[1]
   if regs[reg]:regs[reg]-=1;pc=row[3];dec+=1
   else:pc=row[2]
  elif op=='inc':regs[row[1]]+=1;pc=row[2];inc+=1
  elif op=='jump':pc=row[1]
  else:raise ValueError('early source halt')
 need((step,pc,regs,inc,dec)==(32037,604,[4,1,75,0,0,0,0,0,0],10544,10466),'source reach mismatch')
 need(graph[604]==('dec',2,612,605),'wrong operation')
 permutation=[6,2,0,4,3,7,8,5,1];physical=[0]*9
 for i,j in enumerate(permutation):physical[j]=regs[i]
 tail=26+inc;initial_file=physical+[1]*tail;orig_file=initial_file.copy();orig_file[0]-=1
 child_file=initial_file.copy();child_file[8]+=1;child_file.append(1)
 start=lib.frame(leaves[604][0],initial_file,dec)
 orig_target=lib.frame(leaves[605][0],orig_file,dec+1)
 child_target=lib.frame(leaves[615][0],child_file,dec)
 rows={}
 for line in lib.TABLE.read_text().splitlines():
  q,b,w,d,n=line.split();key=(int(q),int(b));need(key not in rows and d in ('L','R'),'bad table');rows[key]=(int(w), -1 if d=='L' else 1,int(n))
 need(len(rows)==392 and rows[184,1]==(1,1,78),'unexpected table')
 runs=[]
 for candidate,horizon,target in ((False,84142,orig_target),(True,147964,child_target)):
  ones=set(start);q=75;head=0;hit=[];parent_target=[];h=hashlib.sha256()
  for t in range(horizon+1):
   if (q,head,ones)==(75,0,orig_target):parent_target.append(t)
   if q in (160,184,185,187):
    mask=sum(int(head+i in ones)<<(i+2) for i in range(-2,3));hit.append([t,q,head,int(head in ones),mask])
   if t==horizon:break
   need(q!=196,'unexpected halt');rd=int(head in ones);w,d,n=rows[q,rd]
   if candidate and (q,rd)==(184,1):w,d,n=1,-1,75
   if candidate and n==45:n=160
   h.update(f'{q} {head} {rd} {w} {d} {n}\n'.encode())
   ones.discard(head)
   if w:ones.add(head)
   head+=d;q=n
  need((q,head,ones)==(75,0,target),'full frame mismatch')
  need(parent_target==([] if candidate else [horizon]),'unexpected original target')
  need([31,184,27,1,6] in hit,'adverse configuration missing')
  runs.append({'candidate':candidate,'steps':horizon,'site':615 if candidate else 605,'marker_position':48+dec+(0 if candidate else 1),'file_first_nine':child_file[:9] if candidate else orig_file[:9],'trailing_ones':tail+(1 if candidate else 0),'parent_target_steps':parent_target,'affected_state_visits':hit,'transition_trace_sha256':h.hexdigest(),'final_ones_sha256':hashlib.sha256(json.dumps(sorted(ones),separators=(',',':')).encode()).hexdigest()})
 out={'table_sha256':lib.TABLE_HASH,'program_sha256':hashlib.sha256((zero.UPSTREAM/'PA196/Program.lean').read_bytes()).hexdigest(),'source_step':step,'source_site':pc,'logical_registers':regs,'physical_registers_first_nine':physical,'increments':inc,'positive_decrements':dec,'initial_marker_position':48+dec,'initial_trailing_ones':tail,'initial_ones_sha256':hashlib.sha256(json.dumps(sorted(start),separators=(',',':')).encode()).hexdigest(),'source_trace_sha256':hashlib.sha256(json.dumps(source_trace,separators=(',',':')).encode()).hexdigest(),'runs':runs}
 data=json.dumps(out,indent=2,sort_keys=True)+'\n';print(data,end='')
 if args.output:args.output.write_text(data)
if __name__=='__main__':main()

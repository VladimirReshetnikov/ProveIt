#!/usr/bin/env python3
"""Replay a source-reached frame against the alternative196 helper-fold near miss."""
from pathlib import Path
import argparse,hashlib,importlib.util,json
HERE=Path(__file__).resolve().parent;ALT=HERE.parent;UPSTREAM=HERE.parents[3]/'jamesyc-upstream/pa196'
def need(x,msg):
 if not x:raise ValueError(msg)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def frame(path,values,extra):
 need(extra>=0 and len(path)<=48,'frame size');ones={-1,48+extra}|{i for i,b in enumerate(path) if b};pos=49+extra
 for value in values:
  need(value>=0,'negative register');ones.update(range(pos+1,pos+value+2));pos+=value+2
 return ones
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);args=p.parse_args()
need(digest(ALT/'alternative196.tm')=='aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95','table SHA')
need(digest(ALT/'Program.lean')=='abc6f530495511226b17a9a2feff9a015c7bf972de292c241c6a15af0b490411','source SHA')
rot=load('alt_rot',ALT/'scan_rotations.py');zero=load('alt_zero',ALT/'verify_zero_transfer.py')
for name,expected in zero.PINS.items():need(digest(UPSTREAM/name)==expected,'seed source SHA')
physical_pins={'PA196/Startup/Data.lean':'25d47f0d22f6cfcf21f5f1a248b2a555fbe7ff1d8a6a8fd66ad3f8bb8f8c2690','M6/Source/PhysicalRegisters.lean':'102490b3a2ca6b3b57f4e5b52b0409a66f8067b3231e9f48751a4162ecc7627f','M6/Runtime.lean':'e66961d7acb60e0c84e9674ee2d91ca2049ac6d704ad0edf7d971ef933f3ce2e','PA196/PhysicalEndpoint.lean':'20cc824e2b18ba53e1c1a29b98d475bb9199e515312355d691a43e45bd34f94b'}
for name,expected in physical_pins.items():need(digest(UPSTREAM/name)==expected,'physical source SHA')
graph=rot.graph(rot.root);other,leaves=zero.interval_graph(rot,rot.root);need(graph==other and len(graph)==3812,'source resolver mismatch')
pc=25;regs=[2]+[0]*8;inc=dec=0;trace=[]
for step in range(32038):
 trace.append((pc,*regs))
 if pc==604:break
 row=graph[pc];op=row[0]
 if op=='dec':
  reg=row[1]
  if regs[reg]:regs[reg]-=1;pc=row[3];dec+=1
  else:pc=row[2]
 elif op=='inc':regs[row[1]]+=1;pc=row[2];inc+=1
 elif op=='jump':pc=row[1]
 else:raise ValueError('source halts early')
need((step,pc,regs,inc,dec)==(32037,604,[4,1,75,0,0,0,0,0,0],10544,10466),'source endpoint')
need(graph[604]==('dec',2,612,605),'source operation')
physical=[0]*9
for i,j in enumerate([6,2,0,4,3,7,8,5,1]):physical[j]=regs[i]
tail=26+inc;initial=physical+[1]*tail;parent_file=initial.copy();parent_file[0]-=1;child_file=initial.copy();child_file[8]+=1;child_file.append(1)
start=frame(leaves[604][0],initial,dec);parent_target=frame(leaves[605][0],parent_file,dec+1);child_target=frame(leaves[615][0],child_file,dec)
rows={}
for line in (ALT/'alternative196.tm').read_text().splitlines():
 q,b,w,d,z=line.split();key=(int(q),int(b));need(key not in rows and d in ('L','R'),'table row');rows[key]=(int(w),-1 if d=='L' else 1,int(z))
need(len(rows)==392 and rows[190,1]==(1,1,78),'helper row')
runs=[]
for candidate,horizon,target in ((False,84146,parent_target),(True,147968,child_target)):
 bits=set(start);q=75;head=0;hits=[];parent_target_hits=[];h=hashlib.sha256()
 for t in range(horizon+1):
  if (q,head)==(75,0) and bits==parent_target:parent_target_hits.append(t)
  if q==190 and head in bits and sum(int(head+i in bits)<<(i+2) for i in range(-2,3))==6:hits.append(t)
  if t==horizon:break
  need(q!=196,'early halt');read=int(head in bits);w,d,n=rows[q,read]
  if candidate and (q,read)==(190,1):w,d,n=1,-1,75
  if candidate and n==45:n=161
  h.update(f'{q} {head} {read} {w} {d} {n}\n'.encode());(bits.add if w else bits.discard)(head);head+=d;q=n
 need((q,head)==(75,0) and bits==target,'exact endpoint mismatch')
 need(parent_target_hits==([] if candidate else [horizon]),'unexpected parent endpoint')
 need(29 in hits,'adverse state not reached')
 runs.append({'candidate':candidate,'steps':horizon,'source_site':615 if candidate else 605,'marker_position':48+dec+(0 if candidate else 1),'file_first_nine':child_file[:9] if candidate else parent_file[:9],'trailing_ones':tail+(1 if candidate else 0),'parent_target_steps':parent_target_hits,'helper_190_read1_mask6_steps':hits,'transition_trace_sha256':h.hexdigest(),'final_ones_sha256':hashlib.sha256(json.dumps(sorted(bits),separators=(',',':')).encode()).hexdigest()})
result={'table_sha256':digest(ALT/'alternative196.tm'),'program_sha256':digest(ALT/'Program.lean'),'source_step':step,'source_site':pc,'logical_registers':regs,'physical_registers_first_nine':physical,'increments':inc,'positive_decrements':dec,'initial_marker_position':48+dec,'initial_trailing_ones':tail,'initial_ones_sha256':hashlib.sha256(json.dumps(sorted(start),separators=(',',':')).encode()).hexdigest(),'source_trace_sha256':hashlib.sha256(json.dumps(trace,separators=(',',':')).encode()).hexdigest(),'runs':runs,'scope':'Exact source execution and complete instruction-frame replay. The alternative physical and logical transport to this frame is not Lean certified here; the candidate may already diverge before reaching it.'}
args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2,sort_keys=True))

#!/usr/bin/env python3
"""Exact PA196 and candidate startup replay, including the decoded root frame."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
files={'original':'../allocator-screen/pa196.native.tm','candidate':'candidate.native.tm','sites':'../allocator-screen/one.json','original-sites':'../allocator-screen/original.json'}
pins={'original':'454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215','candidate':'9f8c37af1f206f17c5e6773df07a82d694b09454f295f53621fbb8ce00079f66','sites':'897984563bf6b6b0b5d6525e49da6357f5f1ad369a0536db13c2c9a4030bf38c','original-sites':'7204b25d70f0bc6fbc5fbb19d0ccdcb3fa88f9d63fa3610ca0b1c950617d34f9'}
def need(x,msg):
 if not x:raise ValueError(msg)
for name,file in files.items():
 need(hashlib.sha256((HERE/file).read_bytes()).hexdigest()==pins[name],name+' SHA mismatch')
def read(path):
 rows={};starts=[]
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line[9:]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b) not in rows,'duplicate row');rows[q,b]=(w,1 if d=='R' else -1,z)
 need(starts==[74],'start');return rows
original=read(HERE/files['original']);candidate=read(HERE/files['candidate'])
need({k for k in candidate if k not in original}=={(2000,0),(2000,1)},'new rows')
need({k for k in original if original[k]!=candidate.get(k)}=={(164,1)},'changed rows')
need(original[164,1]==(1,1,98) and candidate[164,1]==(1,1,2000),'dispatcher edit')
bits=[set(),set()];state=[74,74];head=[0,0];used=set()
for step in range(1,58155):
 for i,table in enumerate((original,candidate)):
  key=state[i],int(head[i] in bits[i])
  if i==0:used.add(key)
  w,d,nxt=table[key]
  (bits[i].add if w else bits[i].discard)(head[i]);head[i]+=d;state[i]=nxt
 need((state[0],head[0],bits[0])==(state[1],head[1],bits[1]),('startup divergent',step))
need(len(used)==237 and state[0]==84 and head[0]==-2,'startup conclusion')
ones={x-head[0] for x in bits[0]};need(-1 in ones and all(x>=-1 for x in ones),'left exterior')
sites=json.loads((HERE/files['sites']).read_text());oldsites=json.loads((HERE/files['original-sites']).read_text());need(sites[25]==oldsites[25]==['100000','CD',8],'site 25 path/op')
pc=sites[25][0];need([int(i in ones) for i in range(len(pc))]==list(map(int,pc)),'pc bits')
need(all(i not in ones for i in range(len(pc),48)) and 48 in ones,'gap and delimiter')
pos=49;blocks=[]
while pos<=max(ones):
 need(pos not in ones,'expected block zero');pos+=1;run=0
 while pos in ones:run+=1;pos+=1
 need(run>=1,'empty unary run');blocks.append(run-1)
need(blocks==[0,0,0,0,0,0,2,0,0]+[1]*26,('file blocks',blocks))
phy=(6,2,0,4,3,7,8,5,1);need([blocks[i] for i in phy]==[2]+[0]*8,'logical register seed')
print('PASS: identical 58154-step runs; 237 distinct startup rows')
print('root native 84, relative head 0, site 25 path 100000, header offset 48')
print('nine physical values:',blocks[:9],'; nonempty spares:',len(blocks[9:]),'all value 1')

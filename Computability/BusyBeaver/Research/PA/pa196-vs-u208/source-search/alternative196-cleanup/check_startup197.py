#!/usr/bin/env python3
"""Exact PA196 and candidate startup replay, including the decoded root frame."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
files={'original':'pa196.native.tm','candidate':'candidate197.native.tm','sites':'one.json','original-sites':'original.json'}
pins={'original':'a23cb60f8a60fc6f5aea3582c6fa95eca1d8e1956ca995eacff1170b0a66196b','candidate':'917f06ff5a3daa140e1c764010e567614ff18659bf5a5b096a692150768bc368','sites':'b37be5d0e932bd23b2442212d7462e5d7d3766955d6ba10490cc74a9ed7d0cef','original-sites':'b7959498f48961a79789123db3591f817edbd59875230306ff7068f1a1c60f0c'}
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
need({k for k in candidate if k not in original}=={(3000,0),(3000,1)},'new rows')
need({k for k in original if original[k]!=candidate.get(k)}=={(164,1)},'changed rows')
need(original[164,1]==(1,1,98) and candidate[164,1]==(1,1,3000),'dispatcher edit')
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

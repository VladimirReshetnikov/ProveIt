#!/usr/bin/env python3
"""Pin incoming archive, compare its literal program/table and derive startup protections."""
from pathlib import Path
from zipfile import ZipFile
import hashlib,json
HERE=Path(__file__).resolve().parent
archive=HERE.parents[6]/'docs/incoming/pa_tm_research_2026-11-13.zip'
def need(b,msg):
 if not b:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
need(sha(archive.read_bytes())=='6e6c4840cae029357d9fa47fd204cd953ae5af885e69250048d2941660d6a83f','archive SHA')
with ZipFile(archive) as z:
 base='pa_tm_research_2026-11-13/'
 for local,member in [('Program.lean','alternative196/Program.lean'),('alternative196.tm','alternative196/alternative196.tm'),('labels.json','alternative196/labels.json'),('LICENSE.JamesChang','alternative196/LICENSE'),('LICENSE.research','LICENSE.research')]:
  need((HERE/local).read_bytes()==z.read(base+member),'archive member mismatch: '+local)
 native=z.read(base+'alternative196/alternative196.native.tm');need((HERE/'pa196.native.tm').read_bytes()==b'#! start 74\n'+native,'native member mismatch')
need(sha(native)=='6a6caa6249fccc7cf8621058f0c7818a77435752a49b8f309629ff3a73ecdbfd','native SHA')
need(sha((HERE/'Program.lean').read_bytes())=='abc6f530495511226b17a9a2feff9a015c7bf972de292c241c6a15af0b490411','program SHA')
need(sha((HERE/'alternative196.tm').read_bytes())=='aa05f079326ae244c725d611fd50f8ed1e4e9519907e28788dbb2172deee1b95','literal SHA')
def rows(data):
 out={}
 for line in data.decode().splitlines():
  if line.startswith('#') or not line:continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b) not in out and d in ('L','R'),'row error');out[q,b]=(w,1 if d=='R' else -1,z)
 return out
sparse=rows(native);dense=rows((HERE/'alternative196.tm').read_bytes());labels=json.loads((HERE/'labels.json').read_text());need(len(labels)==197 and len(set(labels))==197 and labels[0]==74 and labels[-1]==254,'labels')
need(sparse=={(labels[q],b):(w,d,labels[z])for(q,b),(w,d,z)in dense.items()} and len(sparse)==392,'conjugacy')
q=74;head=0;bits=set();used=set()
for _ in range(58154):
 k=q,int(head in bits);used.add(k);w,d,q=sparse[k]
 (bits.add if w else bits.discard)(head);head+=d
core={tuple(map(int,l.split()))for l in (HERE/'protected-core.txt').read_text().splitlines() if l.strip()};given={tuple(map(int,l.split()))for l in (HERE/'protected-startup.txt').read_text().splitlines() if l.strip()}
need(len(core)==98 and len(used)==237 and len(core|used)==238 and given==core|used,'startup protection derivation')
print('PASS: pinned archive members, 392-row literal/native conjugacy, and 238 startup/core protection rows')

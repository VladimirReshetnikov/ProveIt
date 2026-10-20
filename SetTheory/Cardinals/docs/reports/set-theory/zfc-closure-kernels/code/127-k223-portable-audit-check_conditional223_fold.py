#!/usr/bin/env python3
"""Independent all-binary-tape 224->223 fold check. Imports only stdlib."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent.parent/'fold_binding';OUT=Path(__file__).with_name('conditional223_fold.json')
def need(x,m):
 if not x:raise ValueError(m)
def table(p):
 t={};start=[]
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):start.append(int(l[9:]));continue
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R'),'row syntax');t[q,b]=w,1 if d=='R'else-1,z
 need(start==[0],'start');need(set(t)=={(q,b)for q,_ in t for b in(0,1)},'incomplete rows');return t
old=table(P/'candidate.tm');new=table(P/'fold_0/candidate.tm');states={q for q,b in old};need(len(states)==224 and len(new)==446,'census');need({q for q,b in new}==states-{18},'state set');phi=lambda q:180 if q==18 else q
need(254 not in states and {z for w,d,z in old.values()}<=states|{254},'old targets');need({z for w,d,z in new.values()}<={q for q,b in new}|{254},'new targets')
for (q,b),(w,d,z)in old.items():
 if q not in(18,180):need(new[q,b]==(w,d,phi(z)),'ordinary row mismatch')
blocks=[]
for q,tag in((180,0),(18,1)):
 inc=[(p,b,w,d,z)for(p,b),(w,d,z)in old.items()if z==q];need(inc and all(w==tag and d==1 for p,b,w,d,z in inc),'incoming left tag')
 for bit in(0,1):
  cells={-1:tag,0:bit};initial=cells.copy();s=180;h=0;w,d,z=old[q,bit];expected=initial.copy();expected[0]=w;trace=[]
  for step in range(1,20):
   need(h in cells and(s,cells[h])in new,'special block escaped known cells');trace.append([s,h,cells[h]]);w,move,s=new[s,cells[h]];cells[h]=w;h+=move
   if(s,h,cells)==(phi(z),d,expected):break
  else:raise ValueError('no whole-tape endpoint')
  blocks.append(dict(old_state=q,read=bit,steps=step,trace=trace,whole_tape_endpoint_preserved=True))
result=dict(status='INDEPENDENT_ALL_BINARY_TAPE_223_FOLD_PASS',old_states=224,new_states=223,rows=446,start=0,halt=254,keep=180,drop=18,ordinary_rows=444,blocks=blocks,source_224_sha256=hashlib.sha256((P/'candidate.tm').read_bytes()).hexdigest(),candidate_223_sha256=hashlib.sha256((P/'fold_0/candidate.tm').read_bytes()).hexdigest(),scope='For every arbitrary binary initial tape at common state0, each old transition is simulated by a positive finite block with identical head and entire tape at mapped endpoint. Only states18/180 require the left tag, established by every incoming edge. Ordinary rows commute through phi. Thus halting is equivalent independently of source reachability.')
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

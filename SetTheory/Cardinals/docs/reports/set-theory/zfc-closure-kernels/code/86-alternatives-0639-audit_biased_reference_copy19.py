#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib,random
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;D=OUT.parent/'native_copier';sys.path.insert(0,str(D))
import biased_reference_copy as B
import biased_reference_copy19 as C

def parse(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in t
  t[q,b]=w,d,n
 return t
counts={};maxsteps=0
for variable in (False,True):
 old,os,oh,oi=B.compile_copy();new,ns,nh,ni=C.compile_copy(variable_anchor=variable)
 if variable:old[oi['after_anchor'],1]=(1,'R',oi['after_anchor'])
 qmap={v:ni[k]for k,v in oi.items()}|{oh:nh}
 forbidden={(oi['erase_first'],0),(oi['erase_second'],0),(oi['return_left'],1),(oi['add_loop'],1)}
 # Check quotient compatibility on EVERY nonexcluded row, not just tested runs.
 for(q,b),(w,d,n)in old.items():
  if(q,b)not in forbidden:assert new[qmap[q],b]==(w,d,qmap[n]),(q,b)
 filename='biased_reference_copy_19_variable_anchor.tm'if variable else'biased_reference_copy_19.tm'
 assert parse(D/filename)==new and nh==19 and len(new)==38
 count=0;seen=set()
 for r,length,gextra,alen,origin in itertools.product((0,1,2,3,9,25),range(4),(2,5),(1,2,7,19)if variable else(1,),(-11,13)):
  previous=tuple((j*3+length)%6 for j in range(length));g=r+gextra;c=origin;a=c+g+1
  tape={c}|set(range(a,a+alen));p=a+alen+1
  for v in previous:tape.update(range(p,p+v+1));p+=v+2
  s=p;tape.update(range(s+1,s+r+3));delimiter=s+r+3
  tape|={c-1,c-5,delimiter+1,delimiter+2,delimiter+9};expected=tape|{s}|set(range(c,c+r+1))
  q=os;head=s;steps=0
  while q!=oh:
   read=int(head in tape);assert(q,read)not in forbidden
   seen.add(qmap[q]);w,d,n=old[q,read]
   # Exact stepwise coupling: same tape/head and projected control state.
   assert new[qmap[q],read]==(w,d,qmap[n])
   if w:tape.add(head)
   else:tape.discard(head)
   head+=1 if d=='R'else-1;q=n;steps+=1;assert steps<1000000
  assert tape==expected and head==c+r
  maxsteps=max(maxsteps,steps);count+=1
 assert seen==set(range(19))-{ni['reject']}
 counts['variable_anchor'if variable else'unit_anchor']=count
result={'status':'PASS','working_states':19,'operational_states':18,'transition_rows':38,'quotient_nonexcluded_rows_checked':True,'forbidden_old_rows':4,'whole_tape_coupled_cases':counts,'max_steps':maxsteps,'anchor_lengths_tested':[1,2,7,19],
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[D/'biased_reference_copy19.py',D/'biased_reference_copy_19.tm',D/'biased_reference_copy_19_variable_anchor.tm']}}
(OUT/'biased_reference_copy19_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

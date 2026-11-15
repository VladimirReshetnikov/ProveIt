#!/usr/bin/env python3
"""Independently check all literal finite premises of the composite theorem.

Uses no construction code. Checks complete row lists, history invariants,
whole-tape local identities, dense/native conjugacy, and whole blank startup.
The generic quantifier-free induction proof is supplied separately.
"""
from pathlib import Path
import argparse,json,hashlib,itertools
D=Path(__file__).resolve().parent
PARENT_SHA={'AX11H':'6022711dcc0a025eb4b7a5a8f690d6b52f45f3d963a0868afef10962ccc49bd3','LC_AX11H':'e7800298659a5768a8aabfbd0cfd0ea42af241ed2a10b0cc1dbf64ed8aff1112'}
CHILD_SHA={'AX11H':'23fc656adc1afbe9e63f3a56df6e0c73a4f15a6d1493f2048aebaf00c9483ad2','LC_AX11H':'e9c6864d7fb452dff86a38e561f39a2dac0ddb873369fdfa3c1e7a88edcac7bf'}
START,HALT=74,254
PAIRS=((127,124,8,59),)
def rho(q):return {124:127}.get(q,q)
def read(p):
 r={}
 for line in p.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  ss=line.split();assert len(ss)==5
  q,b,w,d,n=ss;q,b,w,n=map(int,(q,b,w,n));assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in r
  r[q,b]=(w,1 if d=='R'else -1,n)
 s={q for q,b in r};assert len(s)==194 and len(r)==388 and set(r)=={(q,b)for q in s for b in(0,1)}
 return r

def shape(rows,start,halt):
 states={q for q,b in rows}
 assert len(states)==194 and halt not in states and start in states
 assert set(rows)=={(q,b)for q in states for b in(0,1)}
 assert {n for w,m,n in rows.values()}-states=={halt}
 seen={start};queue=[start]
 for q in queue:
  for b in(0,1):
   n=rows[q,b][2]
   if n!=halt and n not in seen:seen.add(n);queue.append(n)
 assert seen==states
 return {'working_states':194,'transition_rows':388,'start':start,'halt':halt,'all_states_reachable':True}

def step(rows,c):
 q,h,ones=c
 if q==HALT:return c
 w,m,n=rows[q,int(h in ones)]; ones=set(ones);(ones.add if w else ones.discard)(h)
 return n,h+m,ones

def local(rows,q,ones,length,window):
 c=(q,0,set(ones));trace=[]
 for _ in range(length):
  assert c[0]!=HALT and c[1]in window
  trace.append((c[0],c[1],int(c[1]in c[2])))
  c=step(rows,c)
 return c,trace

def check_selectors(old,sel):
 edits={q for l,r,u,v in PAIRS for q in(l,r)}
 providers={q for l,r,u,v in PAIRS for q in(u,v)}
 assert len(edits)==2 and not edits&providers and START not in edits
 incoming=[];cases=[]
 for l,r,u,v in PAIRS:
  assert old[l,0][:2]==old[r,0][:2]==(0,1)
  assert old[l,1]==old[r,1] and old[l,1][:2]==(1,1)
  assert old[u,0]==old[l,0]and old[v,0]==old[r,0]
  assert sel[l,0]==(0,-1,r)and sel[r,0]==(0,1,u)and sel[r,1]==(1,1,v)
  for q,bprev in((l,0),(r,1)):
   pred=[(p,b,w,m)for(p,b),(w,m,n)in sorted(old.items())if n==q]
   assert pred and all(w==bprev and m==1 for p,b,w,m in pred)
   incoming.append({'q':q,'left_bit':bprev,'all_predecessors':pred})
   for b in(0,1):
    ones={-1}if bprev else set()
    if b:ones.add(0)
    a,at=local(old,q,ones,1,{-1,0});z,zt=local(sel,rho(q),ones,3 if b==0 else 1,{-1,0})
    assert z==(rho(a[0]),a[1],a[2])
    cases.append({'old_state':q,'read':b,'left_bit':bprev,'new_steps':len(zt),'old_trace':at,'new_trace':zt,'whole_tape_equality':True})
 special={(l,0)for l,r,u,v in PAIRS}|{(r,b)for l,r,u,v in PAIRS for b in(0,1)}
 for k,(w,m,n)in old.items():
  if k not in special:assert sel[k]==(w,m,rho(n))
 assert sum(old[k]!=sel[k]for k in old)==4
 return {'incoming_invariant':incoming,'local_cases':cases,'ordinary_rows':len(old)-len(special),'time_old_to_selector':'3*t','time_selector_to_old':'t'}

def check_fast(sel,fast):
 pred=lambda q:[(p,b,w,m)for(p,b),(w,m,n)in sorted(sel.items())if n==q]
 assert pred(101)==[(96,0,0,1)]
 assert pred(26)==[(11,0,0,-1),(101,0,0,-1)]
 assert pred(11)and all(w==0 for p,b,w,m in pred(11))
 req={(101,0):(0,-1,26),(26,0):(0,1,194),(194,0):(0,1,17),(26,1):(1,1,42),(42,0):(0,1,13),(13,0):(0,-1,91)}
 for k,v in req.items():assert sel[k]==v
 assert START not in(101,26,11)and HALT not in(101,26,11,194,17,42,13,91)
 changes={(26,1):(1,1,91),(101,0):(0,1,17)}
 for k,v in sel.items():assert fast[k]==changes.get(k,v)
 cases=[]
 for bits in itertools.product((0,1),repeat=5):
  ones={i for i,b in zip(range(-2,3),bits)if b}
  for q in(26,101):
   guard=(0 in ones and 1 not in ones and 2 not in ones)if q==26 else(-1 not in ones and 0 not in ones)
   if not guard:continue
   a,at=local(sel,q,ones,3,set(range(-2,3)));b,bt=local(fast,q,ones,1,set(range(-2,3)));assert a==b
   cases.append({'state':q,'bits':bits,'selector_trace':at,'fast_trace':bt,'whole_tape_equality':True})
 assert len(cases)==12
 return {'pred101':pred(101),'pred26':pred(26),'pred11':pred(11),'cases':cases,'time_selector_to_fast':'t','time_fast_to_selector':'3*t'}

def check_startup(old,sel,fast,n):
 a=(START,0,set());b=(START,0,set());selector_steps=0;old_hits=[0]
 for tick in range(n):
  q,h,ones=a;bit=int(h in ones)
  for i,(l,r,u,v)in enumerate(PAIRS):
   if q in(l,r)and bit==0:old_hits[i]+=1
  duration=3 if q in(127,124)and bit==0 else 1
  a=step(old,a)
  for _ in range(duration):b=step(sel,b)
  selector_steps+=duration
  assert b==(rho(a[0]),a[1],a[2])
 assert a[:2]==(84,-2)
 f=(START,0,set());b=(START,0,set());clock=0;time=0;uses={26:0,101:0};edited_used={}
 while clock<selector_steps:
  q,h,ones=f;bit=int(h in ones);duration=3 if(q,bit)in((26,1),(101,0))else 1
  if duration==3:uses[q]+=1
  if old[q,bit]!=fast[q,bit]:edited_used[str((q,bit))]=edited_used.get(str((q,bit)),0)+1
  for _ in range(duration):b=step(sel,b)
  f=step(fast,f);clock+=duration;time+=1;assert f==b
 assert clock==selector_steps and f==(rho(a[0]),a[1],a[2])
 return {'parent_steps':n,'selector_steps':selector_steps,'fast_steps':time,'selector_insertions':old_hits,'accelerated_uses':uses,'complete_configuration_equality':True,'state':f[0],'head':f[1],'one_cells':sorted(f[2]),'changed_rows_used_in_startup':edited_used,'startup_all_time_claim':False}

def main():
 assert __debug__
 output=[]
 for name in('AX11H','LC_AX11H'):
  assert hashlib.sha256((D/'parents'/f'{name}.native.tm').read_bytes()).hexdigest()==PARENT_SHA[name]
  m=D/'machines'/('PA194'+name+'_SF');old=read(D/'parents'/f'{name}.native.tm');sel=read(m/'selector.native.tm');fast=read(m/'machine.native.tm');dense=read(m/'machine.tm');labels=json.loads((m/'labels.json').read_text())
  for table in(old,sel,fast):assert {n for w,z,n in table.values()}-{q for q,b in table}=={HALT}
  assert {n for w,z,n in dense.values()}-{q for q,b in dense}=={194}
  assert len(labels)==195 and len(set(labels))==195 and labels[0]==START and labels[-1]==HALT
  assert {(labels[q],b):(w,move,labels[n])for(q,b),(w,move,n)in dense.items()}==fast
  assert hashlib.sha256((m/'machine.tm').read_bytes()).hexdigest()==CHILD_SHA[name]
  shape(old,START,HALT);shape(sel,START,HALT);native_shape=shape(fast,START,HALT);dense_shape=shape(dense,0,194)
  result={'name':m.name,'status':'PASS','parent_native_sha256':hashlib.sha256((D/'parents'/f'{name}.native.tm').read_bytes()).hexdigest(),'dense_sha256':hashlib.sha256((m/'machine.tm').read_bytes()).hexdigest(),'state_count':194,'row_count':388,'native_shape':native_shape,'dense_shape':dense_shape,'pinned_parent_identity_checked':True,'pinned_child_identity_checked':True,'selector':check_selectors(old,sel),'fast':check_fast(sel,fast),'startup':check_startup(old,sel,fast,57922),'halting_witness_bounds':{'parent_to_composite':'3*t','composite_to_parent':'3*t'},'proof_status':'Finite premises for the written direct relative iPRA theorem; no completed Lean proof and no new absolute calibration.'}
  (m/'verification.json').write_text(json.dumps(result,indent=2)+'\n');output.append({'name':m.name,'hash':result['dense_sha256'],'startup':{k:v for k,v in result['startup'].items()if k!='one_cells'}})
 print(json.dumps(output,indent=2))
if __name__=='__main__':main()

#!/usr/bin/env python3
"""Focused independent source/schedule audit for the zero-spare Z215 seed.

Reads the pinned 4,751-row source as data. Does not import the parent schedule
program, source interpreters, or TM checker. Finite checks support the separate
all-natural argument in focused_review.md.
"""
import argparse,hashlib,json
from functools import lru_cache
from pathlib import Path

def unpair(n):
 d=0
 while (d+1)*(d+2)//2<=n:d+=1
 y=n-d*(d+1)//2
 return d-y,y

def descriptor(n):
 tag,y=unpair(n)
 if tag==0:return 'NIP',-1,y
 if tag==1:return 'DROP',1,y
 if tag==2:return 'MP',0,unpair(y)[1]
 return 'AX',10,unpair(unpair(y)[1])[1]

@lru_cache(None)
def word(n):
 name,delta,r=descriptor(n)
 assert r==0 or 0<=r-1<n
 return (delta,)+(word(r-1)if r else())

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 raw=a.source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 rows=json.loads(raw);paths={p:i for i,(p,op,arg)in enumerate(rows)}
 def target(prefix):
  for k in range(1,len(prefix)+65):
   p=(prefix+'0'*64)[:k]
   if p in paths:
    assert '1'not in prefix[k:]
    return paths[p]
  raise AssertionError('Incomplete source')
 def inc(p):return format((int(p,2)+1)%2**len(p),f'0{len(p)}b')if p else''
 def cut(p,b,k):
  hits=[i for i,v in enumerate(p)if v==b]
  return p[:hits[-k]]if len(hits)>=k else''
 graph=[]
 for p,op,k in rows:
  if op=='CI':successors=[target(inc(p))]
  elif op=='CD':successors=[target(inc(cut(p,'0',1))),target(inc(p))]
  elif op=='CB':successors=[target(inc(cut(p,'0',k)))]
  elif op=='CC':successors=[target(cut(p,'1',k))]
  else:assert op=='CH';successors=[]
  graph.append(successors)
 assert len(rows)==4751
 # Exact live-tail accesses, including the common selector read.
 expected_l_ops=[(0,'CD'),(3,'CI'),(9,'CD'),(18,'CI'),(159,'CD'),(168,'CI'),(200,'CD'),(209,'CI'),(4591,'CD'),(4600,'CI')]
 actual_l_ops=[(i,op)for i,(p,op,k)in enumerate(rows)if k==8 and op in('CD','CI')]
 assert actual_l_ops==expected_l_ops
 actual_n_ops=[(i,op)for i,(p,op,k)in enumerate(rows)if k==0 and op in('CD','CI')]
 assert actual_n_ops==[(2,'CD'),(6,'CI')]
 starts=[9,159,200,4591]
 signature=[(op,k)for p,op,k in rows[9:20]]
 normalized=[]
 for start in starts:
  assert[(op,k)for p,op,k in rows[start:start+11]]==signature
  g=[[t-start for t in graph[i]]for i in range(start,start+11)]
  normalized.append(g)
  assert all(0<=t<=11 for out in g for t in out)
 assert all(g==normalized[0]for g in normalized)
 assert [rows[start+12][2]for start in starts]==[3,5,4,4]
 # NIP0, DROP1, MP2; selector>=3 enters AX with residual selector-3.
 command_entry={4725:'NIP',4698:'DROP',4591:'MP',26:'AX'}
 for selector in range(4):
  pc=23;v=selector;tests=[]
  while pc not in command_entry:
   assert rows[pc][1:]==['CD',3];tests.append(pc)
   pc=graph[pc][bool(v)]
   if v:v-=1
  assert command_entry[pc]==['NIP','DROP','MP','AX'][selector]
  assert tests==[23,24,25][:min(selector+1,3)]and v==0
 # Exact test of cache1 occurs before any stack read in NIP.
 assert rows[4736][1:] == ['CH',None]
 assert rows[4737][1:] == ['CD',2]
 assert all(k!=2 or op not in('CI','CD')for p,op,k in rows[4725:4737])
 def source_step(pc,regs):
  p,op,k=rows[pc]
  if op=='CH':return None
  if op=='CI':regs[k]+=1;return graph[pc][0]
  if op=='CD':
   positive=regs[k]>0
   if positive:regs[k]-=1
   return graph[pc][positive]
  return graph[pc][0]
 # A literal cache1 path establishes that the only halt precedes the pop.
 test_regs=[0,0,123,0,0,1,0,0,0];pc=4725;cache1_path=[]
 while pc is not None:
  cache1_path.append(pc);pc=source_step(pc,test_regs)
 assert cache1_path==[4725,4726,4727,4728,4726,4730,4736]
 assert test_regs[2]==123
 # Concrete early execution binds fetch/continuation conventions to source.
 regs=[1,0,5,0,0,0,0,0,0];early=[]
 for count in range(30):
  n=regs[0]if regs[8]==0 else regs[8]-1
  if regs[8]==0 and n>=6:break
  name,delta,remainder=descriptor(n);before=regs.copy();pc=0;seen_entry=None;steps=0
  while True:
   if pc in command_entry:
    assert seen_entry is None
    seen_entry=command_entry[pc];assert seen_entry==name
    assert regs[8]==unpair(n)[1]
   pc=source_step(pc,regs);steps+=1
   assert steps<100000 and pc is not None
   if pc==0:break
  assert seen_entry==name and regs[8]==remainder
  assert regs[3]==regs[6]==regs[7]==0
  early.append({'decoded_word_number':n,'command':name,'before':before,'after':regs.copy(),'source_steps':steps})
 else:raise AssertionError('Early-source bound exhausted')
 assert regs[0]==6 and regs[8]==0
 # Directly flatten every base word, unlike the parent's b/m recurrence.
 total=0;lowest=0;complete=[];commands=0
 for n in range(666):
  w=word(n);assert len(w)<=n+1
  for d in w:total+=d;lowest=min(lowest,total);commands+=1
  complete.append(total)
  if n>=6:assert total>=7
 assert lowest==-3 and min(complete[6:])==7 and complete[-1]==5762
 total=0;from_one=0
 for n in range(1,666):
  for d in word(n):total+=d;from_one=min(from_one,total)
 assert from_one==-2
 small=[0,-1,0,-2,-2,-2,-2]
 def p(t):return small[t]if t<7 else 7
 def q(t):
  x,y=unpair(t);s=x+y
  return sum(p(j)for j in range(s))+p(y)
 qbase=[q(t)for t in range(45)]
 assert min(qbase)==-11 and sum(v for v in qbase if v<0)==-224
 ax_total=0;ax_minimum=0
 for k in range(26):
  suffix=unpair(unpair(k)[1])[1]
  for d in(10,)+(word(suffix-1)if suffix else()):
   ax_total+=d;ax_minimum=min(ax_minimum,ax_total)
 assert ax_minimum==0
 assert unpair(5)==(0,2)and unpair(2)==(0,1)
 receipt={'status':'PASS','source_sha256':hashlib.sha256(raw).hexdigest(),'reviewer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'scope':'Independent finite source arity/selector/read-before-halt audit and complete induction base; the all-natural extension is ordinary mathematics in focused_review.md.',
  'source_sites':4751,'literal_L_accesses':actual_l_ops,'literal_N_accesses':actual_n_ops,'same_unpair_macro_starts':starts,
  'extra_field_arities':{'NIP':0,'DROP':0,'MP':1,'AX':2},'NIP_cache1_path':cache1_path,
  'base_candidates':666,'base_commands':commands,'complete_base_final_balance':complete[-1],
  'minimum_global_prefix_from_0':lowest,'minimum_global_prefix_from_1':from_one,
  'minimum_complete_balance_after_6':min(complete[6:]),'q_minimum':min(qbase),'q_negative_sum':sum(v for v in qbase if v<0),'AX_prefix_cases':26,'AX_prefix_minimum':ax_minimum,'early_source_commands':early,
  'early_final_registers':regs}
 a.out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='early_source_commands'},indent=2))

if __name__=='__main__':main()

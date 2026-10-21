#!/usr/bin/env python3
"""Exact finite source audit for the shared-CB refill scheduler.

Usage: python check_refill_source.py accepted.sites.json proposed.sites.json
The theorem for all natural register values is in scheduler_section.tex.
This checker establishes its literal CFG premises; finite spot checks are
reported separately and are not the all-natural proof.
"""
import argparse,hashlib,json
from pathlib import Path

def graph(rows):
 leaves={p:i for i,(p,op,a)in enumerate(rows)}
 assert len(leaves)==len(rows)
 D=max(map(len,leaves));count=0
 def locate(pref):
  nonlocal count
  word=pref+'0'*D
  for j in range(1,D+1):
   if word[:j]in leaves:
    assert '1'not in pref[j:]
    count+=1;return leaves[word[:j]]
  raise AssertionError('not complete')
 def cut(p,b,k):
  at=[i for i,x in enumerate(p)if x==b]
  return p[:at[-k]]if len(at)>=k else ''
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else ''
 out=[]
 for p,op,a in rows:
  if op=='CI':targets=[locate(inc(p))]
  elif op=='CD':targets=[locate(inc(cut(p,'0',1))),locate(inc(p))]
  elif op=='CB':targets=[locate(inc(cut(p,'0',a)))]
  elif op=='CC':targets=[locate(cut(p,'1',a))]
  else:assert op=='CH';targets=[]
  out.append(targets)
 return out,count

def main():
 p=argparse.ArgumentParser();p.add_argument('accepted');p.add_argument('proposed');p.add_argument('--output');a=p.parse_args()
 oldraw=Path(a.accepted).read_bytes();newraw=Path(a.proposed).read_bytes();old=json.loads(oldraw);new=json.loads(newraw)
 bg,bc=graph(old);ng,nc=graph(new)
 assert len(old)==4751 and len(new)==4752
 actions=[['CD',8],['CB',1],['CD',0],['CI',8],['CI',6],['CC',3],['CI',0],['CD',6],['CC',2],['CB',1]]
 assert [x[1:]for x in new[:10]]==actions
 assert ng[:10]==[[2,1],[10],[6,3],[4],[5],[2],[7],[9,8],[6],[0]]
 assert [x[1:]for x in old[:9]]==actions[:9]
 assert bg[:9]==[[2,1],[9],[6,3],[4],[5],[2],[7],[9,8],[6]]
 assert new[10:]==old[9:]
 shift=lambda i:i+1 if i>=9 else i
 for i in range(9,len(old)):assert ng[i+1]==list(map(shift,bg[i]))
 assert all(op not in ['CI','CD']or a!=0 for _,op,a in new[10:]),'B touches candidate counter'
 # Direct checks of the derived source clock at representative inputs.
 checks=0
 for n in [0,1,2,10,100]:
  for ell in [0,1,5]:
   r=[n,17,8,0,4,9,0,0,ell];k=steps=0
   while k!=10:
    assert steps<10000
    _,op,arg=new[k]
    if op=='CD':b=int(r[arg]>0);r[arg]-=b;k=ng[k][b]
    elif op=='CI':r[arg]+=1;k=ng[k][0]
    else:k=ng[k][0]
    steps+=1
   assert r==[n if ell else n+1 if n else 2,17,8,0,4,9,0,0,ell-1 if ell else n-1 if n else 0]
   assert steps==(2 if ell else 7*n+7 if n else 19)
   checks+=1
 # The actual CB1-table seed executes one harmless MP(0), returning to
 # the new root with N=5,L=0, hence the accepted seed N=4 under the relation.
 r=[5,0,0,0,0,0,0,0,4];k=steps=0
 while steps==0 or k!=0:
  assert steps<100000
  _,op,arg=new[k]
  assert op!='CH','unexpected halt in actual seed reduction'
  if op=='CD':b=int(r[arg]>0);r[arg]-=b;k=ng[k][b]
  elif op=='CI':r[arg]+=1;k=ng[k][0]
  else:k=ng[k][0]
  steps+=1
 assert r==[5,0,0,0,0,0,0,0,0]
 seed_steps=steps
 receipt={'status':'EXACT_SOURCE_PREMISES_PASS','accepted_sha256':hashlib.sha256(oldraw).hexdigest(),'proposed_sha256':hashlib.sha256(newraw).hexdigest(),'accepted_leaves':len(old),'proposed_leaves':len(new),'tail_literal_identity':True,'tail_all_control_edges_preserved':True,'tail_does_not_touch_counter':True,'no_stray_successor_checks':{'accepted':bc,'proposed':nc},'spot_checks':checks,'actual_seed_reduction':{'initial':[5,0,0,0,0,0,0,0,4],'final':[5,0,0,0,0,0,0,0,0],'source_steps':seed_steps,'command':'MP(0)'},'proof_scope':'Exact finite CFG premises plus separately stated all-natural scheduler proof; spot checks are not the proof.'}
 if a.output:Path(a.output).write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()

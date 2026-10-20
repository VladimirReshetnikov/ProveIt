#!/usr/bin/env python3
"""Widen the second closed splice and beam-reassociate its fixed factors."""
from pathlib import Path
from collections import defaultdict
from functools import cache
import json,time,sys
sys.dont_write_bytecode=True
import source_language as s,measure_pinned as m
P=Path(__file__).resolve().parent;plan=json.loads((P/'input.json').read_text());dp=json.loads((P/'dp-result.json').read_text());start=time.monotonic()
original=s.tree(json.loads((Path(plan['seed'])/'sites218.json').read_text()))
rawnodes=[];ids={}
for i,row in enumerate(plan['nodes']):
 t=tuple(row['leaf'])if'leaf'in row else tuple(rawnodes[x]for x in row['children']);rawnodes.append(t);ids[t]=i
H0=('HOLE',0);H1=('HOLE',1)
skeleton=m.splice(s,m.splice(s,original,648,4433,H1),135,486,H0)
def forest(n,lo,hi,i=0):
 j=i+len(m.flat(n))
 if j<=lo or i>=hi:return []
 if lo<=i and j<=hi:return [n]
 return forest(n[0],lo,hi,i)+forest(n[1],lo,hi,i+len(m.flat(n[0])))
def lead(t):return 0 if s.leaf(t)else 1+lead(t[0])
def split(t):
 assert s.boundary(t)==(0,0,False)
 if lead(t)<=5:return[t]
 assert not s.leaf(t)and s.boundary(t[0])==s.boundary(t[1])==(0,0,False)
 return split(t[0])+split(t[1])
prefix=sum((split(t)for t in forest(original,648,1474)),[]);suffix=sum((split(t)for t in forest(original,1773,4433)),[])
base=set()
def fixed(t):
 if t in(H0,H1):return
 if t in ids:
  base.add(ids[t])
 if not s.leaf(t):fixed(t[0]);fixed(t[1])
fixed(skeleton)
for t in prefix+suffix:fixed(t)
nodes=[];pairs={}
for i,row in enumerate(plan['nodes']):
 if 'leaf'in row:n={'tree':row,'lead':0,'z':0,'depth':0,'added':frozenset()if i in base else frozenset([i])}
 else:
  l,r=row['children'];ld=nodes[l]['lead']+1;n={'tree':row,'lead':ld,'z':max(ld,nodes[l]['z'],nodes[r]['z']),'depth':1+max(nodes[l]['depth'],nodes[r]['depth']),'added':nodes[l]['added']|nodes[r]['added']|(frozenset()if i in base else frozenset([i]))};pairs[(l,r)]=i
 nodes.append(n)
initial=len(nodes)
def pair(l,r):
 if(l,r)in pairs:return pairs[l,r]
 i=len(nodes);ld=nodes[l]['lead']+1
 nodes.append({'tree':{'children':[l,r]},'lead':ld,'z':max(ld,nodes[l]['z'],nodes[r]['z']),'depth':1+max(nodes[l]['depth'],nodes[r]['depth']),'added':nodes[l]['added']|nodes[r]['added']|{i}});pairs[l,r]=i;return i
def restore(e):return e if type(e)==int else pair(restore(e[0]),restore(e[1]))
byword=defaultdict(list)
for c in dp['candidates']:byword[c['word']].append(restore(c['replacement']))
def expr(t):
 if t==H0:return 'H0'
 if t==H1:return 'H1'
 if t in ids:return ids[t]
 return[expr(t[0]),expr(t[1])]
sk=expr(skeleton)
def whole(e,a,b):
 if e=='H0':return a
 if e=='H1':return b
 if type(e)==int:return e
 return pair(whole(e[0],a,b),whole(e[1],a,b))
def serial(i):return i if i<initial else[serial(x)for x in nodes[i]['tree']['children']]
jointrials=0
def trim(cands):
 buckets=defaultdict(list)
 for k in set(cands):
  n=nodes[k]
  if n['z']<=6:buckets[n['lead']].append(k)
 return sum((sorted(v,key=lambda k:(len(nodes[k]['added']),nodes[k]['depth'],k))[:3]for v in buckets.values()),[])
wide={}
for word in sorted(w for w in byword if plan['recipes'][w]['kind']=='mixed_rho4'):
 atoms=[[ids[t]]for t in prefix]+[byword[word]]+[[ids[t]]for t in suffix];n=len(atoms);cells={(i,i+1):trim(a)for i,a in enumerate(atoms)}
 for length in range(2,n+1):
  for i in range(n-length+1):
   j=i+length;c=[]
   for k in range(i+1,j):
    for l in cells[i,k]:
     for r in cells[k,j]:
      jointrials+=1
      if nodes[l]['lead']<6:c.append(pair(l,r))
   cells[i,j]=trim(c)
  assert time.monotonic()-start<120,'Bounded outer DP deadline'
 wide[word]=cells[0,n]
 print('wide',word,len(wide[word]),min([len(base)+len(nodes[k]['added'])for k in wide[word]],default=None),flush=True)
best=[];seen=set();trials=valid=0
for wa,wb in plan['joint_recipes']:
 for a in byword[wa]:
  for b in wide[wb]:
   trials+=1;root=whole(sk,a,b);n=nodes[root]
   if n['z']>6:continue
   valid+=1
   if root in seen:continue
   seen.add(root);score=(len(base)+len(n['added']),n['depth'])
   if len(best)<16 or score<best[-1][0]:
    best.append((score,{'KS_word':wa,'M_word':wb,'KS_replacement':serial(a),'wide_M_replacement':serial(b),'dag_nodes':score[0],'maximum_depth':n['depth'],'maximum_zero_run':n['z']}));best.sort(key=lambda x:x[0]);best=best[:16]
result={'status':'WIDENED_CLOSED_SPLICE_BEAM_SCORED','recipes':len(plan['joint_recipes']),'outer_DP_join_trials':jointrials,'beam_per_leading':3,'prefix_factor_count':len(prefix),'suffix_factor_count':len(suffix),'fixed_base_nodes':len(base),'replacement':[[135,486],[648,4433]],'trials':trials,'zero_compatible':valid,'distinct_global_trees':len(seen),'interned_nodes':len(nodes),'seconds':time.monotonic()-start,'candidates':[x[1]for x in best],'scope':'Found candidates under bounded beam search, not optimum. Exact global subtree census; source/CFG/semantic validation and allocator acceptance remain separate. M calibration has ordinary source review, no kernel or machine claim.'}
(P/'joint-v2-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='candidates'}));print([(c['dag_nodes'],c['maximum_zero_run'],c['KS_word'],c['M_word'])for c in result['candidates']])

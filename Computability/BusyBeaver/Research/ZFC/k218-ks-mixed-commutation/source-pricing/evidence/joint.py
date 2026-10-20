#!/usr/bin/env python3
"""Exact global unique-subtree scoring of two independently optimized closed splices."""
from pathlib import Path
from collections import defaultdict
import json,time
P=Path(__file__).resolve().parent;plan=json.loads((P/'input.json').read_text());dp=json.loads((P/'dp-result.json').read_text())
nodes=[];pairs={};base=set(plan['base_nodes']);start=time.monotonic()
for i,row in enumerate(plan['nodes']):
 if 'leaf'in row:n={'tree':row,'lead':0,'z':0,'depth':0,'added':frozenset()if i in base else frozenset([i])}
 else:
  l,r=row['children'];lead=nodes[l]['lead']+1;n={'tree':row,'lead':lead,'z':max(lead,nodes[l]['z'],nodes[r]['z']),'depth':1+max(nodes[l]['depth'],nodes[r]['depth']),'added':nodes[l]['added']|nodes[r]['added']|(frozenset()if i in base else frozenset([i]))};pairs[(l,r)]=i
 nodes.append(n)
initial=len(nodes)
def pair(l,r):
 if(l,r)in pairs:return pairs[l,r]
 i=len(nodes);lead=nodes[l]['lead']+1
 nodes.append({'tree':{'children':[l,r]},'lead':lead,'z':max(lead,nodes[l]['z'],nodes[r]['z']),'depth':1+max(nodes[l]['depth'],nodes[r]['depth']),'added':nodes[l]['added']|nodes[r]['added']|{i}});pairs[l,r]=i;return i
def restore(e):return e if type(e)==int else pair(restore(e[0]),restore(e[1]))
byword=defaultdict(list)
for c in dp['candidates']:
 k=restore(c['replacement']);byword[c['word']].append(k)
def whole(e,a,b):
 if e=='H0':return a
 if e=='H1':return b
 if type(e)==int:return e
 return pair(whole(e[0],a,b),whole(e[1],a,b))
def serial(i):return i if i<initial else [serial(x)for x in nodes[i]['tree']['children']]
best=[];seen=set();trials=0;valid=0
for wa,wb in plan['joint_recipes']:
 for a in byword[wa]:
  for b in byword[wb]:
   trials+=1;root=whole(plan['skeleton_expression'],a,b);n=nodes[root]
   if n['z']>6:continue
   valid+=1
   if root in seen:continue
   seen.add(root);score=(len(base)+len(n['added']),n['depth'])
   if len(best)<16 or score<best[-1][0]:
    best.append((score,{'KS_word':wa,'M_word':wb,'KS_replacement':serial(a),'M_replacement':serial(b),'dag_nodes':score[0],'maximum_depth':n['depth'],'maximum_zero_run':n['z']}));best.sort(key=lambda x:x[0]);best=best[:16]
result={'status':'CONDITIONAL_MIXED_MODAL_JOINT_DP_SCORED','recipes':len(plan['joint_recipes']),'trials':trials,'zero_compatible':valid,'distinct_global_trees':len(seen),'interned_nodes':len(nodes),'seconds':time.monotonic()-start,'candidates':[x[1]for x in best],'scope':'Exact global subtree census for two closed splices. Mathematical calibration of mixed M is pending; no machine/compiler/runtime claim.'}
(P/'joint-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='candidates'}));print([(c['dag_nodes'],c['maximum_zero_run'],c['KS_word'],c['M_word'])for c in result['candidates']])

#!/usr/bin/env python3
"""Exact compatibility-sensitive certificate for the inherited nine-plan menu.
Standard library; independently reconstructs all support vectors.
"""
from itertools import combinations,permutations,product
from fractions import Fraction as F
from pathlib import Path
import json,time,math
PLANS=[
[[7,4,3,9],[1,6,0],[8,2,5]],
[[5,4,6,7],[9,1,8],[2,3,0]],
[[0,5,9,7],[2,1,4],[8,3,6]],
[[0,4,7,8],[2,9,6],[1,5,3]],
[[3,1,7,2],[9,6,8],[5,4,0]],
[[7,1,5,8],[2,9,4],[0,6,3]],
[[7,2,8,6],[5,9,3],[0,1,4]],
[[1,9,6,7],[2,5,0],[4,3,8]],
[[4,6,1,5],[8,9,2],[0,7,3]]]
W=[137,124,135,120,108,119,106,87,64]
SCALE=1400000
TRIPLES=sorted(set(permutations((1400007,1400007,0)))|set(permutations((1400000,1175014,750000))))
EDGES=list(combinations(range(10),2))
def require(c,m):
 if not c:raise ValueError(m)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def supports(plan):
 require(sorted(sum(plan,[]))==list(range(10)),'partition')
 operations=[]
 def build(block):
  if len(block)==1:return
  t=len(block)//2;A=block[:t];B=block[t:]
  build(A);build(B)
  operations.append((set(A),set(B),set(range(10))-set(block)))
 for b in plan:build(b)
 operations.append(tuple(map(set,plan)))
 rows=[]
 for parts in operations:
  label={v:i for i,p in enumerate(parts) for v in p}
  for triple in TRIPLES:
   vals=dict(zip(((0,1),(0,2),(1,2)),triple))
   rows.append(tuple(0 if label[a]==label[b] else vals[tuple(sorted((label[a],label[b])))] for a,b in EDGES))
 require(len(rows)==72,'support count')
 return rows

def certificate():
 menus=[supports(plan) for plan in PLANS]
 vectors=[[tuple(w*x for x in row) for row in menu] for w,menu in zip(W,menus)]
 norms=[[dot(v,v) for v in menu] for menu in vectors]
 pair_scores={};pair_max={};conditioned={}
 for i,j in combinations(range(9),2):
  table=[[norms[i][a]+norms[j][b]+16*dot(v,z) for b,z in enumerate(vectors[j])] for a,v in enumerate(vectors[i])]
  pair_scores[i,j]=table
  pair_max[i,j]=max(map(max,table))
  conditioned[i,j]=list(map(max,table))
  conditioned[j,i]=[max(table[a][b] for a in range(72)) for b in range(72)]
 old_upper_numerator=sum(pair_max.values())
 witness=(67,67,69,69,67,69,67,69,69)
 def norm_for(choice):
  value=[sum(vectors[i][j][e] for i,j in enumerate(choice)) for e in range(45)]
  return dot(value,value)
 target=norm_for(witness)
 kept=[];exclusion_max=[];conditional_bounds=[]
 for i in range(9):
  baseline=sum(v for (j,k),v in pair_max.items() if i not in (j,k))
  scores=[baseline+sum(conditioned[i,j][a] for j in range(9) if j!=i) for a in range(72)]
  keep=[a for a in range(72) if scores[a]>=8*target]
  kept.append(keep)
  exclusion_max.append(max([scores[a] for a in range(72) if a not in keep],default=0))
  conditional_bounds.append(scores)
 require(all(x<8*target for x in exclusion_max),'elimination margin')
 checked=0;actual=0;actual_witness=None
 for choice in product(*kept):
  value=norm_for(choice);checked+=1
  require(value<=target,'survivor exceeds target')
  if value>actual:actual,actual_witness=value,choice
 require(actual==target,'matching witness')
 b2=F(2*target,SCALE*SCALE*sum(W)**2*100)
 old_b2=F(2*old_upper_numerator,8*SCALE*SCALE*sum(W)**2*100)
 require(b2<old_b2,'strict improvement')
 return {'status':'PASS','support_count':648,'pair_choices':36*72**2,
 'scale':SCALE,'weights':W,'target_squared_norm':target,'witness':list(actual_witness),
 'surviving_indices':kept,'surviving_tuples':checked,'maximum_excluded_pair_numerator':max(exclusion_max),
 'exclusion_numerators':exclusion_max,'threshold_pair_numerator':8*target,
 'b_squared':str(b2),'old_b_squared':str(old_b2),
 'old_pair_sum':old_upper_numerator,'conditional_bounds':conditional_bounds}

if __name__=='__main__':
 t=time.time();out=certificate()
 print(json.dumps(out,indent=2))

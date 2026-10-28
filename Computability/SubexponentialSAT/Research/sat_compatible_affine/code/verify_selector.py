#!/usr/bin/env python3
"""Finite exact selector and contraction semantics checks.

This is a scalar prototype over Z/8Z, not an implementation of asymptotic
matrix multiplication or a SAT solver. Mode dimensions in these fixtures
are powers of two, so the exact support-product selector compares integer
binary exponents instead of constructing enormous powers. An empty mode
list contributes zero before selection.
"""
from fractions import Fraction as F
from itertools import combinations,permutations,product
from math import lcm
from pathlib import Path
import json,random

R=10;MOD=8
PAIRS=list(combinations(range(R),2))
ALPHA=F(321333,1000000);OMEGA=F(2371553,1000000);EPS=F(1,1000000)
K=F(59261,103891);AK=F(26972100941,12986375000)
D=1+EPS/2;C=(OMEGA-1)/2;W=(AK-2-EPS)/(K-ALPHA);V=1+EPS-ALPHA*W
SCALE=lcm(D.denominator,C.denominator,V.denominator,W.denominator)
TRIPLES=sorted(set(permutations((int(D*SCALE),int(D*SCALE),0)))|
               set(permutations((SCALE,int(V*SCALE),int(W*SCALE))))|
               set(permutations((SCALE,int(C*SCALE),int(C*SCALE)))))

def require(c,m):
 if not c:raise RuntimeError(m)

def plans():
 out=[]
 for a,b in [(1,0),(0,1),(1,1),(1,2)]:
  lines=[[3*x+y for x in range(3)for y in range(3)if(a*x+b*y)%3==level]for level in range(3)]
  for k in range(3):out.append([lines[k]+[9]]+[lines[j]for j in range(3)if j!=k])
 return out

def integer_supports(plan):
 ops=[]
 def visit(block):
  if len(block)==1:return
  mid=len(block)//2;A=block[:mid];B=block[mid:]
  visit(A);visit(B);ops.append((set(A),set(B),set(range(R))-set(block)))
 for b in plan:visit(b)
 ops.append(tuple(map(set,plan)))
 rows=[]
 for A,B,O in ops:
  for a,b,c in TRIPLES:
   rows.append(tuple(a if (x in A and y in B)or(x in B and y in A)else
                     b if (x in A and y in O)or(x in O and y in A)else
                     c if (x in B and y in O)or(x in O and y in B)else 0
                     for x,y in PAIRS))
 require(len(rows)==96,'operation support count')
 return rows
MENUS=[integer_supports(p)for p in plans()]

def select_plan(dimensions):
 require(len(dimensions)==45,'one dimension for each unordered pair')
 require(all(type(d)is int and d>=0 for d in dimensions),'nonnegative integer dimensions')
 if 0 in dimensions:return None,None
 require(all(d&(d-1)==0 for d in dimensions),'fixture selector requires dyadic dimensions')
 logs=[d.bit_length()-1 for d in dimensions]
 scores=[max(sum(a*b for a,b in zip(v,logs))for v in menu)for menu in MENUS]
 chosen=min(range(12),key=lambda i:(scores[i],i))
 return chosen,scores

def make_factors(active,kind,seed):
 rng=random.Random(seed)
 incident=[[i for i,e in enumerate(active)if v in e]for v in range(R)]
 factors=[]
 for v,inc in enumerate(incident):
  table={}
  for bits in product((0,1),repeat=len(inc)):
   if not inc:value=1
   elif kind=='equal':value=int(len(set(bits))<=1)
   elif kind=='point':value=(3 if v==0 else 1)*int(all(b==0 for b in bits))
   elif kind=='unit':value=1
   else:value=rng.randrange(8)
   table[bits]=value%MOD
  factors.append((tuple(inc),table))
 return factors

def brute_force(active,factors):
 total=0
 for bits in product((0,1),repeat=len(active)):
  value=1
  for inc,table in factors:value=value*table[tuple(bits[i]for i in inc)]%MOD
  total=(total+value)%MOD
 return total

def merge(left,right):
 idsA,tabA=left;idsB,tabB=right
 common=set(idsA)&set(idsB)
 output=tuple(sorted((set(idsA)|set(idsB))-common))
 posA={e:i for i,e in enumerate(idsA)};posB={e:i for i,e in enumerate(idsB)}
 table={}
 for a,va in tabA.items():
  for b,vb in tabB.items():
   if any(a[posA[e]]!=b[posB[e]]for e in common):continue
   key=tuple(a[posA[e]]if e in posA else b[posB[e]]for e in output)
   table[key]=(table.get(key,0)+va*vb)%MOD
 return output,table

def contract_plan(plan,factors):
 def block_table(block):
  if len(block)==1:return factors[block[0]]
  mid=len(block)//2
  return merge(block_table(block[:mid]),block_table(block[mid:]))
 tables=[block_table(b)for b in plan]
 answer=merge(merge(tables[0],tables[1]),tables[2])
 require(answer[0]==(),'closed contraction has no boundary')
 return answer[1].get((),0)

def main():
 rng=random.Random(20261026)
 fixtures=[('scalar',[],'unit'),('single_edge',[(0,1)],'point'),
 ('path',[(i,i+1)for i in range(9)],'equal'),
 ('cycle',[(i,i+1)for i in range(9)]+[(0,9)],'equal'),
 ('star',[(0,i)for i in range(1,10)],'point'),
 ('matching',[(2*i,2*i+1)for i in range(5)],'random'),
 ('triangles',[(0,1),(1,2),(0,2),(3,4),(4,5),(3,5)],'random'),
 ('twelve_edges',sorted(rng.sample(PAIRS,12)),'random')]
 outcomes=[]
 for i,(name,edges,kind) in enumerate(fixtures):
  active=sorted(edges);dims=[2 if e in active else 1 for e in PAIRS]
  selected,scores=select_plan(dims)
  factors=make_factors(active,kind,seed=500+i)
  reference=brute_force(active,factors)
  answers=[contract_plan(p,factors)for p in plans()]
  require(all(a==reference for a in answers),'regrouping mismatch: '+name)
  require(scores[selected]==min(scores),'selector did not minimize exact exponent')
  outcomes.append({'case':name,'active_edges':len(active),'assignments':2**len(active),
                   'selected_plan':selected,'reference_mod8':reference,
                   'all_twelve_plans_equal':True,'exact_selector_score':scores[selected]})
 zero=[1]*45;zero[0]=0
 require(select_plan(zero)==(None,None),'empty mode list must bypass selection')
 empty_literal_sum=sum(1 for _ in product(*(range(d) for d in zero)))
 require(empty_literal_sum==0,'literal empty allocation sum')
 outcomes.append({'case':'empty_mode_list','contribution':empty_literal_sum,'selected_plan':None})
 bad=[1]*45;bad[0]=-1
 try:select_plan(bad)
 except RuntimeError:rejected=True
 else:rejected=False
 require(rejected,'negative dimension not rejected')
 require(any(o.get('reference_mod8',0)!=0 for o in outcomes),'no nonzero fixture')
 return {'status':'PASS','modulus':8,'plans':12,'support_scale':SCALE,
         'fixture_count':len(outcomes),'plan_contractions_compared':len(fixtures)*12,
         'empty_allocation_contributes_zero':True,'negative_dimension_rejected':True,
         'scope':'dyadic finite mode lists, scalar arithmetic; not a SAT solver',
         'outcomes':outcomes}
if __name__=='__main__':
 result=main()
 Path(__file__).with_name('selector_checks.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))

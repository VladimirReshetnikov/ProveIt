#!/usr/bin/env python3
"""Exact finite localization of all role-activity coefficients in a cubic gap."""
from itertools import product,combinations,permutations
from collections import Counter
import json,time
from pathlib import Path

def alloc(t):
 return [(0,0)] if t==0 else ([(0,1),(1,0)] if t==1 else [(1,1)])

def check_graphs(ci,j,k,ext_types):
 # 1=tail,0=head. ci is total tail exponent at doubled core0.
 m=len(ext_types)
 C=[set(sum(([a,b] for a,b in alloc(ci)),[])),{j},{k}]
 E=[set(sum(([a,b] for a,b in alloc(t)),[])) if z==0 and m==3 else {t}
    for z,t in enumerate(ext_types)]
 edges=[]
 for c in range(3):
  for e in range(m):
   if 1 in C[c] and 0 in E[e]:edges.append((c,e,1))
   if 0 in C[c] and 1 in E[e]:edges.append((c,e,0))
 edgeid={e:b for b,e in enumerate(edges)}
 # Feasibility is a monotone Boolean expression: each mask is a matching witness.
 def witnesses(core, exts):
  if sum(x[1] for x in core)+sum(x[1] for x in exts)!=len(core):return []
  ws=[]
  for ee in permutations(exts):
   if all(cr!=er for (c,cr),(e,er) in zip(core,ee)):
    ws.append(sum(1<<edgeid[c,e,cr] for (c,cr),(e,er) in zip(core,ee)))
  return ws
 def term(core1,ext1,core2,ext2):
  return witnesses(core1,ext1),witnesses(core2,ext2)
 positive=[];negative=[]
 for a,b in alloc(ci):
  if m==4:
   ext=list(enumerate(ext_types))
   for ids in combinations(range(4),2):
    other=[x for x in range(4) if x not in ids]
    positive.append(term([(0,a),(1,j)],[ext[x] for x in ids],[(0,b),(2,k)],[ext[x] for x in other]))
   for x in range(4):
    negative.append(term([(0,a)],[ext[x]],[(0,b),(1,j),(2,k)],[ext[y] for y in range(4) if y!=x]))
  else:
   for x,y in alloc(ext_types[0]):
    for z in [1,2]:
     zz=3-z
     positive.append(term([(0,a),(1,j)],[(0,x),(z,ext_types[z])],[(0,b),(2,k)],[(0,y),(zz,ext_types[zz])]))
    negative.append(term([(0,a)],[(0,x)],[(0,b),(1,j),(2,k)],[(0,y),(1,ext_types[1]),(2,ext_types[2])]))
 hist=Counter()
 for graph in range(1<<len(edges)):
  def ok(ws):return any((graph&w)==w for w in ws)
  coef=sum(ok(a) and ok(b) for a,b in positive)-sum(ok(a) and ok(b) for a,b in negative)
  if coef<0:
   return {'negative':True,'core':[ci,j,k],'exterior_types':ext_types,'arcs':[e for bit,e in enumerate(edges) if graph>>bit&1],'coefficient':coef}
  hist[coef]+=1
 return {'negative':False,'core':[ci,j,k],'exterior_types':ext_types,'potential_arcs':len(edges),'graphs':1<<len(edges),'coefficient_histogram':dict(sorted(hist.items()))}

def main():
 start=time.monotonic();cases=[]
 for ci,j,k in product(range(3),range(2),range(2)):
  ext_tail=4-ci-j-k
  ext=[1]*ext_tail+[0]*(4-ext_tail)
  cases.append(check_graphs(ci,j,k,ext))
  if cases[-1]['negative']:break
  for ei,ej,ek in product(range(3),range(2),range(2)):
   if ci+j+k+ei+ej+ek!=4:continue
   cases.append(check_graphs(ci,j,k,[ei,ej,ek]))
   if cases[-1]['negative']:break
  if cases[-1]['negative']:break
 result={'status':'COUNTEREXAMPLE' if cases[-1]['negative'] else 'PASS','monomial_role_cases':len(cases),'graph_cases':sum(c.get('graphs',1) for c in cases),'elapsed_seconds':time.monotonic()-start,'cases':cases}
 Path(__file__).with_name('universal_boundary_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
 if result['status']!='PASS':print(cases[-1])
if __name__=='__main__':main()

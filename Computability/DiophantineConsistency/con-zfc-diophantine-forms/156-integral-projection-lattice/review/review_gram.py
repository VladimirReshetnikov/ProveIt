#!/usr/bin/env python3
"""Independent Gram audit using exact Schur pivots and exponent vectors.
No construction/search/Gram-checker module is imported.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
import json,math,hashlib,sys

def need(x,m):
 if not x:raise ValueError(m)
def parse(ts,n):
 p=defaultdict(int)
 for a,mon in ts:
  need(isinstance(a,int) and a!=0,'invalid coefficient')
  v=[0]*n
  for i in mon:
   need(type(i) is int and 0<=i<n,'invalid index');v[i]+=1
  p[tuple(v)]+=a
 return {v:a for v,a in p.items() if a}
def accum(out,a,b,w):
 for e,c in a.items():
  for f,d in b.items():out[tuple(x+y for x,y in zip(e,f))]+=w*c*d

def review(folder,source_projection=None):
 folder=Path(folder);source_bytes=(folder/'source_equation.json').read_bytes()
 if source_projection is not None:need(source_bytes==Path(source_projection).read_bytes(),'Gram source differs from independent projection artifact')
 s=json.loads(source_bytes);e=json.loads((folder/'equation.json').read_text());c=json.loads((folder/'GRAM_CERTIFICATE.json').read_text());p=json.loads((folder/'expanded_polynomial.json').read_text());m=json.loads((folder/'METRICS.json').read_text())
 digest=hashlib.sha256(source_bytes).hexdigest()
 need(e['source_sha256']==c['source_sha256']==digest,'source hash mismatch')
 need(e['domain']==s['domain']==p['domain']=='unrestricted integers','domain mismatch')
 need(e['variables']==s['variables']==p['variables'] and e['residuals']==s['residuals'],'retained source changed')
 need(e['definition']=='sum(r_i^2) + sum(sign*r_i*r_j for [i,j,sign] in gram_cross_terms)','ambiguous definition')
 n=len(e['residuals']);nv=len(e['variables']);edges=e['gram_cross_terms'];adj={i:set() for i in range(n)};signs={}
 for i,j,a in edges:
  need(0<=i<j<n and a in (-1,1) and (i,j) not in signs,'invalid or duplicate edge')
  signs[i,j]=a;adj[i].add(j);adj[j].add(i)
 seen=set();blocks=[]
 for i in range(n):
  if i in seen or not adj[i]:continue
  stack=[i];component=set()
  while stack:
   j=stack.pop()
   if j in component:continue
   component.add(j);stack.extend(adj[j]-component)
  seen.update(component);blocks.append(sorted(component))
 need([b['residual_indices'] for b in c['blocks']]==blocks,'certified blocks differ from graph components')
 need(c['isolated_count']==n-len(seen),'isolated count mismatch')
 proof=[]
 for indices,b in zip(blocks,c['blocks']):
  size=len(indices);H=[[2*int(i==j) if i==j else signs.get(tuple(sorted((i,j))),0) for j in indices] for i in indices]
  need(H==b['gram_matrix_H'],'matrix not equal to actual edge form')
  S=[[Fraction(a) for a in row] for row in H];pivots=[]
  for k in range(size):
   d=S[k][k];need(d>0,'nonpositive exact Schur pivot');pivots.append(d)
   for i in range(k+1,size):
    for j in range(k+1,size):S[i][j]-=S[i][k]*S[k][j]/d
  need(pivots==[Fraction(*a) for a in b['positive_diagonal_D']],'claimed diagonal disagrees with independent Schur elimination')
  determinant=math.prod(pivots);need(determinant==Fraction(*b['determinant']),'determinant mismatch')
  L=[[Fraction(*a) for a in row] for row in b['unit_lower_L']]
  need(len(L)==size and all(len(row)==size for row in L),'invalid lower matrix')
  for i in range(size):
   for j in range(size):
    need(i>j or L[i][j]==int(i==j),'not unit lower triangular')
    need(sum(L[i][k]*pivots[k]*L[j][k] for k in range(size))==H[i][j],'exact LDL identity false')
  proof.append({'indices':indices,'size':size,'positive_schur_pivots':[[a.numerator,a.denominator] for a in pivots],'determinant':[determinant.numerator,determinant.denominator]})
 parsed=[parse(row['terms'],nv) for row in e['residuals']]
 need(all(max(map(sum,r),default=0)<=2 for r in parsed),'residual not quadratic')
 q=defaultdict(int)
 for r in parsed:accum(q,r,r,1)
 source={v:a for v,a in q.items() if a}
 for i,j,a in edges:accum(q,parsed[i],parsed[j],a)
 q={v:a for v,a in q.items() if a}
 literal=parse(p['terms'],nv)
 need(len(p['terms'])==len(literal),'expansion not fully collected')
 need(q==literal,'coefficient-by-coefficient expansion mismatch')
 live={i for v in q for i,k in enumerate(v) if k}
 need(live==set(range(nv)),'dead variable')
 measured={'variable_count':nv,'used_variables':len(live),'residual_count':n,'degree':max(map(sum,q)),'monomial_count':len(q),'coefficient_height':max(map(abs,q.values())),'coefficient_l1':sum(map(abs,q.values())),'content':math.gcd(*q.values()),'cross_term_count':len(edges),'source_monomials':len(source),'source_height':max(map(abs,source.values())),'source_l1':sum(map(abs,source.values()))}
 need(measured==m,'metrics mismatch')
 need(measured['degree']==4,'not exact quartic')
 return {'ok':True,'source_sha256':digest,'metrics':measured,'blocks':proof,'isolated':n-len(seen),'proof':'Exact positive Schur pivots prove H positive definite. Q=r^T H r/2 vanishes iff all residuals vanish, over R and therefore over Z.'}
if __name__=='__main__':
 print(json.dumps(review(sys.argv[1],sys.argv[2] if len(sys.argv)>2 else None),indent=2))

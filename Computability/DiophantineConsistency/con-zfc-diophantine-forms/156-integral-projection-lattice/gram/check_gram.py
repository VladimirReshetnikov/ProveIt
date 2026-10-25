#!/usr/bin/env python3
"""Exact, standard-library-only verifier for residual Gram recombination.

This checker does not import the search or construction program. It verifies
polynomial equality, every entry of rational LDL certificates, positive
definiteness, source binding, domain/liveness, and the stated metrics.
The proof of the equivalence with the source zero set is in PROOF.md.
"""
import json,sys,pathlib,hashlib,math
from fractions import Fraction

def require(condition,message):
 if not condition:raise ValueError(message)
def fraction(q):
 require(isinstance(q,list) and len(q)==2 and q[1]>0,'invalid rational encoding')
 return Fraction(q[0],q[1])
def checked_positive_ldl(H,L,D):
 n=len(H);require(len(L)==n and len(D)==n,'matrix dimension mismatch')
 require(all(len(row)==n for row in H+L),'matrix row length mismatch')
 require(all(d>0 for d in D),'nonpositive LDL diagonal')
 for i in range(n):
  for j in range(n):
   require((i>j) or L[i][j]==int(i==j),'L is not unit lower triangular')
   require(H[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(n)),'LDL identity failed')

def verify(folder):
 p=pathlib.Path(folder);e=json.loads((p/'equation.json').read_text());source_bytes=(p/'source_equation.json').read_bytes();s=json.loads(source_bytes);cert=json.loads((p/'GRAM_CERTIFICATE.json').read_text());expanded=json.loads((p/'expanded_polynomial.json').read_text());claimed=json.loads((p/'METRICS.json').read_text())
 require(e['source_sha256']==cert['source_sha256']==hashlib.sha256(source_bytes).hexdigest(),'source hash mismatch')
 require(e['variables']==s['variables'] and e['residuals']==s['residuals'],'source residuals changed')
 require(e['domain']==expanded['domain']=='unrestricted integers','domain mismatch')
 require(expanded['variables']==e['variables'],'expanded variable list mismatch')
 rows=e['residuals'];n=len(rows);vcount=len(e['variables']);edges=e['gram_cross_terms'];seen=set();H=[[2*int(i==j) for j in range(n)] for i in range(n)]
 for i,j,sign in edges:
  require(0<=i<j<n and sign in(-1,1),'invalid cross term')
  require((i,j) not in seen,'duplicate cross term');seen.add((i,j));H[i][j]=H[j][i]=sign
 covered=set()
 for b in cert['blocks']:
  vs=b['residual_indices'];require(vs==sorted(set(vs)) and not(covered&set(vs)),'overlapping/unordered block');covered.update(vs)
  local=[[H[i][j] for j in vs] for i in vs];require(local==b['gram_matrix_H'],'block matrix mismatch')
  for i in vs:
   require(all(H[i][j]==0 for j in range(n) if j not in vs),'cross-block edge')
  L=[[fraction(q) for q in rr] for rr in b['unit_lower_L']];D=[fraction(q) for q in b['positive_diagonal_D']]
  checked_positive_ldl(local,L,D);require(math.prod(D)==fraction(b['determinant']),'determinant mismatch')
 require(cert['isolated_count']==n-len(covered),'isolated count mismatch')
 require(all(i in covered and j in covered for i,j,z in edges),'uncovered edge')
 poly={}
 def accumulate(left,right,weight):
  for c,m in left:
   require(isinstance(c,int) and c!=0 and all(isinstance(i,int) and 0<=i<vcount for i in m),'invalid sparse term')
   require(m==sorted(m),'unsorted source monomial')
   for d,q in right:
    key=tuple(sorted(m+q));poly[key]=poly.get(key,0)+weight*c*d
 for row in rows:accumulate(row['terms'],row['terms'],1)
 base={k:c for k,c in poly.items() if c};base_metrics=[len(base),max(map(abs,base.values())),sum(map(abs,base.values()))]
 for i,j,sign in edges:accumulate(rows[i]['terms'],rows[j]['terms'],sign)
 poly={k:c for k,c in poly.items() if c};expected=[[c,list(m)] for m,c in sorted(poly.items())]
 require(expected==expanded['terms'],'collected coefficient mismatch')
 require(max(map(len,poly))==4,'not exact quartic')
 used=set(i for m in poly for i in m);require(used==set(range(vcount)),'dead or invalid variable')
 metrics={'variable_count':vcount,'used_variables':len(used),'residual_count':n,'degree':max(map(len,poly)),'monomial_count':len(poly),'coefficient_height':max(map(abs,poly.values())),'coefficient_l1':sum(map(abs,poly.values())),'content':math.gcd(*poly.values()),'cross_term_count':len(edges),'source_monomials':base_metrics[0],'source_height':base_metrics[1],'source_l1':base_metrics[2]}
 require(metrics==claimed,'metrics mismatch')
 return metrics

def negative_controls():
 # A correct LDL identity with a zero diagonal pivot must be rejected.
 H=[[2,-1,-1],[-1,2,-1],[-1,-1,2]]
 L=[[Fraction(1),Fraction(0),Fraction(0)],[Fraction(-1,2),Fraction(1),Fraction(0)],[Fraction(-1,2),Fraction(-1),Fraction(1)]];D=[Fraction(2),Fraction(3,2),Fraction(0)]
 try:checked_positive_ldl(H,L,D)
 except ValueError:pass
 else:raise ValueError('singular Gram corruption was accepted')
 H=[[2,-1],[-1,2]];L=[[Fraction(1),Fraction(0)],[Fraction(-1,2),Fraction(1)]];D=[Fraction(2),Fraction(1)]
 try:checked_positive_ldl(H,L,D)
 except ValueError:pass
 else:raise ValueError('false LDL identity was accepted')

if __name__=='__main__':
 negative_controls();result={'status':'pass','negative_controls':2,'metrics':verify(sys.argv[1])};print(json.dumps(result,indent=2))

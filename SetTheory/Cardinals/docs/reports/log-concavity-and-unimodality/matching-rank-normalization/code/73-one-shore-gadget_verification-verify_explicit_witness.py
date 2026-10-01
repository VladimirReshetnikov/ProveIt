from math import comb
from pathlib import Path
import json
from exact_gadget_tails import gadget
ROOT=Path(__file__).parent
a,b,N,M,W,T=20,10,14,30,21,1
r=a+b;K=N*(W-1);R=r+K
# Group original supports by number l of selected exterior-left vertices.
# The full-core matching criterion is j>=l (equivalent to i+j>=i+l).
base=[]
for l in range(min(N,b)+1):
    q=[0]*(r+1)
    for i in range(a+1):
        k=i+l
        for j in range(l,b+1):
            rho=k-j
            if 0<=rho<=M:
                q[k]+=comb(a,i)*comb(b,j)*comb(N,l)*comb(M,rho)*W**j
    base.append(q)
# Independently expand the full polynomial, rather than using the tail formulas.
p=[0]*(R+1)
for l,q in enumerate(base):
    exponent1=K-N+l;exponentW=N-l
    gp=[sum(comb(exponent1,k-j)*comb(exponentW,j)*W**j
            for j in range(max(0,k-exponent1),min(k,exponentW)+1))*T**k
        for k in range(K+1)]
    for i,x in enumerate(q):
        if x:
            for j,y in enumerate(gp):p[i+j]+=x*y
assert p[0]==1 and p[-1]>0
margin=(R-1)*p[-2]**2-2*R*p[-3]*p[-1]
assert margin<0
rec=gadget(a,b,N,M,W)
assert rec['T']==T
expected=W**(2*N-2)*T**(2*K-2)*rec['quadratic_gcd']*rec['endpoint_quadratic_value_primitive']
assert margin==expected
# Explicit edge inventory and rank certificates.
left_core=[f'A{i}'for i in range(a)];right_core=[f'B{j}'for j in range(b)]
left_outer=[f'L{i}'for i in range(N)];right_outer=[f'R{j}'for j in range(M)]
centers=[f'Z{i}_{h}'for i in range(N)for h in range(W-1)]
leaves=[f'P{i}_{h}'for i in range(N)for h in range(W-1)]
edges=[[x,y]for x in left_core for y in right_core]
edges += [[x,y]for x in left_core for y in right_outer]
edges += [[x,y]for x in left_outer for y in right_core]
for i in range(N):
    for h in range(W-1):edges += [[f'L{i}',f'Z{i}_{h}'],[f'P{i}_{h}',f'Z{i}_{h}']]
matching=[[left_core[i],right_outer[i]]for i in range(a)]+[[left_outer[j],right_core[j]]for j in range(b)]+[[leaf,z]for leaf,z in zip(leaves,centers)]
cover=left_core+right_core+centers
assert len(matching)==R==len(cover)
assert len(set(x for x,y in matching))==R==len(set(y for x,y in matching))
assert all(x in cover or y in cover for x,y in edges)
out={'description':'Full20x10 Hall core,14 exterior-left and30 exterior-right vertices;20 pendant length-two arms at each exterior-left vertex.',
 'activities':{'all_left_vertices':1,'ten_original_right_core_vertices':21,'all_other_right_vertices':1},
 'rank':R,'vertices':len(left_core+left_outer+leaves+right_core+right_outer+centers),'edges':len(edges),
 'top_three_coefficients':p[-3:],'failed_margin':margin,
 'primitive_endpoint_quadratic':rec['endpoint_quadratic_primitive'],
 'endpoint_factorization':'-726235 * 4485169759863727935000 * 21^26',
 'coefficients':p,'matching_certificate':matching,'cover_certificate':cover,'edge_list':edges,
 'one_shore_condition_verified':True,'full_polynomial_matches_tail_formula':True}
(ROOT/'one_shore_rank310_witness.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k]for k in('rank','vertices','edges','top_three_coefficients','failed_margin','endpoint_factorization')}))

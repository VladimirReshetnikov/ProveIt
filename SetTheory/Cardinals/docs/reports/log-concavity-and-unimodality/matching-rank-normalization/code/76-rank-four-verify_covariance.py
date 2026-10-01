"""Exact independent-column squared-minor certificates for core masks6 and7.
All entries lie in Q(2**(1/4)); SymPy performs exact algebra.
"""
import itertools, json, sympy as s
from pathlib import Path
q=s.sqrt(2)/2
r=s.sqrt(q)

def sign(p):return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))

def covariance(core, n):
 out=[]
 for j in range(2):
  C=s.zeros(n+2)
  for u in range(n+2):
   if u>=2 or core>>(2*u+j)&1:C[u,u]=1
  for u in range(2,n+2):
   for v in range(2,u):C[u,v]=C[v,u]=q
  if core==6:
   i=1-j
   for u in range(2,n+2):C[i,u]=C[u,i]=(-1 if j else 1)*r
  elif core==7:
   if j==0:
    C[0,1]=C[1,0]=q
    for u in range(2,n+2):C[0,u]=C[u,0]=r/s.sqrt(2)
   else:
    for u in range(2,n+2):C[0,u]=C[u,0]=r
  out.append(C)
 R=s.zeros(n+2);R[0,0]=R[1,1]=1;R[0,1]=R[1,0]=q
 return out+[R,R]

def expected_minor(Cs, rows,cols):
 perms=list(itertools.permutations(rows))
 return s.simplify(s.expand(sum(sign(pi)*sign(tau)*s.prod(Cs[j][pi[k],tau[k]] for k,j in enumerate(cols)) for pi in perms for tau in perms)))

def matchable(adj,rows,cols):
 return any(all(adj[i,j] for i,j in zip(rows,p)) for p in itertools.permutations(cols))

if __name__=='__main__':
 report=[]
 for core in (6,7):
  Cs=covariance(core,2)
  adj=s.zeros(4)
  for i in range(4):
   for j in range(4):
    adj[i,j]=int((i<2 and j<2 and core>>(2*i+j)&1) or (i<2 and j>=2) or (i>=2 and j<2))
  checked=0;match=0
  for k in range(5):
   for rows in itertools.combinations(range(4),k):
    for cols in itertools.combinations(range(4),k):
     want=int(matchable(adj,rows,cols));got=expected_minor(Cs,rows,cols)
     assert got==want,(core,rows,cols,got,want)
     checked+=1;match+=want
  # finite-dimensional PSD corroboration, symbolic proof given in note
  for C in Cs:
   for k in range(1,5):
    for ix in itertools.combinations(range(4),k):
     val=s.simplify(C.extract(ix,ix).det())
     assert val.is_nonnegative,(core,ix,val)
  report.append(dict(core=core,square_minors=checked,feasible_minors=match,all_equal=True))
 print(json.dumps(report,indent=2))
 Path(__file__).with_name('covariance_verification.json').write_text(json.dumps(report,indent=2)+'\n')

"""Finite diagnostics for legal log-accelerated staircase subclasses.

This checks all integer boundary/length/binomial conditions; it is not used to
infer the asymptotic theorem. Floating logarithms only choose sample heights.
"""
from mpmath import mp
mp.dps=70
alpha=mp.findroot(lambda a:7*a**3+14*a**2-7*a-1,mp.mpf('.51'))
kappa=(-21*alpha**2+17*alpha+5)/29
mu=(1+alpha)/(1-alpha-kappa)
z=kappa*(1-alpha-kappa)/((alpha-kappa)*(2*alpha+kappa))
J=20

def h(j):return int(mp.floor(j*j*mp.log(j)))
def pars(j):
 q=h(j)//2;ell=int(mp.floor(q/alpha));k=int(mp.nint(kappa*ell))
 return ell,q,k

def check_block(height,ell,q,r,k):
 assert 1<=q<=height
 assert height+1-q+r>=1
 assert 0<=k<=r
 assert 0<=r-k<=q
 assert ell>=r+k+1
 assert abs(q-alpha*ell)<=2
 assert abs(k-kappa*ell)<=1
 return height+1-q+r

def base_length(K):
 return 2*h(J)+1+sum(pars(j)[0]+1 for j in range(J,K))+sum(pars(j)[0]+1 for j in range(J+1,K+1))

def construct(n):
 K=J
 while base_length(K+1)<=n:K+=1
 height=h(J);length=2*h(J)+1;blocks=[]
 for j in range(J,K):
  ell,q,k=pars(j);r=q-1+h(j+1)-h(j)
  height=check_block(height,ell,q,r,k);assert height==h(j+1)
  blocks.append((ell,q,r,k));length+=ell+1
 R=n-base_length(K)
 # For tiny residuals, the terminating 1/(1-x) supplies the remainder.
 tail=R
 if R>=2000:
  tail=0
  for m in (R//2,R-R//2):
   ell=m-1;q=int(mp.nint(alpha*ell));r=q-1;k=int(mp.nint(kappa*ell))
   assert check_block(height,ell,q,r,k)==height
   blocks.append((ell,q,r,k));length+=m
 for j in range(K,J,-1):
  ell,q,k=pars(j);r=q-1+h(j-1)-h(j)
  height=check_block(height,ell,q,r,k);assert height==h(j-1)
  blocks.append((ell,q,r,k));length+=ell+1
 assert height==h(J)
 assert length+tail==n
 assert sum(r-q for ell,q,r,k in blocks)==-len(blocks)
 return K,blocks,tail

for K in [20,21,30,50,100,200]:
 L=base_length(K);gap=base_length(K+1)-L
 for R in sorted(set([0,1,999,1000,1999,2000,gap//2,gap-1])):
  if R>=gap:continue
  kk,blocks,tail=construct(L+R)
  assert kk==K
  print('K',K,'n',L+R,'blocks',len(blocks),'terminal padding',tail,'PASS')
print('PASS all sample exact length, boundary, binomial-interior, and tilt-telescope checks')

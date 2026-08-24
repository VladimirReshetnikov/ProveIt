import random
from fractions import Fraction
# exhaustive small search for a violation of Phi+ <= 2P+2N  (Step 4)
from itertools import product
def masses(M,A,cells):
    P=0;Nn=0;Phi=0;bal=0
    js=sorted(set(j for (i,j) in cells))
    for j in js:
        sl=sorted([i for (i,jj) in cells if jj==j])
        prev=0
        for k,i in enumerate(sl):
            T=sum(cells[(ii,j)] for ii in sl[k:])
            D=M**i-prev; prev=M**i
            if T>0: P+=T*D*A**j
            else: Nn+=(-T)*D*A**j
        for i in sl:
            c=cells[(i,j)]; bal+=c*M**i*A**j
            if c>0: Phi+=c*M**i*A**j
    return P,Nn,Phi,bal

worst=Fraction(0); wex=None
for M in (2,3,5):
  for idx in [(0,1),(0,1,2),(0,2),(1,3),(0,1,3)]:
    for vals in product(range(-4,5), repeat=len(idx)):
      if all(v==0 for v in vals): continue
      cells={(i,0):v for i,v in zip(idx,vals)}
      P,Nn,Phi,bal=masses(M,3,cells)
      if 2*P+2*Nn>0:
        r=Fraction(Phi,2*P+2*Nn)
        if r>worst: worst=r; wex=(M,dict(cells),P,Nn,Phi)
print("max Phi+/(2P+2N) over single-slice exhaustive =",float(worst), worst)
print("extremal:",wex)

# now with the balance imposed (P=N): max Phi+/(4P)
worst2=Fraction(0); w2=None
for M in (2,3,5,16390):
  for idx in [(0,1),(0,1,2),(0,2),(0,1,3)]:
    for vals in product(range(-6,7), repeat=len(idx)):
      if all(v==0 for v in vals): continue
      cells={(i,0):v for i,v in zip(idx,vals)}
      P,Nn,Phi,bal=masses(M,3,cells)
      if bal!=0: continue
      if P>0:
        r=Fraction(Phi,4*P)
        if r>worst2: worst2=r; w2=(M,dict(cells),P,Nn,Phi)
print("max Phi+/(4P) over BALANCED single-slice =",float(worst2), worst2)
print("extremal:",w2)

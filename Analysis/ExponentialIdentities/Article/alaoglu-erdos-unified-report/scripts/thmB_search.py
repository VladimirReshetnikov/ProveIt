"""Exhaustive/randomized hunt for a counterexample to:

  THEOREM B.  If c : S -> Z (S finite subset of Z_{>=0}^2) satisfies
      (B0)  sum_{ij} c_ij M^i A^j = 0                (M>1, A>0)
      (TH)  for every j and every k, the slice tail T^{(j)}_k = sum_{l>=k} c_{i_l, j} >= 0
  then c = 0.

We brute force over small grids and coefficient boxes with exact integer arithmetic.
"""
from itertools import product

def tails_ok(c, cells):
    js = sorted({j for (i,j) in cells})
    for j in js:
        row = sorted([i for (i,jj) in cells if jj == j])
        vals = [c[(i,j)] for i in row]
        s = 0
        for l in range(len(vals)-1, -1, -1):
            s += vals[l]
            if s < 0:
                return False
    return True

def search(M, A, I, J, B):
    cells = [(i,j) for i in range(I) for j in range(J)]
    w = [M**i * A**j for (i,j) in cells]
    found = []
    cnt = 0
    for vec in product(range(-B, B+1), repeat=len(cells)):
        if sum(a*b for a,b in zip(vec,w)) != 0: continue
        if all(a == 0 for a in vec): continue
        cnt += 1
        c = dict(zip(cells, vec))
        if tails_ok(c, cells):
            found.append(c)
    return cnt, found

for (M,A,I,J,B) in [(2,3,3,3,3), (3,2,3,3,3), (2,5,3,2,4), (5,11,3,2,4),
                    (2,3,2,4,4), (7,3,4,2,3)]:
    cnt, found = search(M,A,I,J,B)
    print(f"M={M} A={A} grid {I}x{J} box |c|<={B}: nonzero balanced vectors = {cnt};"
          f"  with all slice tails >=0 : {len(found)}")
    for f in found[:3]: print("   COUNTEREXAMPLE", f)

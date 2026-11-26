"""Certify the canonical-line property of E_{m,n} for a whole half-line n>=m.

Only Python's standard library is required. The proof is given in the report.
Run without -O, since the certificate uses assertions.
"""
from math import comb, prod
from argparse import ArgumentParser
from time import monotonic


def core_coeffs(r, n):
    """Return A,B in the cross-polynomial basis A Q_n - B Q_{n-1}.
    A common positive multiplier clears all denominators."""
    scale = prod((n-j)**2 for j in range(1, r))
    d = n+r
    weights = [4**(r-j)*comb(2*j,j)*comb(r,j)*comb(n-1,j) for j in range(r+1)]
    mixture = [sum(weights[j]*comb(j,i) for j in range(i,r+1))
               * prod(d-k for k in range(2*i)) for i in range(r+1)]
    def coord(core, previous):
        polys = {0:[core*scale], -1:[previous*scale]}
        for k in range(1,r+1):
            shifted = [0]+polys[k-1]
            for j, value in enumerate(polys[k-2]):
                shifted[j] -= (n+k-1)**2 * value
            polys[k] = shifted
        for k in range(-2,-r-1,-1):
            shifted = [0]+polys[k+1]
            for j,value in enumerate(polys[k+2]):
                shifted[j] -= value
            divisor = (n+k+1)**2
            assert all(c % divisor == 0 for c in shifted)
            polys[k] = [c//divisor for c in shifted]
        result = [0]*(r+1)
        for i,weight in enumerate(mixture):
            for j,value in enumerate(polys[r-2*i]):
                result[j] += weight * value
        return result
    return coord(1,0), coord(0,-1)


def bezout(a,b):
    r=len(a)-1
    mat=[[0]*r for _ in range(r)]
    for i in range(1,r+1):
        for j in range(i):
            v=a[i]*b[j]-a[j]*b[i]
            for k in range(i-j):
                mat[i-1-k][j+k] += v
    return mat


def minors(matrix):
    """Fraction-free symmetric Bareiss elimination gives all leading minors."""
    size=len(matrix)
    previous=1
    result=[]
    for k in range(size):
        pivot=matrix[k][k]
        assert pivot > 0
        result.append(pivot)
        for i in range(k+1,size):
            for j in range(i,size):
                v=matrix[i][j]*pivot-matrix[k][i]*matrix[k][j]
                assert v % previous == 0
                matrix[i][j] = v//previous
        previous=pivot
    return result


def normalized_coords(r,n):
    scale = prod((n-j)**2 for j in range(1,r))
    a,b=core_coeffs(r,n)
    assert all(v % scale == 0 for v in a+b)
    return [v//scale for v in a], [v//scale for v in b]


def differences(sequence):
    return [y-x for x,y in zip(sequence,sequence[1:])]


def certify(m):
    r=m-1
    minors(bezout(*normalized_coords(r,m-1)))  # the diagonal boundary
    # Certify degree <=r for A and <=r+1 for B *after dividing by scale*.
    # Each cleared coordinate has degree <=7r. Multiplication by scale
    # restores the original coordinate, checked at 7r+1 distinct integers.
    samples=[normalized_coords(r,m+t) for t in range(7*r+1)]
    for index,bound in enumerate((r,r+1)):
        for seq in zip(*(pair[index] for pair in samples)):
            for _ in range(bound+1):
                seq=differences(seq)
            assert all(v==0 for v in seq)
    # The normalized Bezout entries now have degree <=2r+1.
    sizes=((r+1)//2,r//2)
    bounds=[(2*r+1)*j for size in sizes for j in range(1,size+1)]
    values=[[] for _ in bounds]
    for t in range(1+max(bounds)):
        a,b=samples[t] if t<len(samples) else normalized_coords(r,m+t)
        matrix=bezout(a,b)
        assert all(matrix[i][j]==0 for i in range(r) for j in range((i+1)%2,r,2))
        h=[]
        for parity in (0,1):
            indices=range(parity,r,2)
            block=[[matrix[i][j] for j in indices] for i in indices]
            h.extend(minors(block))
        for j,bound in enumerate(bounds):
            if t<=bound:
                values[j].append(h[j])
    exact_degrees=[]
    for j,seq in enumerate(values):
        k=0
        while seq and seq[0]>0:
            seq=differences(seq)
            k+=1
        assert all(v==0 for v in seq), (m,j+1,k)
        exact_degrees.append(k-1)
    return exact_degrees
if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run without -O to enable certificate assertions')
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('first',type=int,nargs='?',default=6)
    parser.add_argument('last',type=int,nargs='?',default=None)
    args=parser.parse_args()
    for m in range(args.first,(args.last or args.first)+1):
        start=monotonic()
        print(f'm={m}  degrees={certify(m)}  seconds={monotonic()-start:.2f}',flush=True)

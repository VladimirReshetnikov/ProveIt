from fractions import Fraction as F
import json

def mul(A,B):
    return [[sum((a*b for a,b in zip(row,col)), F(0)) for col in zip(*B)] for row in A]

def block(n):
    # E0: residue 0 at time 3n-3, with one artificial top coordinate,
    # to residue 1 at time 3n-2. The artificial up edge has weight zero.
    E0=[[F(0) for j in range(n+1)] for i in range(n)]
    E1=[[F(0) for j in range(n)] for i in range(n)]
    E2=[[F(0) for j in range(n)] for i in range(n+1)]
    for r in range(n):
        E0[r][r]=F(4*((3*n-2)-(3*r+1)+3),2*(3*n-2)+(3*r+1))
        E0[r][r+1]=F(1)
        E1[r][r]=F(4*((3*n-1)-(3*r+2)+3),2*(3*n-1)+(3*r+2))
        if r+1<n:E1[r][r+1]=F(1)
        E2[r][r]=F(1)
        E2[r+1][r]=F(4*((3*n)-(3*r+3)+3),2*(3*n)+(3*r+3))
    return mul(E2,mul(E1,E0))

def direct(max_i):
    d={0:F(1)}
    out={0:d}
    for i in range(1,max_i+1):
        e={}
        for j in range(i%3,i+1,3):
            e[j]=F(4*(i-j+3),2*i+j)*d.get(j-1,0)+d.get(j+2,0)
        d=e
        out[i]=d
    return out

def checks():
    ds=direct(36)
    checks=[]
    for n in range(1,13):
        A=block(n)
        prev=[ds[3*n-3].get(3*j,F(0)) for j in range(n+1)]
        got=[sum((a*b for a,b in zip(row,prev)),F(0)) for row in A]
        expected=[ds[3*n][3*j] for j in range(n+1)]
        assert got==expected
        # Immediate positivity on both adjacent diagonals, including new top.
        assert all(A[j][j]>0 for j in range(n+1))
        assert all(A[j][j+1]>0 and A[j+1][j]>0 for j in range(n))
        checks.append({'n':n,'endpoint':str(got[0]),'block_matches':True,'primitive_support':True})
    result={'checks':checks,'A1':[[str(x) for x in row] for row in block(1)],'A2':[[str(x) for x in row] for row in block(2)]}
    print(json.dumps(result,indent=2))
if __name__=='__main__':checks()

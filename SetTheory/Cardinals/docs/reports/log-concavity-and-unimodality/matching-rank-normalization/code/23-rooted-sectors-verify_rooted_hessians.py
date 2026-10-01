"""Exact cubic Hessian checks for a rooted version of the connected example."""
from itertools import combinations
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import json

core=[2,1,0];left=[7]*8;right=[1,2]+[3]*7+[4,5]
activities=[Q(15),Q(15)]+[Q(1)]*7+[Q(15),Q(1,10)]
columns=[sum(1<<i for i,r in enumerate(core+left) if r>>b&1) for b in range(3)]+right
def supports(J):
    states={0}
    for j in [0,1,2]+[3+i for i in J]:
        nxt=set()
        for m in states:
            available=columns[j]&~m
            while available:
                bit=available&-available;available-=bit;nxt.add(m|bit)
        states=nxt
    return sum(bool(m&8) for m in states)  # First exterior-left vertex is forced.

def psd(matrix):
    A=[[Q(x) for x in row] for row in matrix]
    while A:
        if any(A[i][i]<0 for i in range(len(A))):return False
        pivot=next((i for i in range(len(A)) if A[i][i]>0),None)
        if pivot is None:return not any(x for row in A for x in row)
        ids=[i for i in range(len(A)) if i!=pivot];p=A[pivot][pivot]
        A=[[A[i][j]-A[i][pivot]*A[pivot][j]/p for j in ids] for i in ids]
    return True

def one_positive(H):
    p=H[0][0]
    if p<=0:raise RuntimeError('positive Hessian pivot')
    return psd([[H[i][0]*H[j][0]-p*H[i][j] for j in range(1,len(H))] for i in range(1,len(H))])

m=len(right);counts={I:supports(I) for k in range(4) for I in combinations(range(m),k)}
c0=counts[()];H=[[Q(0)]*(m+1) for _ in range(m+1)];H[0][0]=6*c0
for i in range(m):H[0][i+1]=H[i+1][0]=2*counts[(i,)]
for i,j in combinations(range(m),2):H[i+1][j+1]=H[j+1][i+1]=counts[(i,j)]
if not one_positive(H):raise RuntimeError('homogenizing derivative Hessian')
checks=1
for fixed in range(m):
    ids=[i for i in range(m) if i!=fixed];H=[[Q(0)]*(len(ids)+1) for _ in range(len(ids)+1)];H[0][0]=2*counts[(fixed,)]
    for i,a in enumerate(ids):H[0][i+1]=H[i+1][0]=counts[tuple(sorted((fixed,a)))]
    for i,j in combinations(range(len(ids)),2):H[i+1][j+1]=H[j+1][i+1]=counts[tuple(sorted((fixed,ids[i],ids[j])))]
    if not one_positive(H):raise RuntimeError(('right derivative Hessian',fixed))
    checks+=1
c=[sum(counts[I]*prod(activities[i] for i in I) for I in combinations(range(m),k)) for k in range(4)]
gaps=[c[1]**2-3*c[0]*c[2],c[2]**2-3*c[1]*c[3]]
if min(gaps)<=0:raise RuntimeError('rooted scalar ULC3')
out={'forced_left_vertex':'first common exterior-left vertex','all_B_forced':True,'exact_Hessian_checks':checks,'all_have_at_most_one_positive_eigenvalue':True,'rooted_cubic':[str(x) for x in c],'ulc3_gaps':[str(x) for x in gaps],'all_passed':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

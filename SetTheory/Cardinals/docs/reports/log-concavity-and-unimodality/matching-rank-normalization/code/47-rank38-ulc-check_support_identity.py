"""Small exact graph regressions, supplementary to the unbounded certificate."""
from itertools import combinations
from math import comb
from independent_replay import support_table, choose


def matching_exists(left,right,a,b):
    reachable={0}
    for x in left:
        nxt=set()
        for mask in reachable:
            for pos,y in enumerate(right):
                if not mask>>pos&1 and (x<a or y<b):
                    nxt.add(mask|(1<<pos))
        reachable=nxt
    return (1<<len(right))-1 in reachable


def brute(a,b,n,m):
    out=[]
    for k in range(min(a+n,b+m)+1):
        row=[0]*(b+1)
        for left in combinations(range(a+n),k):
            for right in combinations(range(b+m),k):
                if matching_exists(left,right,a,b):
                    row[sum(y<b for y in right)]+=1
        out.append(row)
    return out


def run():
    cases=[(1,1,0,0),(1,2,3,2),(2,1,2,3),(2,2,0,4),
           (3,3,1,5),(3,3,3,3),(3,4,4,3),(4,3,3,4)]
    for a,b,n,m in cases:
        actual=brute(a,b,n,m)
        for k,row in enumerate(actual):
            expected=[choose(b,j)*choose(m,k-j)*sum(
                choose(a,k-j+x)*choose(n,j-x) for x in range(j+1)
            ) if k-j>=0 else 0 for j in range(b+1)]
            if row!=expected: raise RuntimeError((a,b,n,m,k,row,expected))
        # Recheck the exterior-addition recurrence over its complete table.
        get=support_table(a,b)
        for q in range(a+1):
            for j in range(b+1):
                for i,val in enumerate(get(q+j,j)):
                    direct=sum(choose(a,q+x)*choose(b+i,j-x)
                               for x in range(j+1))
                    if val!=direct: raise RuntimeError('support recurrence mismatch')
    print(f'{len(cases)} exact graph-support enumerations and all support recurrence entries passed')

if __name__=='__main__': run()

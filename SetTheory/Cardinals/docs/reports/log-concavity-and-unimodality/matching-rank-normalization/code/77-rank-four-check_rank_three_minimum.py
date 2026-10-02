"""Independent exact audit using Hall-theorem closed forms, not bijection tables."""
from itertools import combinations
from math import comb
import json

def choose(n,k):
    return comb(n,k) if n>=k else 0

def coeff(n):
    N=sum(n)
    a=sum(mask.bit_count()*n[mask-1] for mask in range(1,8))
    b=0
    for i,j in combinations((1,2,4),2):
        eligible=sum(n[m-1] for m in range(1,8) if m&(i|j))
        onlyi=sum(n[m-1] for m in range(1,8) if m&i and not m&j)
        onlyj=sum(n[m-1] for m in range(1,8) if m&j and not m&i)
        b+=choose(eligible,2)-choose(onlyi,2)-choose(onlyj,2)
    # Inclusion-exclusion for union of three nonempty masks equal to 111.
    c=choose(N,3)
    for i in (1,2,4):
        c-=choose(sum(n[m-1] for m in range(1,8) if not m&i),3)
        c+=choose(n[i-1],3)
        # Remaining Hall obstructions: two copies of one singleton mask.
        c-=choose(n[i-1],2)*(n[(7^i)-1]+n[6])
    return [1,a,b,c]

def vectors(N):
    for bars in combinations(range(N+6),6):
        p=(-1,)+bars+(N+6,)
        yield tuple(p[i+1]-p[i]-1 for i in range(7))

def discriminant(a,b,c):
    return a*a*b*b-4*b*b*b-4*a*a*a*c-27*c*c+18*a*b*c

result={'status':'PASS','method':'Hall-theorem closed forms with stars-and-bars enumeration','by_total':[],'negative':[]}
for N in range(13):
    count=rank3=negative=0
    for n in vectors(N):
        count+=1
        p=coeff(n)
        if not p[3]: continue
        rank3+=1
        D=discriminant(*p[1:])
        if D<0:
            negative+=1
            result['negative'].append({'n':n,'coefficients':p,'discriminant':D})
    assert count==comb(N+6,6)
    result['by_total'].append({'N':N,'all_vectors':count,'rank3_vectors':rank3,'negative':negative})
result['rank3_vectors_checked']=sum(x['rank3_vectors'] for x in result['by_total'])
assert result['rank3_vectors_checked']==48987
assert sum(row['rank3_vectors'] for row in result['by_total'] if row['N']<=11)==30699
assert result['by_total'][12]['rank3_vectors']==18288
assert result['negative']==[{'n':(0,0,4,0,4,4,0),'coefficients':[1,24,162,208],'discriminant':-2592}]
print(json.dumps(result,indent=2))

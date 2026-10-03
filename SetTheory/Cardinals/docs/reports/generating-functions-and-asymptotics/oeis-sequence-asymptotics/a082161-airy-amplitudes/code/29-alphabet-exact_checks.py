from itertools import product
from fractions import Fraction
import json, math
from pathlib import Path
OUT=Path(__file__).parent

def recurrence(k,N):
    X=(k-1)*N
    r,b={},{}
    for x in range(X+1):r[x,0]=b[x,0]=1
    b[-1,0]=1
    for m in range(1,N+1):
      for x in range((k-1)*m,X+1):
        r[x,m]=r.get((x,m-1),0)+(m+1)*r.get((x-1,m),0)
        b[x,m]=2*b.get((x,m-1),0)+(m+1)*b.get((x-1,m),0)-m*b.get((x-k,m-1),0)
    return r,b

def renewal(k,N):
    X=(k-1)*N
    a={(x,1):1 for x in range(k-1,X+1)}
    A=dict(a)
    for m in range(1,N):
      for x in range((k-1)*(m+1),X+1):
        a[x,m+1]=sum((m+1)**l*a[x-l,m] for l in range(x-(k-1)*m+1))
        A[x,m+1]=sum((2*(m+1)**l-((m+1)**(l-k+1) if l>=k else 0))*A[x-l,m] for l in range(x-(k-1)*m+1))
    return a,A

def brute(k,n):
    # Enumerate all postorder-labeled acyclic accessible rooted ordered DAGs.
    # Labels are enforced by an independent DFS, so no division by automorphisms.
    R=B=0
    pools=[list(product(range(i),repeat=k)) for i in range(1,n+1)]
    for rows in product(*pools):
      transitions=[(0,)*k]+list(rows)
      seen={0}; order=[0]
      def dfs(i):
        if i in seen:return
        seen.add(i)
        for j in transitions[i]:dfs(j)
        order.append(i)
      dfs(n)
      if order!=list(range(n+1)):continue
      R+=1
      for rest in product((0,1),repeat=n-1):
        colors=(0,1)+rest
        signatures={(colors[i],transitions[i]) for i in range(n+1)}
        if len(signatures)==n+1:B+=1
    return R,B

result={'array_checks':[],'brute_checks':[]}
for k in range(2,9):
    N=30
    r,b=recurrence(k,N);a,A=renewal(k,N)
    P=Fraction(1)
    for m in range(1,N+1):
      if m>=2:P*=1-Fraction(1,2*m**(k-1))
      for x in range((k-1)*m,(k-1)*N+1):
        assert 2**(m-1)*P*a[x,m]<=A[x,m]<=2**(m-1)*a[x,m]
        assert r[x,m]==sum((m+1)**l*a[x-l,m] for l in range(x-(k-1)*m+1))
        assert b[x,m]==sum((m+1)**l*A[x-l,m] for l in range(x-(k-1)*m+1))
    result['array_checks'].append({'k':k,'N':N,'verified':'all supported array entries and both bounds','B_first':[b[(k-1)*n,n] for n in range(1,7)],'R_first':[r[(k-1)*n,n] for n in range(1,7)],'ratio_n30':float(Fraction(b[(k-1)*N,N],2**(N-1)*r[(k-1)*N,N]))})
for k,N in [(2,5),(3,4),(4,3),(5,3)]:
    r,b=recurrence(k,N)
    for n in range(1,N+1):
      R,B=brute(k,n)
      assert R==r[(k-1)*n,n] and B==b[(k-1)*n,n]
      result['brute_checks'].append({'k':k,'n':n,'R':R,'B':B})
result['uniform_product']=2*math.sqrt(2)/math.pi*math.sin(math.pi/math.sqrt(2))
(OUT/'exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

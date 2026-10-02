from functools import lru_cache
from itertools import combinations
@lru_cache(None)
def f(n,a,l,S):
 if n==0:return 1
 ans=0
 for i in range(a+2):
  p=max((v for v in S if v<i),default=0)
  ans+=f(n-1,a+(i>l)-p,i-p,tuple(sorted(set(v-p for v in S if v>=p)|{i-p})))
 return ans
if __name__=='__main__':
 print('A202061:', [1]+[f(n-1,0,0,(0,)) for n in range(1,17)])

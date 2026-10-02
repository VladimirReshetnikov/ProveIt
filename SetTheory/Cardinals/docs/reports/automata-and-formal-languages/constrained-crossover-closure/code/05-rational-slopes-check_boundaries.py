from itertools import product
import json

def image(A,S):
 return sum(1<<j for j in range(len(A)) if any(S>>i&1 and A[i]>>j&1 for i in range(len(A))))
def orbit(start,f):
 xs=[];seen={};x=start
 while x not in seen:
  seen[x]=len(xs);xs.append(x);x=f(x)
 return xs,seen[x],len(xs)-seen[x]
def check(name,A,B,I,F,w):
 n=len(w);s=len(A);E=tuple(a|b for a,b in zip(A,B));ET=tuple(sum(1<<i for i in range(s) if E[i]>>j&1) for j in range(s))
 powers,mt,mp=orbit(tuple(1<<i for i in range(s)),lambda M:tuple(image(E,row) for row in M))
 layers,t,p=orbit((I,F),lambda pr:(image(E,pr[0]),image(ET,pr[1])))
 assert p==1 and layers[t]==((1<<s)-1,(1<<s)-1)
 assert any(A[i]>>i&1 and B[i]>>i&1 for i in range(s))
 seeds=[]
 for v in product(range(2),repeat=n):
  S=I
  for a in v:S=image((A,B)[a],S)
  if S&F:seeds.append(''.join(map(str,v)))
 assert all(any(v[i]==w[i] for v in seeds) for i in range(n))
 dp=[0]+[999]*n
 for j in range(1,n+1):
  dp[j]=1+min(dp[i] for i in range(j) if any(v[i:j]==w[i:j] for v in seeds))
 assert dp[n]==n
 return dict(name=name,zero=list(A),one=list(B),initial=I,final=F,matrix_transient=mt,matrix_period=mp,pair_transient=t,pair_period=p,word=w,rank=dp[n],seeds=seeds,finite_rank_upper_bound=2*t+1)
results=[check('Pair threshold one, exact rank three',(5,3,7),(0,1,4),3,1,'111'),check('Matrix threshold two, rank at least four',(2,3,1),(0,2,4),4,5,'0101')]
assert results[0]['pair_transient']==1 and results[0]['rank']==3
assert results[1]['matrix_transient']==2 and results[1]['rank']==4
print(json.dumps(results,indent=2))

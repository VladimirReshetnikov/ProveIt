import math,itertools,functools,collections,sys,json
from fractions import Fraction as F
from scipy.optimize import linprog
from scipy.sparse import csc_matrix,diags
import numpy as np
from sympy import Matrix
@functools.lru_cache(None)
def parts(n,m=None):
    if m is None or m>n:m=n
    if n==0:return ((),)
    return tuple((k,)+p for k in range(m,0,-1) for p in parts(n-k,k))
def z(p):return math.prod(k**v*math.factorial(v) for k,v in collections.Counter(p).items())
def mul(a,b):
    r=collections.defaultdict(F)
    for p,x in a.items():
        for q,y in b.items():r[tuple(sorted(p+q,reverse=True))]+=x*y
    return {p:x for p,x in r.items() if x}
def cycle(p):
    n=len(p);seen=set();l=[]
    for i in range(n):
        if i in seen:continue
        k=0
        while i not in seen:seen.add(i);k+=1;i=p[i]
        l.append(k)
    return tuple(sorted(l,reverse=True))
@functools.lru_cache(None)
def ram(d,k):
    s=0
    for e in range(1,d+1):
        if d%e==0 and k%e==0:
            q=d//e;mu=1;f=2
            while f*f<=q:
                if q%f==0:
                    q//=f;mu=-mu
                    if q%f==0:mu=0;break
                f+=1
            if q>1:mu=-mu
            s+=e*mu
    return F(s,sum(math.gcd(i,d)==1 for i in range(1,d+1)))
@functools.lru_cache(None)
def block(k):
    rows={}
    def add(desc,row):
        row={p:x for p,x in row.items() if x};key=tuple(sorted(row.items()));rows.setdefault(key,(desc,row))
    for d in range(1,k+1):
        if k%d:continue
        r=collections.defaultdict(F)
        for j in range(k):
            g=math.gcd(k,j);r[(k//g,)*g]+=ram(d,j)
        add(('C',k,d),r)
    if k>=3:
        for a in [0,1]:
            if a and k%2:continue
            for b in [0,1]:
                r=collections.defaultdict(F)
                for j in range(k):
                    g=math.gcd(k,j);r[(k//g,)*g]+=(-1)**(a*j)
                    r[cycle(tuple((j-i)%k for i in range(k)))]+=(-1)**(a*j+b)
                add(('D',k,a,b),r)
    for a in [0,1]:add(('S',k,a),{p:F(math.factorial(k)//z(p)*(-1)**(a*(k-len(p)))) for p in parts(k)})
    if k>=3:add(('A',k),{p:F(math.factorial(k)//z(p)) for p in parts(k) if (k-len(p))%2==0})
    if k>=3 and all(k%i for i in range(2,math.isqrt(k)+1)):
        for d in range(2,k):
            if (k-1)%d:continue
            for e in range(1,d+1):
                if d%e:continue
                r=collections.defaultdict(F);r[(1,)*k]+=1;r[(k,)]+=k-1
                for j in range(1,d):
                    order=d//math.gcd(d,j);r[(order,)*((k-1)//order)+(1,)]+=k*ram(e,j)
                add(('F',k,d,e),r)
    return tuple(rows.values())
def gen(n):
    seen=set()
    for p in parts(n):
        blocks=[block(k) for k in p if k>1]
        for combo in itertools.product(*blocks):
            desc=tuple(x[0] for x in combo)
            if any(desc[j]>desc[j+1] for j in range(len(desc)-1) if desc[j][1]==desc[j+1][1]):continue
            r={(1,)*p.count(1):F(1)}
            for _,s in combo:r=mul(r,s)
            if sum(r.values())!=0 or sum(v*(q.count(1)-1) for q,v in r.items())!=0:continue
            key=tuple(sorted(r.items()))
            if key in seen:continue
            seen.add(key);yield desc,r
def solve(n):
    P=parts(n);ids={p:i for i,p in enumerate(P)};t=(2,)+(1,)*(n-2);idp=(1,)*n
    target={p:F(2,(n-1)*z(p)) for p in P};target[idp]+=F(n-3,n-1);target[t]-=1
    desc=[];rows=[];vs=[];ii=[];jj=[]
    for d,r in gen(n):
        j=len(desc);desc.append(d);rows.append(r)
        for p,v in r.items():ii.append(ids[p]);jj.append(j);vs.append(float(v)/float(abs(target[p]))**0.65)
    print(n,len(P),len(rows),flush=True)
    A=csc_matrix((vs,(ii,jj)),shape=(len(P),len(rows)));b=np.array([float(target[p])/float(abs(target[p]))**0.65 for p in P]);scale=np.asarray(abs(A).max(axis=0).toarray()).ravel();B=A@diags(1/scale)
    res=linprog(np.ones(len(rows)),A_eq=B,b_eq=b,bounds=(0,None),method='highs-ds',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9});print(res.message,flush=True)
    if not res.success:return
    ix=[i for i,x in enumerate(res.x) if x>1e-10];print('support',len(ix),flush=True)
    M=Matrix([[rows[j].get(p,0) for j in ix] for p in P]);bb=Matrix([target[p] for p in P])
    try:w,params=M.gauss_jordan_solve(bb)
    except ValueError as e:print('reconstruct fail',e);return
    if params.rows:w=w.subs({v:0 for v in params})
    if min(w)<0:print('negative',min(w));return
    data={'n':n,'terms':[{'blocks':desc[j],'weight':str(a)} for j,a in zip(ix,w) if a>0]}
    with open(f'cert_{n}.json','w') as f:json.dump(data,f,indent=1)
    print('EXACT',len(data['terms']),flush=True)
if __name__=='__main__':
    for n in map(int,sys.argv[1:]):solve(n)

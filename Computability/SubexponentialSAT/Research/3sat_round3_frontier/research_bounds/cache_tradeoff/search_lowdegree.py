import math,json
W=math.log2(7); C=math.pi*math.sqrt(2)/math.log(2)
def terms(r):
    ks=[r//3+(i<r%3) for i in range(3)]
    a=math.sqrt(2*(r-1))/r
    ab=math.sqrt(max(2*r*k-k*k-k for k in ks))/r
    vs=[2*ks[i]*ks[j] for i,j in [(0,1),(0,2),(1,2)]]
    bs=math.sqrt(sum(vs)-(1-(W-2)**2)*min(vs))/r
    jb=math.sqrt(max(2*k*(r-k) for k in ks))/r
    return a,max(ab,bs),jb,ks

def tail(r):
    a,b,j,k=terms(r); t=2/r
    qs=[t+1e-8,t**(2/3)]
    if a<b:
        qs.append((t/(1-a/b))**2)
    qs=[q for q in qs if t<q<1]
    q=min(qs,key=lambda q:max(b,a/(1-t/math.sqrt(q)))/math.sqrt(1-q))
    f=max(b,a/(1-t/math.sqrt(q)))/math.sqrt(1-q)
    return f,q

def val(r0,rt,v):
    A=min(1/(1+2*math.log2(rt)),(11/12)/(2*math.log2(rt))); B=A-v
    if B<=0:return 1e99,None
    a,b,j,k=terms(r0); f,q=tail(rt)
    K0=C/math.sqrt(v); K1=C*(2/r0)/math.sqrt(B*(1-q))
    T=max(b*K0,a*K0+C*(2/r0)*f/math.sqrt(B))
    S=max(j*K0,terms(rt)[2]*K1)
    return T,dict(r0=r0,rt=rt,v0=v,tail_total=B,q=q,time=T,space=S,root_time=b*K0,recursive_time=a*K0+C*(2/r0)*f/math.sqrt(B))

def golden(f,lo,hi):
    x=(math.sqrt(5)-1)/2;a=hi-x*(hi-lo);b=lo+x*(hi-lo);fa=f(a);fb=f(b)
    for _ in range(90):
        if fa<fb:hi=b;b=a;fb=fa;a=hi-x*(hi-lo);fa=f(a)
        else:lo=a;a=b;fa=fb;b=lo+x*(hi-lo);fb=f(b)
    return (lo+hi)/2
out=[]
for r0 in range(3,61):
 for rt in range(3,61):
    hi=min(1/(1+2*math.log2(r0)),(11/12)/(2*math.log2(r0)),1/(1+2*math.log2(rt)),(11/12)/(2*math.log2(rt)))*(1-1e-10)
    v=golden(lambda v:val(r0,rt,v)[0],hi*.00001,hi)
    out.append(val(r0,rt,v)[1])
out.sort(key=lambda v:v['time']);print(json.dumps(out[:20],indent=2));open('eth_3sat_round3_20261027/research_bounds/cache_tradeoff/lowdegree_search_results.json','w').write(json.dumps(out[:100],indent=2)+'\n')

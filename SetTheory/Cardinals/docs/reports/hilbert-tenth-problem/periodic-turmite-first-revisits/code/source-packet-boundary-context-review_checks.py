import sys,random
sys.path.insert(0,'/workspace/shared/one-visit-turmite-boundary-20261003')
from one_visit import Lane,collision,decide,snapshot_head,colour_at,DIRS
rng=random.Random(62010103)

def independent_collision(a,b,chron,cap):
    limit=cap if a.last is None else min(cap,a.last)
    for n in range(limit+1):
        x,y=a.point(n)
        if b.d[0]:
            z=x-b.p[0]
            if z%b.d[0]: continue
            m=z//b.d[0]
        elif b.d[1]:
            z=y-b.p[1]
            if z%b.d[1]: continue
            m=z//b.d[1]
        else: m=0
        if m<0 or (b.last is not None and m>b.last): continue
        if b.point(m)!=(x,y): continue
        if chron and b.time(m)>=a.time(n): continue
        return a.time(n),n,m
    return None

counts={'lane':0,'runs':0,'heads':0,'colours':0}
for z in range(30000):
    def lane():
        return Lane(tuple(rng.randrange(-50,51) for _ in range(2)),
                    tuple(rng.randrange(-7,8) for _ in range(2)),
                    rng.randrange(-500,501),rng.randrange(1,30),
                    rng.choice([None,0,1,2,3,10,30]))
    a,b=lane(),lane(); chron=rng.choice([True,False])
    got=collision(a,b,chron)
    want=independent_collision(a,b,chron,2000)
    if want is not None:
        assert got is not None and got[0:2]==want[0:2],(a,b,chron,got,want)
    else:
        assert got is None or got[1]>2000,(a,b,chron,got,want)
    if got:
        tt,n,k=got
        assert a.point(n)==b.point(k)
        assert n>=0 and k>=0
        assert a.last is None or n<=a.last
        assert b.last is None or k<=b.last
        assert not chron or a.time(n)>b.time(k)
    counts['lane']+=1

for z in range(1200):
    m=rng.randrange(1,7); u=rng.randrange(1,6); v=rng.randrange(1,6)
    rule=''.join(rng.choice('LR') for _ in range(m))
    tile=[[rng.randrange(m) for _ in range(u)] for _ in range(v)]
    defects={tuple(rng.randrange(-30,31) for _ in range(2)):rng.randrange(m)
             for _ in range(rng.randrange(13))}
    start=tuple(rng.randrange(-6,7) for _ in range(2)); h=rng.randrange(4)
    result=decide(rule,tile,defects,start,h)
    S=4*u*v; K=len(defects)
    assert result.excursions<=K+1 and result.defects_departed<=K
    assert len(result.lanes)<=(K+1)*S
    seen={}; board=dict(defects); p=start
    max_t=min(1000,result.repeat[0] if result.repeat else 1000)
    for t in range(max_t+1):
        assert snapshot_head(result,t)==(p,h),(z,t,result)
        counts['heads']+=1
        if t%7==0 or t==max_t:
            for q in [p,(p[0]+1,p[1]),(p[0],p[1]-1),start]:
                expected=board.get(q,tile[q[1]%v][q[0]%u])
                got=colour_at(result,rule,tile,defects,q,t)
                assert got==expected,(z,t,q,got,expected)
                counts['colours']+=1
        if p in seen:
            assert result.repeat==(t,p,seen[p]),(z,t,result.repeat)
            break
        seen[p]=t
        col=board.get(p,tile[p[1]%v][p[0]%u]); board[p]=(col+1)%m
        h=(h+(1 if rule[col]=='R' else -1))%4
        dx,dy=DIRS[h]; p=(p[0]+dx,p[1]+dy)
    else:
        assert result.repeat is None or result.repeat[0]>max_t
    counts['runs']+=1
print(counts)

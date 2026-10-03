"""Exact one-visit decision for cyclic L/R turmites on a periodic board + defects.
Own implementation; Python standard library only. Time t means before departure.
Coordinates: x east, y north. Heading 0=N, 1=E, 2=S, 3=W.
"""
from dataclasses import dataclass, replace
from math import gcd

DIRS=((0,1),(1,0),(0,-1),(-1,0))

@dataclass(frozen=True)
class Lane:
    p: tuple
    d: tuple
    t: int
    period: int
    last: int | None
    heading: int = 0
    def point(self,n): return (self.p[0]+n*self.d[0],self.p[1]+n*self.d[1])
    def time(self,n): return self.t+n*self.period

@dataclass
class Result:
    repeat: tuple | None  # (least time, position, earlier time)
    lanes: list
    excursions: int
    defects_departed: int
    tail_start: int | None = None
    tail_period: int | None = None
    tail_drift: tuple | None = None


def egcd(a,b):
    """Return g >= 0 and x,y with a*x+b*y=g."""
    aa,bb=abs(a),abs(b); x0,x1,y0,y1=1,0,0,1
    while bb:
        q=aa//bb; aa,bb=bb,aa-q*bb
        x0,x1=x1,x0-q*x1; y0,y1=y1,y0-q*y1
    return aa,x0 if a>=0 else -x0,y0 if b>=0 else -y0


def ceildiv(a,b):
    assert b>0
    return -((-a)//b)


def collision(new,old,chronological=True):
    """Minimize new.time(n) with same position and optionally old.time(m)<it.
    Return (new time, new index, old index), or None. Both index sets start at 0.
    last=None denotes infinity. Rank 2/1/0 handled without lane expansion.
    """
    a,b=new.d[0],-old.d[0]; c,d=new.d[1],-old.d[1]
    e,f=old.p[0]-new.p[0],old.p[1]-new.p[1]
    def valid(n,m):
        return (n>=0 and m>=0 and (new.last is None or n<=new.last)
                and (old.last is None or m<=old.last)
                and (not chronological or new.time(n)>old.time(m)))
    det=a*d-b*c
    if det:
        nn,mm=e*d-b*f,a*f-e*c
        if nn%det or mm%det: return None
        n,m=nn//det,mm//det
        return (new.time(n),n,m) if valid(n,m) else None
    if a==b==c==d==0:
        if e or f: return None
        n=0
        if chronological: n=max(0,ceildiv(old.t+1-new.t,new.period))
        return (new.time(n),n,0) if valid(n,0) else None
    if a==b==0: a,b,e,c,d,f=c,d,f,a,b,e
    g,x,y=egcd(a,b)
    if e%g: return None
    n0,m0=x*(e//g),y*(e//g)
    kn,km=b//g,-a//g
    if c*n0+d*m0!=f or c*kn+d*km!=0: return None
    low=high=None
    def lower(const,coef):
        # Require const + coef*z >= 0.
        nonlocal low,high
        if coef>0:
            v=ceildiv(-const,coef); low=v if low is None else max(low,v)
        elif coef<0:
            v=const//(-coef); high=v if high is None else min(high,v)
        elif const<0: return False
        return low is None or high is None or low<=high
    constraints=[(n0,kn),(m0,km)]
    if new.last is not None: constraints.append((new.last-n0,-kn))
    if old.last is not None: constraints.append((old.last-m0,-km))
    if chronological:
        constraints.append((new.t+new.period*n0-old.t-old.period*m0-1,
                            new.period*kn-old.period*km))
    if not all(lower(*q) for q in constraints): return None
    if kn>0:
        assert low is not None
        z=low
    elif kn<0:
        assert high is not None
        z=high
    else:
        z=low if low is not None else high if high is not None else 0
    n,m=n0+kn*z,m0+km*z
    assert valid(n,m)
    return new.time(n),n,m


def background_excursion(tile,p,h,t):
    v,u=len(tile),len(tile[0]); states={}; trajectory=[]
    while (p[0]%u,p[1]%v,h) not in states:
        states[p[0]%u,p[1]%v,h]=len(trajectory)
        trajectory.append((p,h))
        h=(h+(1 if tile[p[1]%v][p[0]%u]=='R' else -1))%4
        dx,dy=DIRS[h]; p=(p[0]+dx,p[1]+dy)
    mu=states[p[0]%u,p[1]%v,h]; length=len(trajectory)-mu
    drift=(p[0]-trajectory[mu][0][0],p[1]-trajectory[mu][0][1])
    lanes=[Lane(q,(0,0) if i<mu else drift,t+i,1 if i<mu else length,
                0 if i<mu else None,hh) for i,(q,hh) in enumerate(trajectory)]
    return lanes,t+mu,length,drift


def truncate(lanes,through):
    result=[]
    for lane in lanes:
        if lane.t>through: continue
        last=(through-lane.t)//lane.period
        if lane.last is not None: last=min(last,lane.last)
        result.append(replace(lane,last=last))
    return result


def decide(rule,tile,defects=None,start=(0,0),heading=0):
    """tile rows and defect values are colour indices; rule is a string of L/R.
    Returns full one-visit path, or path through first repeated arrival inclusive.
    """
    assert rule and set(rule)<=set('LR')
    assert tile and tile[0] and all(len(row)==len(tile[0]) for row in tile)
    assert all(0<=z<len(rule) for row in tile for z in row)
    defects=dict(defects or {})
    assert all(0<=z<len(rule) for z in defects.values())
    assert 0<=heading<4
    turns=[[rule[z] for z in row] for row in tile]
    history=[]; p=start; h=heading; t=0; count=0; departed=set()
    while True:
        count+=1
        candidate,tail_start,period,drift=background_excursion(turns,p,h,t)
        best_repeat=None
        for a in candidate:
            for b in history+candidate:
                hit=collision(a,b)
                if hit and (best_repeat is None or hit[0]<best_repeat[0]):
                    tt,n,m=hit; best_repeat=(tt,a.point(n),b.time(m))
        best_defect=None
        for q in defects:
            target=Lane(q,(0,0),0,1,0)
            for a in candidate:
                hit=collision(a,target,chronological=False)
                if hit and (best_defect is None or hit[0]<best_defect[0]):
                    tt,n,_=hit; best_defect=(tt,q,a.heading)
        if best_repeat is not None and (best_defect is None or best_repeat[0]<=best_defect[0]):
            return Result(best_repeat,history+truncate(candidate,best_repeat[0]),count,len(departed))
        if best_defect is None:
            assert best_repeat is None and drift!=(0,0)
            return Result(None,history+candidate,count,len(departed),tail_start,period,drift)
        tt,p,h=best_defect
        assert p not in departed, 'A second defect arrival must already be a repeat.'
        history+=truncate(candidate,tt)
        departed.add(p)
        h=(h+(1 if rule[defects[p]]=='R' else -1))%4
        dx,dy=DIRS[h]; p=(p[0]+dx,p[1]+dy); t=tt+1
        assert len(departed)<=len(defects)


def snapshot_head(result,t):
    hits=[]
    for a in result.lanes:
        if t>=a.t and (t-a.t)%a.period==0:
            n=(t-a.t)//a.period
            if a.last is None or n<=a.last: hits.append((a.point(n),a.heading))
    assert len(hits)==1,(t,hits)
    return hits[0]


def visited_before(result,p,t):
    """Exact only on the certified domain: t>=0, and t<=first repeat if finite."""
    if t<0 or (result.repeat is not None and t>result.repeat[0]):
        raise ValueError("Time is outside the certified pre-departure domain")
    current=Lane(p,(0,0),t,1,0)
    return any(collision(current,a) is not None for a in result.lanes)


def colour_at(result,rule,tile,defects,p,t):
    v,u=len(tile),len(tile[0])
    initial=defects.get(p,tile[p[1]%v][p[0]%u])
    return (initial+int(visited_before(result,p,t)))%len(rule)


def brute(rule,tile,defects=None,start=(0,0),heading=0,limit=10000):
    defects=defects or {}; board=dict(defects); seen={}; out=[]
    p=start; h=heading; v,u=len(tile),len(tile[0])
    for t in range(limit+1):
        out.append((p,h))
        if p in seen: return (t,p,seen[p]),out
        seen[p]=t
        col=board.get(p,tile[p[1]%v][p[0]%u])
        board[p]=(col+1)%len(rule)
        h=(h+(1 if rule[col]=='R' else -1))%4
        dx,dy=DIRS[h]; p=(p[0]+dx,p[1]+dy)
    return None,out

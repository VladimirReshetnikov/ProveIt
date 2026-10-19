"""Literal table parser, physical permutation, and binary path arithmetic."""
from pathlib import Path
PHY=(6,2,0,4,3,7,8,5,1)

def table(p):
    r={}
    for line in Path(p).read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in r and b in (0,1) and w in (0,1) and d in ('L','R')
        r[q,b]=(w,1 if d=='R' else -1,t)
    return r


def inc(pc):
    n=len(pc);v=(int(pc,2) if pc else 0)+1
    return (format(v%2**n,'0'+str(n)+'b') if n else ''),int(v==2**n)


def strip(pc,bit,count):
    assert isinstance(count,int) and count>=0
    if count==0:return pc
    for i in range(len(pc)-1,-1,-1):
        if pc[i]==bit:
            count-=1
            if count==0:return pc[:i]
    return ''


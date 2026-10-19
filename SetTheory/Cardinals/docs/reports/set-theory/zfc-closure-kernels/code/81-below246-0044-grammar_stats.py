"""Exact compositional path statistics for shared binary source graphs."""
import rotation_search as r

cache={}
def stats(i):
    if i in cache:return cache[i]
    e=r.entries[i]
    if e[0]!='N':
        answer=(1,0,e[0]=='CD',0,0,((1,) if e[0]=='CD' else (0,)))
    else:
        ln,ll,lc,ld,lz,lh=stats(e[1]);rn,rl,rc,rd,rz,rh=stats(e[2])
        length=max(len(lh)+(1 if lc else 0),len(rh));h=[0]*length
        for j,n in enumerate(lh):h[j]+=n
        for j,n in enumerate(rh):h[j]+=n
        if lc:h[ll]-=1;h[ll+1]+=1
        while len(h)>1 and not h[-1]:h.pop()
        answer=(ln+rn,ll+1,lc,1+max(ld,rd),max(lz,rz,ll+1),tuple(h))
    cache[i]=answer;return answer

def score(i):
    hist=stats(i)[5]
    return tuple(hist[j] if j<len(hist) else 0 for j in range(70,-1,-1))

def import_graph(data):
    memo={}
    def rec(i):
        if i not in memo:
            e=data['entries'][str(i)]
            memo[i]=r.mk(('N',rec(e[1]),rec(e[2]))) if e[0]=='N' else r.mk(tuple(e))
        return memo[i]
    return rec(data['root'])

"""Universal affine register effects with an existential valid spare suffix.

This oracle composes the same four frozen Box contracts as strict_affine.
All nine semantic registers remain symbolic. At a decrement, the original
source guard and current affine offset must decide the branch; unknown guards
are rejected, never guessed. Positive decrements append a zero spare block.
The symbolic relation deliberately existentially quantifies that finite spare
suffix, so these append operations need not cancel when primary effects do.
No finite simulation is promoted to an unbounded operation contract.
"""
import common as c
from collections import Counter

ZERO=(0,)*9
STATS=Counter()

def vector(effect):
    if effect is None:return ZERO
    tag,datum=effect
    if tag=='vector':
        assert len(datum)==9 and all(type(x) is int for x in datum)
        return datum
    assert tag in ('inc','dec') and 0<=datum<9
    return tuple((1 if tag=='inc' else -1) if i==datum else 0 for i in range(9))

def encode(effect):
    nonzero=[i for i,x in enumerate(effect) if x]
    if not nonzero:return None
    if len(nonzero)==1:
        r=nonzero[0]
        if effect[r]==1:return 'inc',r
        if effect[r]==-1:return 'dec',r
    return 'vector',tuple(effect)

def bounds(branch,r):
    if branch is not None and branch[0]==r:
        return (0,0) if branch[1] else (1,None)
    return 0,None

def oracle(q,branch,state):
    if state[0]=='plain' and q in c.strict.SKIP:
        delta=vector(state[1]);r=c.strict.SKIP[q]
        assert all(bounds(branch,i)[0]+delta[i]>=0 for i in range(9))
        STATS['mark']+=1
        if state[1] is not None:STATS['mark_after_effect']+=1
        return ('2' if r==0 else '6'),('mark',r,encode(delta))
    if state[0]!='mark':return None
    r=state[1]
    assert 0<=r<9
    delta=list(vector(state[2] if len(state)==3 else None))
    if q=='73':
        delta[r]+=1;STATS['inc']+=1
        return '48',('plain',encode(delta))
    if q=='43':
        lo,hi=bounds(branch,r)
        lower=lo+delta[r]
        assert lower>=0
        if hi is not None and hi+delta[r]==0:
            STATS['dec0']+=1
            return '3',('plain',encode(delta))
        if lower>=1:
            delta[r]-=1;STATS['decp']+=1
            # The concrete suffix receives one more valid zero block.
            STATS['appended_zero_spares']+=1
            return ('63' if r==0 else '48'),('plain',encode(delta))
        raise AssertionError(('undetermined sequential guard',r,tuple(delta),branch))
    return None

def install():c.strict.oracle=oracle

if __name__=='__main__':
    install()
    assert vector(encode((0,)*9))==(0,)*9
    for r in range(9):
        d=[0]*9;d[r]=1
        assert vector(encode(d))==tuple(d)
        marked=('mark',r,('inc',r))
        assert oracle('43',None,marked)[1]==('plain',None)
    try:oracle('43',None,('mark',1,None))
    except AssertionError:pass
    else:raise AssertionError('unknown decrement guard accepted')
    print(c.check(c.T),dict(STATS))

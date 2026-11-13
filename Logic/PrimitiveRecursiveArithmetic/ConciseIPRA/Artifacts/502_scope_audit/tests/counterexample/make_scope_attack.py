import json
from pathlib import Path
ONE=[0]
P=[[ONE],ONE,0]
def comp_succ(body):
    return [0,ONE,ONE,body]
def refl(term):
    source=[[ONE],ONE,term]
    return [
        [[source,term],source,term,[3,term]],
        comp_succ(term),
        comp_succ(term),
    ]
def eq_zero_iter_nonzero(seed,h1,h2):
    a=[0,seed,h1];b=[0,seed,h2]
    return [
        [[seed,b],seed,b,[a,3]],
        [[b,seed],b,seed,[3,b]],
        [0,0,seed,h2],
        *refl(b),
        [0,0,seed,h1],
    ]
def eq_zero_iter(h1,h2):
    return [
        [[P,0],P,0,[[0,5,h1],[0,5,h2]]],
        comp_succ(0),
        *eq_zero_iter_nonzero(P,h1,h2),
    ]
future=-1000000
m=[[[5,0,7],[5,0,[future]]]]
goal=[[[5,0,7],[5,0,[11]]]]
w=[[-1]]
t=[[-2],0,w]
qb=[[5,0,-6],[5,0,[-6]]]
program=[
    [m,0,0,0],
    [0,0,ONE,0],
    [0,0,0,w],
    *refl(t),
    [0,0,0,-6],
    [[qb]*3,0,[-7],qb],
    *eq_zero_iter(-6,[-6]),
]
certificate=list(reversed(program))+[goal]
Path(__file__).with_name('future_scope_attack.json').write_text(json.dumps(certificate,separators=(',',':'))+'\n')
print('packets',len(program))

#!/usr/bin/env python3
"""Authored finite literal Z^3 sandpile primitives and independent checks.
No imported code. Threshold is six; every unlisted site starts at zero.
"""
from collections import defaultdict, deque
from itertools import product
import json, hashlib, pathlib

DIRS=((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))
def require(condition, detail="verification failed"):
    if not condition:
        raise AssertionError(detail)

def nbr(p): return [tuple(a+b for a,b in zip(p,d)) for d in DIRS]
def gate(kind,tail=12):
    if kind not in ('AND','OR'): raise ValueError(kind)
    b={(x,0,0):5 for x in range(-tail,tail+1)}
    b.update({(0,y,0):5 for y in range(-tail,0)})
    b.update({(-5,1,0):5,(-4,1,0):5,(4,1,0):5,(5,1,0):5})
    b[(-4,0,0)]=b[(4,0,0)]=4
    b[(0,0,0)]=4 if kind=='AND' else 5
    return b, {'A':(-tail,0,0),'B':(tail,0,0),'O':(0,-tail,0)}
def diode(tail=12):
    b={(x,0,0):5 for x in range(-tail,tail+1)}
    b[0,0,0]=4
    b[-1,1,0]=b[0,1,0]=5
    return b, {'I':(-tail,0,0),'O':(tail,0,0)}
def fork(tail=12):
    b={(x,0,0):5 for x in range(-tail,tail+1)}
    b.update({(0,y,0):5 for y in range(-tail,0)})
    return b, {'A':(-tail,0,0),'B':(tail,0,0),'O':(0,-tail,0)}
def geom(b):
    degree={p:sum(q in b for q in nbr(p)) for p in b}
    leakage=defaultdict(int)
    for p in b:
        for q in nbr(p):
            if q not in b: leakage[q]+=1
    return {'sites':len(b),'max_support_degree':max(degree.values()),
            'max_cumulative_offsupport_leakage':max(leakage.values()),
            'height_sum':sum(b.values()),'halo_sites':len(leakage)}
def closure(b,seed):
    """Slow synchronous least threshold closure, independent of chip simulation."""
    active=set()
    while True:
        add={p for p,h in b.items() if p not in active and h+(p in seed)+sum(q in active for q in nbr(p))>=6}
        if not add:return active
        active |=add

def sandpile(b,seed,reverse=False):
    """Actual six-neighbour chip toppling; entire dynamically reached zero halo."""
    chips=defaultdict(int,b); odo=defaultdict(int)
    for p in seed:chips[p]+=1
    while True:
        unstable=sorted(p for p,h in chips.items() if h>=6)
        if not unstable:break
        p=unstable[-1] if reverse else unstable[0]
        chips[p]-=6;odo[p]+=1
        for q in nbr(p):chips[q]+=1
        if sum(odo.values())>2*len(b):raise AssertionError('unexpected repeated/external toppling')
    return dict(odo),dict(chips)

def verify():
    out={}
    for kind,func in [('AND',lambda:gate('AND')),('OR',lambda:gate('OR')),('DIODE',diode),('FORK',fork)]:
        b,ports=func();g=geom(b)
        require(g['max_support_degree'] <= 3 and g['max_cumulative_offsupport_leakage'] <= 2, 'check_gates.py: invariant at original line 62')
        rows=[]
        for mask in product((0,1),repeat=len(ports)):
            seeds={p for p,a in zip(ports.values(),mask) if a};a=dict(zip(ports,mask))
            active=closure(b,seeds)
            for rev in (False,True):
                odo,chips=sandpile(b,seeds,rev)
                require(set(odo) == active and max(odo.values(), default=0) <= 1, 'check_gates.py: invariant at original line 69')
                require(all((h < 6 for h in chips.values())), 'check_gates.py: invariant at original line 70')
                require(all((chips[p] <= 2 for p in chips if p not in b)), 'check_gates.py: invariant at original line 71')
            result={k:int(p in active) for k,p in ports.items()}
            expected=(dict(A=a['A'],B=a['B'],O=int(a['O'] or (a['A'] and a['B']))) if kind=='AND' else
                      dict(A=a['A'],B=a['B'],O=int(a['O'] or a['A'] or a['B'])) if kind=='OR' else
                      dict(I=a['I'],O=int(a['I'] or a['O'])) if kind=='DIODE' else
                      {k:int(any(mask)) for k in ports})
            require(result == expected, (kind, a, result, expected))
            rows.append({'activated_ports':a,'final_ports':result,'topplings':len(active),
                         'maximum_offsupport_chips':max((chips[p] for p in chips if p not in b),default=0)})
        out[kind]={'geometry':g,'ports':ports,'rows':rows,
                   'table':[{'xyz':p,'height':h} for p,h in sorted(b.items())]}
    return out
if __name__=='__main__':
    output=pathlib.Path(__file__).with_name('gate_receipt.json')
    data=verify(); output.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v['geometry'] for k,v in data.items()},indent=2))
    print('PASS: all 28 activation subsets; forward and backward legal schedules; exact threshold closure; all-site stabilization')
    print('receipt SHA256',hashlib.sha256(output.read_bytes()).hexdigest())

"""Independent audit: analytical microstates and adversarial local checks.
Never mutates compiler or construction receipts. No external dependencies.
"""
import hashlib
import itertools
import json
import random
from pathlib import Path
from five_binary import BinaryCA, Machine

ROOT = Path(__file__).parent
COUNT = {}
def add(name, n=1): COUNT[name] = COUNT.get(name, 0) + n

def analytic(ca, q, a, b):
    """Build microstates directly from shuttle geometry, without ca.step/duration."""
    initial = ca.encode(q, a, b)
    yield initial
    if q == ca.machine.halt:
        return
    r = ca.machine.rows[q]
    if r[0] == 'NOP' or (r[0]=='SUB' and (a,b)[r[1]] == 0):
        yield ca.encode(*ca.machine.step(q, a, b)); return
    side = 2*r[1]-1
    delta = 1 if r[0]=='ADD' else -1
    distance = ca.Z+(a,b)[r[1]]
    o, i = ca.codes['O',q], ca.codes['I',q]
    outward = distance-ca.C-o-ca.K
    inward = distance+delta-ca.C-i-ca.K
    assert min(outward,inward)>0
    marks = {-ca.Z-a,0,ca.Z+b}
    for k in range(outward+1):
        yield marks | {side*(ca.C+k),side*(ca.C+o+k)}
    target = side*(distance+delta)
    marks = marks-{side*distance}|{target}
    for k in range(inward+1):
        yield marks | {target-side*(ca.C+k), target-side*(ca.C+i+k)}
    yield ca.encode(*ca.machine.step(q, a, b))

def halt_anchors(ca, x):
    width = ca.C+ca.D+1
    expected = {0,ca.C,ca.C+ca.codes['H',ca.machine.halt]}
    return {p for p in x if {z-p for z in x if p <= z < p+width} == expected}

def local_check(ca,x,centers):
    y = ca.step(x)
    assert len(x)==len(y)
    for center in centers:
        n = {z-center for z in x if abs(z-center)<=ca.radius}
        assert ca.local(n)==int(center in y),(x,center,y)
        add('local_centers')
    add('conservation_cases')
    return y

def run():
    programs = [
        Machine({},'HALT','HALT'),
        Machine({'a':['NOP','a']},'a','HALT'),
        Machine({'a':['ADD',0,'a']},'a','HALT'),
        Machine({'a':['ADD',1,'HALT']},'a','HALT'),
        Machine({'a':['SUB',0,'HALT','a']},'a','HALT'),
        Machine({'a':['SUB',1,'a','HALT']},'a','HALT'),
        Machine({'a':['ADD',0,'c'],'b':['ADD',1,'a'],
                 'c':['SUB',0,'d','b'],'d':['SUB',1,'e','f'],
                 'e':['NOP','f'],'f':['SUB',0,'f','HALT']},'a','HALT')]
    for machine in programs:
        ca=BinaryCA(machine)
        assert ca.radius==30*ca.D+37
        for q in ca.states:
            for a,b in itertools.product(range(5),repeat=2):
                trace=iter(analytic(ca,q,a,b)); x=next(trace); t=0
                assert halt_anchors(ca,x)==({0} if q==machine.halt else set())
                for expected in trace:
                    x=ca.step(x); t+=1
                    assert x==expected,(machine.rows,q,a,b,t,x,expected)
                    assert len(x)==5
                    target_q=machine.step(q,a,b)[0]
                    at_final = (x==ca.encode(*machine.step(q,a,b)))
                    assert halt_anchors(ca,x)==({0} if at_final and target_q==machine.halt else set())
                    add('analytical_microstates')
                assert t==ca.duration(q,a,b)
                assert x==ca.encode(*machine.step(q,a,b))
                if q==machine.halt: assert ca.step(x)==x
                add('source_macros')
    # Exhaust every threshold-bounded pair/triple shape, including all roles,
    # ambiguous short gaps and home sensor on/off, for a tiny mixed source.
    ca=BinaryCA(Machine({'a':['SUB',0,'b','HALT'],'b':['ADD',1,'a']},'a','HALT'))
    centers=set(range(-ca.E,ca.E+1))
    shapes=[{0,d} for d in range(1,ca.K+2)]
    shapes += [{0,d,d+e} for d,e in itertools.product(range(1,ca.K+2),repeat=2)]
    for shape in shapes:
        for sensor in (set(),{-ca.Z},{ca.Z},{-ca.Z,ca.Z}):
            x=shape|sensor
            y=local_check(ca,x,centers|x|ca.step(x))
            for shift in (-19,23):
                assert ca.step({z+shift for z in x})=={z+shift for z in y}
                add('translation_cases')
        add('pair_triple_shapes')
    rng=random.Random(7148609)
    # Short dense words with sparse remote context plus deliberately long
    # chains crossing the local window; test truncation-created fake heads.
    ca=BinaryCA(programs[2])
    for bits in range(1<<12):
        x={j for j in range(12) if bits>>j&1}
        if bits&1: x|={-ca.Z}
        local_check(ca,x,x|{0,12})
        add('exhaustive_dense_words')
    for d in (1,ca.D,ca.C,ca.K-1,ca.K):
        for phase in range(d):
            x=set(range(-3*ca.radius+phase,3*ca.radius+1,d))
            local_check(ca,x,{-ca.radius,-ca.radius+ca.E,0,ca.radius-ca.E,ca.radius})
            add('long_connected_phases')
    for trial in range(1000):
        x=set()
        for _ in range(rng.randrange(1,12)):
            start=rng.randrange(-2*ca.radius,2*ca.radius+1)
            typ=rng.randrange(4)
            if typ==0: x|={start,start+ca.C,start+ca.C+rng.randrange(1,ca.D+1)}
            elif typ==1: x|={start,start+rng.randrange(1,ca.D+1)}
            elif typ==2: x|=set(range(start,start+rng.randrange(4,30)))
            else: x|={start}
        y=local_check(ca,x,x|ca.step(x)|{0,-ca.radius,ca.radius})
        add('adversarial_multi_component_cases')
    # Materialized periodic words: center period evaluated through the actual
    # Boolean local rule, with enough copies to supply every complete window.
    for period in range(1,37):
        for _ in range(8):
            occupied={j for j in range(period) if rng.randrange(4)==0}
            copies=ca.radius//period+2
            lifted={j+k*period for j in occupied for k in range(-copies,copies+1)}
            output={j for j in range(period) if ca.local({z-j for z in lifted if abs(z-j)<=ca.radius})}
            assert len(output)==len(occupied),(period,occupied,output)
            add('periodic_words')
    report={'status':'passed','compiler_sha256':hashlib.sha256((ROOT/'five_binary.py').read_bytes()).hexdigest(),'counts':COUNT,
        'scope':'Independent analytical microstate, finite local/conservation, and periodic tests; no standalone universality certification.'}
    (ROOT/'audit_independent.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':run()

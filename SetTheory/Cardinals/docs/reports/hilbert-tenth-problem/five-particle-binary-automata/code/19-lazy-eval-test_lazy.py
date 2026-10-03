"""Deterministic differential tests; no asserts, so checks survive python -O."""
import copy
import itertools
import json
import random
import time
from hashlib import sha256
from pathlib import Path
import lazy_reversible as lazy

HERE = Path(__file__).resolve().parent
RNG = random.Random(202610030529)
COUNTS = dict(sources=0, factor_equalities=0, differential_cases=0,
              inverse_cases=0, sparse_gate_cases=0, invalid_inputs=0,
              candidate_completeness_cases=0)


def check(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def branch(name, source, target, side=1, delta=0, guard=None):
    return dict(name=name, source=source, target=target, side=side,
                delta=delta, guard=guard or {'op':'true'})


def source(controls, branches, J=0):
    return dict(schema='reversible-two-counter-v1', controls=controls,
                start=controls[0], halt=controls[-1], class_cut=J, branches=branches)


def generated_sources():
    yield source(['h'], [])
    yield source(['q','h'], [branch('inc','q','h',1,1)])
    yield source(['q','h'], [branch('dec','q','h',-1,-1,{'op':'gt','counter':0,'value':0})])
    yield source(['q','h'], [branch('zero','q','h',guard={'op':'eq','counter':0,'value':0}),
                             branch('pos','q','h',guard={'op':'gt','counter':0,'value':0})])
    yield source(['q','r','h'], [branch('unused','q','h',1,1,{'op':'or','args':[]}),
                                 branch('same','q','q',guard={'op':'eq','counter':1,'value':0}),
                                 branch('end','q','h',guard={'op':'gt','counter':1,'value':0})])
    for n in range(2, 8):
        controls = [f'q{i}' for i in range(n)]
        rows = []
        for i in range(n-1):
            delta, side = RNG.choice((-1,0,1)), RNG.choice((-1,1))
            g = {'op':'gt','counter':0 if side == -1 else 1,'value':0} if delta == -1 else {'op':'true'}
            rows.append(branch(f'e{i}',controls[i],controls[i+1],side,delta,g))
        yield source(controls, rows, 1)
    yield source(['q','a','b','h'], [
        branch('left','q','a',-1,1,{'op':'eq','counter':0,'value':0}),
        branch('right','q','b',1,-1,{'op':'and','args':[{'op':'gt','counter':0,'value':0},{'op':'gt','counter':1,'value':0}]}),
        branch('done','a','h',-1,0),
    ], 1)


def differential(a, b, x, inverse=False, detailed=False):
    x = frozenset(x)
    y, stats = a.step(x, inverse=inverse, verify=True, trace=True)
    z = b.step(x, inverse=inverse, verify=True)
    check(y == z, ('composition mismatch', a.source_data, sorted(x), inverse, sorted(y), sorted(z),dict(stats)))
    check(len(y) == len(x), 'mass changed')
    restored = a.step(y, inverse=not inverse, verify=True)
    check(restored == x, ('inverse mismatch', x, y, restored))
    COUNTS['differential_cases'] += 1
    COUNTS['inverse_cases'] += 1
    if detailed:
        candidates = set(a.candidate_indices(x))
        for i, g in enumerate(b.E+b.P):
            raw = g.raw(x)
            if raw:
                check(i in candidates, ('missing candidate', i, g.name, x, raw))
            check(lazy.apply_gate(g, x, True)[0] == g.apply(x, True), ('sparse gate mismatch',g.name,x))
            COUNTS['sparse_gate_cases'] += 1
        COUNTS['candidate_completeness_cases'] += 1


def test_source(data, index):
    a, b = lazy.compile_lazy_source(data), lazy.ref.compile_source(data)
    COUNTS['sources'] += 1
    check(a.ledger() == b.ledger(), 'ledger mismatch')
    for i, g in enumerate(b.E+b.P):
        h = a.gate_at(i)
        check(g == h, ('factor mismatch',index,i,g,h))
        COUNTS['factor_equalities'] += 1
        # Every endpoint family is exercised; translate alternating endpoints.
        for shape in g.shapes:
            shift = -79 if i % 2 else 103
            x = frozenset(v+shift for v in shape)
            differential(a,b,x,inverse=bool(i%2))
            # A random spoiler may affect raw, isolation, competition or context.
            noise = RNG.choice((-g.M,-g.L,-g.B,0,g.B,g.L,g.M,a.Z,-a.Z)) + RNG.choice((-1,0,1))
            differential(a,b,x|{shift+noise},inverse=bool((i+1)%2))
    for _ in range(160):
        mass = RNG.randrange(0,18)
        if RNG.randrange(2):
            x = frozenset(RNG.randrange(-2*a.Z,2*a.Z+1) for _ in range(mass))
        else:
            i = RNG.randrange(a.factors)
            g = b.E[i] if i < len(b.E) else b.P[i-len(b.E)]
            shape = RNG.choice(g.shapes)
            x = frozenset(shape)|{RNG.randrange(-g.M-2,g.M+3) for _ in range(max(0,mass-len(shape)))}
        differential(a,b,x,inverse=bool(RNG.randrange(2)),detailed=(_<12))
    for q in a.controls:
        for sign in ('+','-'):
            for c0,c1 in ((0,0),(1,0),(0,1),(2,3)):
                x=a.encode(q,c0,c1,sign)
                check(x==b.encode(q,c0,c1,sign),'encoding mismatch')
                differential(a,b,x)
                differential(a,b,x,inverse=True)
    # One factor may have simultaneous distant active anchors; raw competitors
    # within M may block one another despite disjoint supports.
    if a.factors:
        for i in (0,a.factors-1):
            g=a.gate_at(i)
            for separation in (g.M-1,g.M,g.M+1,4*g.M+13):
                x=set(g.P)|{separation+v for v in g.P}
                differential(a,b,x,detailed=True)
        x=a.encode(a.start,2,3)
        huge=-(1<<2048)
        shifted=frozenset(v+huge for v in x)
        differential(a,b,shifted,inverse=True)
        check(a.step(shifted)==frozenset(v+huge for v in a.step(x)),'translation mismatch')


def test_invalid():
    good=source(['q','h'],[branch('inc','q','h',1,1)])
    bad=[]
    for path,val in [(('class_cut',),True),(('class_cut',),-1),(('controls',),('q','h')),
                     (('start',),1),(('halt',),'missing'),(('schema',),'no'),
                     (('branches',0,'side'),True),(('branches',0,'delta'),1.0),
                     (('branches',0,'side'),0),(('branches',0,'target'),'missing'),
                     (('branches',0,'source'),'h'),(('branches',0,'guard'),{'op':'eq','counter':1,'value':0}),
                     (('branches',0,'guard'),{'op':'eq','counter':True,'value':0})]:
        d=copy.deepcopy(good); at=d
        for k in path[:-1]: at=at[k]
        at[path[-1]]=val;bad.append(d)
    d=copy.deepcopy(good);d['branches']*=2;bad.append(d)
    d=copy.deepcopy(good);d['extra']=1;bad.append(d)
    d=copy.deepcopy(good);d['branches'][0]['guard']={'op':'not'};bad.append(d)
    d=copy.deepcopy(good);d['branches'][0]['delta']=-1;bad.append(d)
    d=copy.deepcopy(good);d['branches'].append(branch('dup','q','h',1,1));bad.append(d)
    cycle={'op':'not'};cycle['arg']=cycle
    d=copy.deepcopy(good);d['branches'][0]['guard']=cycle;bad.append(d)
    for d in bad:
        outcomes=[]
        for fn in (lazy.compile_lazy_source,lazy.ref.compile_source):
            try: fn(d)
            except (TypeError,ValueError) as e: outcomes.append(type(e))
            else: outcomes.append(None)
        check(outcomes[0] is not None and outcomes[0]==outcomes[1],('validation mismatch',outcomes,d))
        COUNTS['invalid_inputs']+=1
    a=lazy.compile_lazy_source(good)
    for value in ([0,1],{True},{1.0},(1,2)):
        try: a.step(value)
        except TypeError: COUNTS['invalid_inputs']+=1
        else: raise RuntimeError('invalid positions accepted')
    for kwargs in ({'inverse':1},{'verify':0},{'trace':None}):
        try: a.step(set(),**kwargs)
        except TypeError: COUNTS['invalid_inputs']+=1
        else: raise RuntimeError('invalid Boolean flag accepted')
    for value in (True,1.0,-1,a.factors):
        try: a.gate_at(value)
        except (TypeError,ValueError): COUNTS['invalid_inputs']+=1
        else: raise RuntimeError('invalid factor index accepted')
    for action in (lambda: setattr(a, 'D', 3),
                   lambda: a.control_index.__setitem__('q', 4),
                   lambda: a.source_data.__setitem__('class_cut', 9),
                   lambda: a.home_out.__setitem__(0, ()),
                   lambda: setattr(a.branches[0], 'delta', 0)):
        try: action()
        except (AttributeError, TypeError): COUNTS['invalid_inputs']+=1
        else: raise RuntimeError('immutable metadata changed')
    original=a.encode('q',0,0)
    good['controls'].append('x');good['branches'][0]['guard']['op']='false'
    check(a.encode('q',0,0)==original,'source mutation leaked')


def test_cascade():
    data=source(['q','h'],[branch('inc','q','h',1,1)])
    a,b=lazy.compile_lazy_source(data),lazy.ref.compile_source(data)
    x=frozenset((-118,-112,0,18,23))
    differential(a,b,x,detailed=True)
    def block(seq,x):
        for g in seq:x=g.apply(x,True)
        return x
    check(block(b.P,block(b.P,x))!=x,'phase cascade fixture is not a cascade')
    check(block(b.E,block(b.E,x))!=x,'edge cascade fixture is not a cascade')
    _,stats=a.step(x,trace=True)
    check(stats['changed_factors']>=3,('expected changing-factor cascade',dict(stats)))
    return {'input':sorted(x),'output':sorted(a.step(x)),'stats':dict(stats)}


def main():
    start=time.perf_counter()
    test_invalid()
    for i,data in enumerate(generated_sources()):
        test_source(data,i)
        print('source',i,'passed',COUNTS,flush=True)
    # Exhaust every support in a contiguous nine-cell window for pair cases.
    data=source(['q','h'],[branch('inc','q','h',1,1)])
    a,b=lazy.compile_lazy_source(data),lazy.ref.compile_source(data)
    for bits in range(1<<9):
        differential(a,b,{i-4 for i in range(9) if bits>>i&1},bool(bits%2))
    cascade=test_cascade()
    receipt=dict(status='passed',counts=COUNTS,cascade=cascade,
                 elapsed_seconds=time.perf_counter()-start,
                 frozen_compiler_sha256=lazy.FROZEN_SHA256,
                 evaluator_sha256=sha256((HERE/'lazy_reversible.py').read_bytes()).hexdigest())
    out=HERE/('test-optimized-receipt.json' if not __debug__ else 'test-receipt.json')
    out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

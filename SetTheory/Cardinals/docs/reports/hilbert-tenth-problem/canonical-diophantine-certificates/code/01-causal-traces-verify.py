#!/usr/bin/env python3
"""Deterministic exact finite tests. Run from any working directory.

These checks exercise the implementation, not a formal proof of the theorems.
No third-party packages are required. Test ranges and counts are recorded.
"""
from __future__ import annotations
from itertools import product, combinations
from collections import Counter
from pathlib import Path
import json, platform, random, time
from causal_diophantine import *

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260930
rng = random.Random(SEED)
counts = Counter()
start = time.perf_counter()

def require(condition, message='verification failed'):
    if not condition:
        raise AssertionError(message)

def sequential(a, b, x):
    y = a.apply(x)
    return None if y is None else b.apply(y)

def petri_criterion(c, d, e, f):
    v, w = d-c, f-e
    if v == w == 0: return True
    if v > 0 and w > 0: return c == e
    if v < 0 and w < 0: return d == f
    if v == 0: return c <= min(e, f)
    if w == 0: return e <= min(c, d)
    return False

def multiset_words(ns):
    if not any(ns):
        yield ()
        return
    for a, n in enumerate(ns):
        if n:
            rest = list(ns); rest[a] -= 1
            for tail in multiset_words(rest):
                yield (a,) + tail

# 1. Domain-box commutation against direct operational semantics.
small = []
for lo in range(4):
    for v in range(-lo, 3):
        for hi in (lo, lo+1, lo+3, None):
            small.append(Action(f'a{len(small)}', (lo,), (v,), (hi,)))
for a, b in product(small, repeat=2):
    direct = all(sequential(a,b,(x,)) == sequential(b,a,(x,)) for x in range(26))
    require(commute(a,b) == direct, ('box', a,b))
    counts['box_pairs'] += 1
for c, d, e, f in product(range(6), repeat=4):
    a, b = Action.petri('a',(c,),(d,)), Action.petri('b',(e,),(f,))
    require(commute(a,b) == petri_criterion(c,d,e,f), ('petri',c,d,e,f))
    counts['petri_classification_pairs'] += 1

# 2. Resource envelope vs EVERY permutation; SOME also for commuting support.
for case in range(1200):
    p, m = rng.randint(1,3), rng.randint(1,4)
    actions = []
    for i in range(m):
        lo = tuple(rng.randrange(4) for _ in range(p))
        dv = tuple(rng.randint(-l, 2) for l in lo)
        hi = tuple(None if rng.randrange(2) else l+rng.randrange(5) for l in lo)
        actions.append(Action(str(i),lo,dv,hi))
    ns = tuple(rng.randrange(3) for _ in range(m))
    if sum(ns)>6: ns = (0,)*m
    words = list(multiset_words(ns))
    for _ in range(8):
        x = tuple(rng.randrange(11) for _ in range(p))
        outputs = [execute(actions,x,w) for w in words]
        expected = all(y is not None for y in outputs)
        got = envelope_apply(actions,x,ns)
        require((got is not None) == expected, ('envelope',actions,ns,x))
        if expected: require(all(y == got for y in outputs))
        act = [i for i,n in enumerate(ns) if n]
        if all(commute(actions[i],actions[j]) for i,j in combinations(act,2)):
            require((got is not None) == any(y is not None for y in outputs))
            counts['commuting_existential_cases'] += 1
        sys = compile_accelerator(actions)
        ass = complete_accelerator(actions,x,ns)
        require((ass is not None)==expected)
        if ass is not None:
            require(sys.check(ass), 'accelerator certificate')
            for name in sys.witnesses:
                bad = ass.copy(); bad[name] += 1
                require(not sys.check(bad), ('accelerator mutation',name))
                counts['auxiliary_mutations'] += 1
            counts['valid_accelerator_certificates'] += 1
        counts['envelope_state_multisets'] += 1
        counts['serialized_executions'] += len(words)

# 3. All independence graphs on three labels: normal forms vs swap components.
edge_list = list(combinations(range(3),2))
for mask in range(8):
    pairs = frozenset(e for j,e in enumerate(edge_list) if (mask>>j)&1)
    for length in range(7):
        words = list(product(range(3),repeat=length))
        parent = {w:w for w in words}
        def find(w):
            while parent[w] != w:
                parent[w] = parent[parent[w]]; w=parent[w]
            return w
        for w in words:
            for j in range(length-1):
                if independent(w[j],w[j+1],pairs):
                    v = w[:j]+(w[j+1],w[j])+w[j+2:]
                    rw, rv = find(w),find(v)
                    parent[rw]=rv
        nf_to_component, component_to_nf = {}, {}
        for w in words:
            nf, comp = foata(w,pairs), find(w)
            require(canonical_layers(nf,3,pairs))
            if nf in nf_to_component: require(nf_to_component[nf] == comp)
            if comp in component_to_nf: require(component_to_nf[comp] == nf)
            nf_to_component[nf], component_to_nf[comp] = comp,nf
            counts['normal_form_words'] += 1
    inert = [Action.petri(str(i),(1,),(1,)) for i in range(3)]
    H=3; sys=compile_history(inert,H,pairs)
    for bits in product(range(2),repeat=9):
        layers = [tuple(i for i in range(3) if bits[3*h+i]) for h in range(3)]
        canon = canonical_layers(layers,3,pairs)
        ass = complete_history(inert,(1,),layers,H,pairs)
        require((ass is not None)==canon)
        if canon:
            trimmed=tuple(c for c in layers if c)
            require(foata(tuple(i for c in layers for i in c),pairs)==trimmed)
            require(sys.check(ass))
            for name in sys.witnesses:
                if name.startswith('z_'): continue  # Changes semantic trace, not auxiliary data.
                bad=ass.copy(); bad[name]+=1
                require(not sys.check(bad),('history mutation',name))
                counts['auxiliary_mutations']+=1
            counts['canonical_matrices']+=1
        counts['boolean_layer_matrices']+=1

# 4. Random execution histories, incl nontrivial lower/upper guards.
for case in range(200):
    p,m,H = rng.randint(1,3),rng.randint(1,4),rng.randint(0,5)
    a=[]
    for i in range(m):
        lo=tuple(rng.randrange(3) for _ in range(p))
        dv=tuple(rng.randint(-l,2) for l in lo)
        hi=tuple(None if rng.randrange(2) else l+rng.randrange(6) for l in lo)
        a.append(Action(str(i),lo,dv,hi))
    I=independence(a); sys=compile_history(a,H,I)
    f=sum(hi is not None for act in a for hi in act.upper)
    e=m*(m-1)//2-len(I); d=m+2*e
    N=0 if H==0 else H*(m*(1+p)+f+2*p)+(H-1)*(d+p)
    E=p if H==0 else H*m+H*e+3*H*p+2*H*(p*m+f)+(H-1)*(d+m)
    require(len(sys.witnesses)==N and len(sys.residuals)==E,('counts',p,m,H))
    require(all(r.degree<=2 for _,r in sys.residuals))
    for trial in range(12):
        x=tuple(rng.randrange(8) for _ in range(p))
        word=tuple(rng.randrange(m) for _ in range(rng.randrange(H+1)))
        nf=foata(word,I)
        if len(nf)>H: continue
        y=execute(a,x,word)
        ass=complete_history(a,x,nf,H,I)
        require((ass is None)==(y is None),('history semantics',a,x,word))
        if ass is not None:
            require(sys.check(ass))
            require(tuple(ass[f'y_{j}'] for j in range(p))==y)
            bad=ass.copy(); bad['y_0']+=1
            require(not sys.check(bad))
            counts['valid_history_certificates']+=1
        counts['random_history_cases']+=1
    counts['history_count_formula_instances']+=1

# 5. Full bounded root enumeration in small instances, not only produced witnesses.
read=[Action.petri('read',(1,),(1,))]
root_counts={}
for H in (0,1,2):
    sys=compile_history(read,H)
    found=[]
    for vals in product(range(2),repeat=len(sys.witnesses)):
        ass={'x_0':1,'y_0':1}; ass.update(zip(sys.witnesses,vals))
        if sys.check(ass): found.append(ass)
        counts['fully_enumerated_history_assignments']+=1
    require(len(found)==H+1,('full root count',H,len(found)))
    root_counts[f'read_height_{H}']=len(found)
dec=[Action.petri('dec',(1,),(0,))]
sys=compile_accelerator(dec)
for x,y,n in product(range(3),repeat=3):
    roots=0
    for vals in product(range(3),repeat=len(sys.witnesses)):
        ass={'x_0':x,'y_0':y,'n_0':n};ass.update(zip(sys.witnesses,vals))
        roots+=sys.check(ass)
        counts['fully_enumerated_accelerator_assignments']+=1
    require(roots==int(x>=n and y==x-n),('full accelerator',x,y,n,roots))

# 6. Large exact accelerator, expanded polynomial and degree.
a=[Action.petri('loss_one',(2,),(1,)),
   Action.petri('loss_two',(3,),(1,)),
   Action.petri('shared_read',(1,),(1,))]
ns=(10**100,10**80,10**90);x=(ns[0]+2*ns[1]+1,)
sys=compile_accelerator(a);ass=complete_accelerator(a,x,ns)
require(sys.check(ass)); require(ass['y_0']==1)
P=sys.expanded();require(P.degree==4 and P.evaluate(ass)==0)
require(len(sys.witnesses)==11 and len(sys.residuals)==18)
(ROOT/'examples').mkdir(exist_ok=True)
sys.export(ROOT/'examples'/'shared_resource_accelerator.json',ass,expand=True)
hsys=compile_history(a,3);layers=((0,1,2),(0,2),(0,))
hass=complete_history(a,(9,),layers,3)
require(hsys.check(hass)); require(hsys.expanded().degree==4)
hsys.export(ROOT/'examples'/'canonical_history.json',hass,expand=True)
example={'accelerator_witnesses':len(sys.witnesses),'accelerator_residuals':len(sys.residuals),
         'expanded_monomials':len(P.terms),'degree':P.degree,
         'multiplicities':[str(n) for n in ns],
         'canonical_history_witnesses':len(hsys.witnesses),
         'canonical_history_residuals':len(hsys.residuals)}

# 7. Fixed-block composition, with and without existential counts.
phases = [[Action.petri('loss_one',(2,),(1,)), Action.petri('read',(1,),(1,))],
          [Action.petri('inc',(0,),(1,))]]
for x in range(8):
    for na,nr,ni in product(range(4),repeat=3):
        ns=((na,nr),(ni,))
        ass=complete_blocks(phases,(x,),ns)
        direct=execute(phases[0],(x,),(0,)*na+(1,)*nr)
        if direct is not None: direct=execute(phases[1],direct,(0,)*ni)
        require((ass is None)==(direct is None))
        if ass is not None:
            for existential in (False,True):
                bs=compile_blocks(phases,existential)
                require(bs.check(ass))
                require(bs.expanded().degree<=4)
                baseN=1+sum(2*len(a)+2+len(a) for a in phases)
                require(len(bs.witnesses)==baseN+(3 if existential else 0))
            require(ass['y_0']==direct[0])
        counts['fixed_block_cases']+=1
# All 60 serializations of the worked trace agree.
worked_words=list(multiset_words((3,1,2)))
require(len(worked_words)==60)
for word in worked_words:
    require(foata(word,independence(a))==layers)
    require(execute(a,(9,),word)==(4,))
counts['worked_example_serializations']=len(worked_words)

# 8. Arbitrary fixed words (not assumed commuting) and their powers.
word_actions=[Action('inc',(0,),(1,),(4,)),
              Action('dec',(1,),(-1,),(None,)),
              Action('zero',(0,),(0,),(0,))]
for length in range(6):
    for word in product(range(3),repeat=length):
        ws=compile_word_power(word_actions,word)
        for n,x in product(range(5),range(9)):
            direct=execute(word_actions,(x,),word*n)
            ass=complete_word_power(word_actions,word,(x,),n)
            require((ass is None)==(direct is None),('word power',word,n,x))
            if ass is not None:
                require(ws.check(ass))
                require(ass['y_0']==direct[0])
            counts['word_power_cases']+=1

report={'status':'PASS','seed':SEED,'python':platform.python_version(),
        'scope':'Exact finite implementation checks; not proof-assistant verification',
        'test_counts':dict(counts),'small_full_root_counts':root_counts,
        'large_example':example,'elapsed_seconds':round(time.perf_counter()-start,3)}
(ROOT/'data').mkdir(exist_ok=True)
(ROOT/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
lines=['PASS: all exact finite checks completed.',report['scope'],f'Python {report["python"]}; seed {SEED}.','']
lines += [f'{k}: {v}' for k,v in counts.items()]
lines += ['',f'Full tiny history root counts: {root_counts}',f'Large example: {example}',
          f'Elapsed seconds (environment-dependent): {report["elapsed_seconds"]}']
(ROOT/'data'/'verification.txt').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines))

"""Exact checks of the article's worked examples and denominator sharpness."""
from fractions import Fraction as F
from pathlib import Path
import json
from signal_geometry import trace, polynomial, linear_rank, compile_schema, witness
from signal_sparse import compile_sparse, sparse_witness


def certify(machine, labels, pos, cap, halt=False):
    layers = trace(machine, labels, pos, cap)
    schema = [z['blocks'] for z in layers]
    cert = compile_sparse(machine, labels, schema, halt=halt)
    a = sparse_witness(cert, pos, layers)
    assert polynomial(cert, a) == 0
    return layers, cert, a

# Every residual of the complete displayed annihilation polynomial.
annihilation_cases = 0
example_witness = None
for p0 in range(5):
    for gap in range(1, 9):
        p1 = p0 + gap
        machine = ({'R': 2, 'S': 0}, {frozenset(('R', 'S')): ()})
        layers, c, a = certify(machine, ['R', 'S'], [p0, p1], 1, True)
        assert c['B'] == 2 and len(c['variables']) == 5 and len(c['rows']) == 6
        T, X, d, u, h = gap, 2*p1, gap-1, gap-1, 2*gap-1
        rows = [p1-p0-u-1, T-d-1, X-2*p0-2*T, X-2*p1,
                2*p1-2*p0-h-1, 2*p1-2*p0-2*T]
        assert sum(z*z for z in rows) == 0
        assert (a['t1'], a['e0'], a['d1'], a['input_gap0'], a['lower0']) == (T,X,d,u,h)
        assert linear_rank(c) == 5
        positive = {v: a[v]+1 for v in c['variables']}
        assert all(x >= 1 for x in positive.values())
        restored = {f'x{j}': x for j,x in enumerate([p0,p1])}
        restored.update({v: positive[v]-1 for v in c['variables']})
        assert polynomial(c, restored) == 0
        if (p0,p1) == (0,1): example_witness = dict(T=T,X=X,d=d,u=u,h=h)
        annihilation_cases += 1

speeds = {'a':0,'b':2,'c':3,'d':4}
machine = (speeds,{frozenset('da'):()})
labels, pos = list('dada'), [0,4,10,14]
false_schema = [[[0,1],[2],[3]]]
c = compile_sparse(machine, labels, false_schema)
fake = [dict(dt=F(1), end=list(map(F,[4,4,14,14])), blocks=false_schema[0])]
rejected = False
try:
    a = sparse_witness(c,pos,fake)
    rejected = polynomial(c,a) != 0
except AssertionError:
    rejected = True
assert rejected
# Identify the exact strict endpoint that rejects the surviving omitted pair.
life = next(x for x in c['lifetimes'] if x['pair'] == ('initial2','initial3'))
assert life['upper_equal'] is False
assert 48-4*12 == 0
layers, correct, a = certify(machine,labels,pos,1,True)
assert len(correct['events']) == 2 and a['e0']==48 and a['e1']==168
assert a['t1']==12 and correct['final_live']==[]

fan_machine = (speeds,{frozenset('da'):('b','c')})
layers, fan, _ = certify(fan_machine,labels,pos,1)
assert len(fan['final_live']) == 4
try:
    compile_sparse(fan_machine,labels,[z['blocks'] for z in layers],halt=True)
except AssertionError:
    fan_halt_rejected = True
else:
    fan_halt_rejected = False
assert fan_halt_rejected

empty_cases = 0
for labels,pos in [([],[]),(['a'],[0]),(['d'],[7])]:
    for halt in (False,True):
        z,c,a = certify((speeds,{}),labels,pos,0,halt)
        assert c['variables']==[] and polynomial(c,a)==0
        baseline=compile_schema((speeds,{}),labels,[],halt)
        assert baseline['variables']==[] and polynomial(baseline,witness(baseline,pos,[]))==0
        empty_cases += 1

# Fixed integer data; alternating collisions approach t=2 from below.
bounce = ({'L':3,'R':2,'F':4,'B':0},
          {frozenset(('F','R')):('B','R'), frozenset(('L','B')):('L','F')})
periods = 32
layers, bc, ba = certify(bounce,['L','F','R'],[0,1,2],2*periods)
t=F(0); times=[]
for index,layer in enumerate(layers):
    t += layer['dt']; times.append(t)
    k=index//2+1
    expected = 2-F(3,2)*F(1,3**(k-1)) if index%2==0 else 2-F(1,3**(k-1))
    assert t==expected and 0<t<2
    assert all(0<=x<6 for x in layer['end'])
    if index%2==1: assert t.denominator==3**(k-1)
assert len(layers)==64
assert max(ba.values()) <= 60**64*2
print_data = dict(annihilation_cases=annihilation_cases,
                  annihilation_witness=example_witness,
                  positive_translation_checks=annihilation_cases,
                  hidden_final_collision_rejected=True,
                  hidden_final_collision_reason='Surviving pair has upper gap 0; strict gap requires h+1 >= 1.',
                  simultaneous_annihilation_events=2,
                  nonhalting_fan_rejected=True,
                  empty_singleton_convention_checks=empty_cases,
                  sharpness_prefix_batches=len(layers),
                  sharpness_initial_times=list(map(str,times[:6])),
                  sharpness_last_left_denominator=str(times[-1].denominator))
Path(__file__).with_name('worked_examples_receipt.json').write_text(json.dumps(print_data,indent=2)+'\n')
print(json.dumps(print_data,indent=2))

#!/usr/bin/env python3
"""Reproducible exact tests and complete example exports. Standard library only."""
from bellman_diophantine import *
from check_certificate import check
from collections import Counter
from itertools import product
import random
import platform

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts'
OUT.mkdir(exist_ok=True)
rng = random.Random(20261002)
counts = Counter()


def require(condition, category):
    if not condition:
        raise AssertionError(category)
    counts[category] += 1


def rejected(call):
    try:
        call()
    except (ValueError, TypeError):
        counts['invalid_input_rejections'] += 1
    else:
        raise AssertionError('invalid input accepted')


# Exhaust all min/max local tuples in a box, including every tie and bad output.
for owner in ('min', 'max'):
    for a, b, y, u, v in product(range(5), range(5), range(7), range(7), range(7)):
        r0, r1 = (a-y-u, b-y-v) if owner == 'min' else (y-a-u, y-b-v)
        q = r0*r0 + r1*r1 + u*v
        optimum = min(a,b) if owner == 'min' else max(a,b)
        gu, gv = (a-y, b-y) if owner == 'min' else (y-a, y-b)
        require((q == 0) == (y == optimum and u == gu and v == gv), 'local_quadratic_iff')

# Random counter programs; all control labels and bounded counter pairs.
programs = []
for _ in range(10):
    instructions = []
    for q in range(3):
        instructions.append(Instruction(rng.choice(('inc','dec')), rng.randrange(2),
                                        rng.randrange(4), rng.randrange(4)))
    programs.append(Program(2, tuple(instructions+[Instruction('halt')])))
for program in programs:
    raw = counter_circuit(program)
    compiled = compile_program(program)
    for state, a, b in product(range(4), range(4), range(4)):
        x = program.encode(state, (a,b))
        expected = program.encode(*program.step(state,(a,b)))
        require(raw.apply(x) == expected, 'counter_circuit_step')
        require(compiled.circuit.apply(x) == expected, 'layered_counter_step')
        scale = F(rng.randrange(1,9), 16)
        require(raw.apply([scale*v for v in x]) == [scale*v for v in expected], 'positive_homogeneity')
    for g in compiled.circuit.gates[compiled.circuit.inputs:]:
        require(all(compiled.circuit.gates[j].depth == g.depth-1 for j in g.args),
                'one_layer_dependencies')
    # Every microstep for a randomly chosen input, not only macro boundaries.
    state, cs = rng.randrange(4), (rng.randrange(3),rng.randrange(3))
    w = compiled.initialize(state, cs, shifted=False)
    configs = [(state,cs)]
    for _ in range(4):
        configs.append(program.step(*configs[-1]))
    for n in range(3*compiled.macro+2):
        q = (n+compiled.macro-1)//compiled.macro
        expected = [v/compiled.scale**q for v in program.encode(*configs[q])]
        require([w[compiled.plus(i)] for i in range(compiled.circuit.inputs)] == expected,
                'pipeline_all_microsteps')
        require(all(w[compiled.plus(i)] == -w[compiled.minus(i)]
                    for i in range(len(compiled.circuit.gates))), 'dual_rail_invariance')
        w = compiled.game.apply(w, discounted=False)

# Full-support lift on arbitrary (not just dual-rail) vectors: every coordinate difference.
for _ in range(12):
    n=4
    owners = tuple(rng.choice(('lin','min','max')) for _ in range(n))
    actions = []
    for owner in owners:
        aa=[]
        for _ in range(1 if owner == 'lin' else 2):
            dest=[rng.randrange(n) for _ in range(4)]
            aa.append(tuple((j,F(dest.count(j),4)) for j in sorted(set(dest))))
        actions.append(tuple(aa))
    base=Game(owners,tuple(actions))
    mixed=Game(owners,tuple(actions),F(1,2))
    w=[F(rng.randrange(-8,9),8) for _ in range(n)]
    u=w.copy()
    for t in range(10):
        for i,j in product(range(n),repeat=2):
            require(u[i]-u[j] == F(1,4)**t*(w[i]-w[j]),'common_reset_difference_identity')
        w=base.apply(w,discounted=False)
        u=mixed.apply(u)
    require(min(p for aa in mixed.rows() for a in aa for p in a.values())>=F(1,2*n),
            'full_support_bound')

# Chance-only matrix / Skolem lift, including negative and zero matrix entries.
for _ in range(25):
    d=rng.randrange(1,5)
    A=[[rng.randrange(-3,4) for _ in range(d)] for _ in range(d)]
    x=[rng.randrange(-4,5) for _ in range(d)]
    game,v,pair,C=matrix_game(A,x)
    R=power_two_at_least(max(map(abs,x)))
    for t in range(9):
        require(v[pair[0]]-v[pair[1]] == F(1,4*C)**t*F(x[0],2*R), 'skolem_lift_exact')
        x=[sum(a*y for a,y in zip(row,x)) for row in A]
        v=game.apply(v)

# Small complete 12-witness polynomial, expanded without a CAS.
toy=Game(('min','max'),(
    (((0,F(1,2)),(1,F(1,2))),((1,F(1)),)),
    (((0,F(1)),),((0,F(1,2)),(1,F(1,2))))),F(1,2))
qc=certificate(toy,[1,0],2,(0,1))
require(qc.evaluate()==0,'small_certificate_zero')
require(len(qc.assignment)==12,'small_certificate_count')
expanded=qc.expanded()
for _ in range(100):
    v=[rng.randrange(6) for _ in qc.labels]
    val=sum(a*(v[m[0]] if len(m)==1 else v[m[0]]*v[m[1]] if len(m)==2 else 1)
            for m,a in expanded.items())
    require(val==qc.evaluate(v),'expanded_polynomial_identity')
qc.export(OUT/'small_certificate.json')
(OUT/'small_game.json').write_text(json.dumps(toy.export(),indent=2)+'\n')
(OUT/'small_expanded_quadratic.json').write_text(json.dumps({
    'variable_labels':qc.labels,'terms':[[list(m),a] for m,a in sorted(expanded.items())]},indent=2)+'\n')
for i in range(len(qc.assignment)):
    v=qc.assignment.copy();v[i]+=1
    require(qc.evaluate(v)>0,'small_witness_mutation_rejected')

# General discount supported by the exporter, plus exact integer/rational agreement.
for _ in range(30):
    game=Game(toy.owners,toy.actions,F(1,2),rng.choice((F(1,2),F(2,3),F(3,4))))
    initial=[rng.randrange(6),rng.randrange(6)]
    T=rng.randrange(6)
    q=certificate(game,initial,T,(0,1))
    v=list(map(F,initial))
    for _ in range(T):v=game.apply(v)
    require((q.evaluate()==0)==(v[0]==v[1]),'integer_fraction_agreement')
    require(len(q.labels)==(game.n+2*game.binary)*T,'exact_arity')
    require(len(q.squares)==(game.n+game.binary)*T+1,'exact_square_count')
    require(len(q.products)==game.binary*T,'exact_product_count')

# Published counter example: decrement twice, then take the zero branch to halt.
countdown=Program(1,(Instruction('dec',0,0,1),Instruction('halt')))
compiled=compile_program(countdown,reset=F(1,2))
initial=compiled.initialize(0,[2]);d0,A=integer_numerators(initial)
first=2*compiled.macro+1
v=initial.copy(); timeline=[]
for t in range(first+3):
    q=(t+compiled.macro-1)//compiled.macro
    r,s=compiled.halt_pair
    gap=v[r]-v[s]
    expected= -F(1,2)*F(1,4)**t/F(compiled.scale)**q if t<first else F(0)
    require(gap==expected,'countdown_exact_gap')
    require(sum(v,F(0))/len(v)==F(1,2)**(t+1),'countdown_exact_mean')
    require(max(v)<=F(1,2)**t and min(v)>=0,'countdown_value_bounds')
    timeline.append({'time':t,'machine_steps':q,'gap':str(gap),'equal':gap==0})
    v=compiled.game.apply(v)
q=certificate(compiled.game,A,first,compiled.halt_pair,initial_denominator=d0)
require(q.evaluate()==0,'countdown_certificate_zero')
require(certificate(compiled.game,A,first-1,compiled.halt_pair,initial_denominator=d0).evaluate()>0,
        'prehalt_certificate_rejected')
# Exact local change in Q for incrementing each coordinate, without re-evaluating the dense polynomial.
diag=[0]*len(q.labels)
for lin in q.squares:
    for j,a in lin.items():
        if j>=0:diag[j]+=a*a
for u,v in q.products:
    diag[u]+=q.assignment[v];diag[v]+=q.assignment[u]
for value in diag:require(value>0,'all_countdown_coordinate_mutations_rejected')
q.export(OUT/'countdown_certificate.json')
write_game(compiled,OUT/'countdown_game.json',counters=[2])
(OUT/'countdown_timeline.json').write_text(json.dumps(timeline,indent=2)+'\n')

# Tied actions have no selector multiplicity; every gap is exactly zero.
ties=certificate(toy,[2,2],3,(0,1))
require(ties.evaluate()==0,'ties_certificate_zero')
for label,value in zip(ties.labels,ties.assignment):
    if label.startswith('gap'):require(value==0,'ties_have_zero_gaps')

# Validate formats and domains, including bool (a Python int subclass).
rejected(lambda:Program(0,(Instruction('halt'),)))
rejected(lambda:Program(1,(Instruction('inc',2,0),Instruction('halt'))))
rejected(lambda:Program(1,(Instruction('dec',0,0,5),Instruction('halt'))))
rejected(lambda:countdown.encode(0,[-1]))
rejected(lambda:countdown.encode(0,[True]))
rejected(lambda:certificate(toy,[1,0],-1,(0,1)))
rejected(lambda:certificate(toy,[1],2,(0,1)))
rejected(lambda:certificate(toy,[1,0],2,(0,2)))
rejected(lambda:qc.evaluate([-1]*12))
rejected(lambda:Game(('lin',),((((0,F(1,2)),),),)))
rejected(lambda:matrix_game([[1,2]],[1]))
rejected(lambda:matrix_game([[F(1,2)]],[1]))

# Erasing the halt configuration yields exact finite convergence of the full vector.
fixcomp=compile_program(countdown,reset=F(1,2),erase_halt=True,reward=F(1,4))
fixinit=fixcomp.initialize(0,[2])
v=fixinit.copy(); hit=None
for t in range(4*fixcomp.macro+1):
    if all(y==F(1,2) for y in v) and hit is None:hit=t
    require(max(abs(y-F(1,2)) for y in v)<=F(1,2)*F(1,4)**t,
            'fixedpoint_error_bound')
    v=fixcomp.game.apply(v)
require(hit is not None and hit<=4*fixcomp.macro,'erasing_eventual_fixedpoint')
fixden,fixA=integer_numerators(fixinit)
fixq=certificate(fixcomp.game,fixA,hit,fixcomp.halt_pair,
                 initial_denominator=fixden,target=F(1,2))
require(fixq.evaluate()==0,'fixedpoint_certificate_zero')
require(certificate(fixcomp.game,fixA,hit-1,fixcomp.halt_pair,
                    initial_denominator=fixden,target=F(1,2)).evaluate()>0,
        'pre_fixedpoint_certificate_rejected')
fixq.export(OUT/'fixedpoint_certificate.json')
write_game(fixcomp,OUT/'fixedpoint_game.json',counters=[2])
# All-erasing / initially halted edge case, including unused deep gates.
for program,state,cs in ((Program(1,(Instruction('halt'),)),0,[0]),(countdown,1,[3])):
    er=compile_program(program,erase_halt=True,reset=F(1,2),reward=F(1,4))
    vals=er.initialize(state,cs)
    for _ in range(er.macro):vals=er.game.apply(vals)
    require(all(y==F(1,2) for y in vals),'initial_halt_drains_pipeline')
# Erasing circuits retain exact nonhalting clock values at every microstep.
for program in programs[:4]:
    er=compile_program(program,erase_halt=True,reset=F(1,2))
    raw=counter_circuit(program,erase_halt=True)
    x=program.encode(0,[1,2]); xs=[x]
    for _ in range(4):xs.append(raw.apply(xs[-1]))
    vals=er.initialize(0,[1,2],shifted=False)
    for t in range(3*er.macro+1):
        j=(t+er.macro-1)//er.macro
        expected=[a*F(1,4)**t/er.scale**j for a in xs[j]]
        require([vals[er.plus(i)] for i in range(er.circuit.inputs)]==expected,
                'erasing_microstep_simulation')
        vals=er.game.apply(vals)
# Consensus terminal condition is also exported without selector variables.
cons=certificate(toy,[1,0],2,(0,1),consensus=True)
require(cons.evaluate()==0,'consensus_certificate_zero')
# Rewards, denominators and rational point targets checked independently of the reduction.
for _ in range(20):
    random_game=Game(toy.owners,toy.actions,F(1,2),F(2,3),F(1,5))
    input_A=[rng.randrange(5),rng.randrange(5)]; den=rng.randrange(1,6)
    T=rng.randrange(5); target=F(3,5)
    obj=certificate(random_game,input_A,T,(0,1),initial_denominator=den,target=target)
    vals=[F(a,den) for a in input_A]
    for _ in range(T):vals=random_game.apply(vals)
    require((obj.evaluate()==0)==all(y==target for y in vals),'affine_point_certificate_iff')

independent={}
for name in ('small','countdown','fixedpoint'):
    independent[name]=check(OUT/f'{name}_certificate.json',OUT/f'{name}_game.json')
    require(independent[name]['polynomial_value']==0,'independent_export_checks')

summary={'python':platform.python_version(),'seed':20261002,'total_assertions':sum(counts.values()),
         'counts':dict(sorted(counts.items())), 'independent_checks':independent,
         'countdown':{'states':compiled.game.n,'binary_states':compiled.game.binary,
                      'circuit_nodes_including_inputs':len(compiled.circuit.gates),
                      'macro_period':compiled.macro,'normalization_scale':compiled.scale,
                      'normalizers':compiled.normalizers,'initial_denominator':d0,
                      'machine_halting_steps':3,'first_game_equality':first,
                      **{k:v for k,v in q.metadata.items() if k not in ('initial_numerators','observed_pair')}},
         'fixedpoint':{'states':fixcomp.game.n,'binary_states':fixcomp.game.binary,
                       'circuit_nodes_including_inputs':len(fixcomp.circuit.gates),
                       'macro_period':fixcomp.macro,'normalization_scale':fixcomp.scale,
                       'first_fixedpoint_time':hit,'initial_denominator':fixden,
                       'natural_witnesses':len(fixq.labels),'squares':len(fixq.squares),
                       'products':len(fixq.products)},
         'small_expanded_monomials':len(expanded),
         'scope':'Exact finite tests, not a proof assistant verification or a universal game table.'}
(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))

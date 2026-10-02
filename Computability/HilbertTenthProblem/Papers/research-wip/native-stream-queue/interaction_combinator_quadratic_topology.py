"""Guarded natural-domain delta-delta topology relations and finite histories.

Complete port tables and cyclic-wire counts are paid. Only externally chosen
annihilation schedules are compiled; this is not the universal six-rule system.
"""
import argparse
from collections import Counter
from copy import deepcopy
from functools import lru_cache
from itertools import combinations
import hashlib
import json
from math import prod
from pathlib import Path
from types import ModuleType

ORACLE_FILE = 'interaction_combinator_wiring_obstruction.py'
ORACLE_SHA256 = '5c4881f28ae3286097c9629751856118d06365300de77d40eaecd087d6d8b0bc'
JOIN = (2, 3, 0, 1)
DIRECT = ((0, 2), (1, 3))
CROSS = ((0, 1), (0, 3), (1, 2), (2, 3))
SCOPE = ('Exact natural-domain selected delta-delta rewrites and externally fixed finite deletion '
         'schedules, with full matching tables and port-free cycle counts. No universal six-rule '
         'compiler, variable-time compression, ordinary-input loader, integer-domain graph '
         'equivalence, global universal bound, or arithmetic optimality is claimed.')


@lru_cache(None)
def _oracle():
    path = Path(__file__).with_name(ORACLE_FILE)
    code = path.read_bytes()
    assert hashlib.sha256(code).hexdigest() == ORACLE_SHA256, 'pinned wiring source mismatch'
    module = ModuleType('_interaction_topology_pinned_oracle')
    module.__file__ = str(path)
    exec(compile(code, str(path), 'exec'), module.__dict__)
    return module


def exact(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def cells_key(cells):
    assert type(cells) is tuple and len(cells) >= 2 and len(cells) % 2 == 0
    assert all(type(c) is int and c >= 0 for c in cells)
    assert tuple(sorted(set(cells))) == cells
    return cells


def pair_key(cells, pair):
    assert type(pair) is tuple and len(pair) == 2
    assert all(type(c) is int and c >= 0 for c in pair)
    assert pair[0] < pair[1] and set(pair) <= set(cells)
    return pair


def step_key(cells, pair, mode):
    cells_key(cells); pair_key(cells, pair)
    assert type(mode) is str and mode in ('quadratic', 'cubic')
    return cells, pair, mode


def history_key(cells, pairs):
    cells_key(cells)
    assert type(pairs) is tuple and pairs
    current = cells
    for pair in pairs:
        pair_key(current, pair)
        current = tuple(c for c in current if c not in pair)
    return cells, pairs


def edge_name(kind, a, b):
    a, b = sorted((a, b)); return f'{kind}_{a}_{b}'


def _execute(rows, values):
    env = dict(values)
    for n, op, a, b in rows:
        a = env[a] if type(a) is str else a
        b = env[b] if type(b) is str else b
        env[n] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def _add(p, q, sign=1):
    out = dict(p)
    for mon, coef in q.items():
        out[mon] = out.get(mon, 0) + sign*coef
        if not out[mon]: del out[mon]
    return out


def _multiply(p, q):
    out = {}
    for m, a in p.items():
        for n, b in q.items():
            powers = dict(m)
            for name, exponent in n: powers[name] = powers.get(name, 0)+exponent
            mon = tuple(sorted(powers.items()))
            out[mon] = out.get(mon, 0)+a*b
    return {mon:coef for mon,coef in out.items() if coef}


def _residual_polynomials(rows, residuals, coordinates):
    # Exact sparse integer arithmetic, before the final SOS. Monomials are
    # tuples of (coordinate-name, positive exponent), sorted by name.
    env = {n:{((n, 1),):1} for n in coordinates}
    for n, op, a, b in rows:
        assert type(n) is str and n not in env and op in ('+', '-', '*')
        for arg in (a, b): assert (type(arg) is int or type(arg) is str and arg in env)
        p = env[a] if type(a) is str else ({():a} if a else {})
        q = env[b] if type(b) is str else ({():b} if b else {})
        env[n] = _multiply(p, q) if op == '*' else _add(p, q, 1 if op == '+' else -1)
    return tuple(tuple((coef, mon) for mon,coef in sorted(env[r].items())) for r in residuals)


def _finish(rows, residuals, parameters, auxiliaries):
    rows, residuals = tuple(rows), tuple(residuals)
    parameters, auxiliaries = tuple(parameters), tuple(auxiliaries)
    assert len(parameters+auxiliaries) == len(set(parameters+auxiliaries))
    polynomials = _residual_polynomials(rows, residuals, parameters+auxiliaries)
    degrees = tuple(max((sum(e for n,e in mon) for c,mon in p), default=0) for p in polynomials)
    top = max(degrees); i = degrees.index(top)
    leading = tuple((c,mon) for c,mon in polynomials[i] if sum(e for n,e in mon) == top)
    full = list(rows); squares = []
    for i, r in enumerate(residuals):
        n = f'square_{i}'; full.append((n, '*', r, r)); squares.append(n)
    output = squares[0]
    for i, r in enumerate(squares[1:]):
        n = f'sum_{i}'; full.append((n, '+', output, r)); output = n
    def count(schedule):
        return dict(M=sum(op == '*' for n,op,a,b in schedule),
                    A=sum(op != '*' for n,op,a,b in schedule))
    cert, poly = count(rows), count(full)
    return dict(certificate_source=rows, residuals=residuals,
        residual_polynomials=polynomials, source=tuple(full), output=output,
        parameters=parameters, auxiliaries=auxiliaries,
        degree_certificate=dict(residual=residuals[degrees.index(top)], degree=top,
                                leading=leading, exact_sos_degree=2*top,
                                reason='A nonzero highest homogeneous residual part has a nonzero square; a sum of real squares cannot cancel.'),
        ledger=dict(certificate_operations=len(rows), certificate=cert,
                    residuals=len(residuals), polynomial_operations=len(full), polynomial=poly,
                    source_coordinates=len(parameters), quantified_successor_and_helper_coordinates=len(auxiliaries),
                    exact_sos_degree=2*top),
        domain='naturals_including_zero', oracle_file=ORACLE_FILE, oracle_sha256=ORACLE_SHA256,
        scope=SCOPE)


@lru_cache(None)
def _build_step(cells=(0, 1, 2, 3), pair=(0, 1), mode='quadratic', matching_rows=True):
    step_key(cells, pair, mode)
    assert type(matching_rows) is bool
    _oracle()
    ports = [3*c+p for c in cells for p in range(3)]
    surviving_cells = tuple(c for c in cells if c not in pair)
    surviving = [3*c+p for c in surviving_cells for p in range(3)]
    aux = [3*pair[0]+1, 3*pair[0]+2, 3*pair[1]+1, 3*pair[1]+2]
    x = lambda a, b: edge_name('x', a, b)
    e = lambda i, j: x(aux[i], aux[j])
    parameters = [x(a, b) for a, b in combinations(ports, 2)]+['L0']
    auxiliaries = [edge_name('y', a, b) for a, b in combinations(surviving, 2)]+['L1']
    rows = []; residuals = []; helpers = {}
    def gate(n, op, a, b):
        rows.append((n, op, a, b)); return n
    def add_list(stem, terms):
        value = terms[0]
        for i, term in enumerate(terms[1:]): value = gate(f'{stem}_{i}', '+', value, term)
        return value
    if matching_rows:
        for a in ports:
            total = add_list(f'matching_sum_{a}', [x(a, b) for b in ports if b != a])
            residuals.append(gate(f'matching_residual_{a}', '-', total, 1))
    residuals.append(gate('active_residual', '-', x(3*pair[0], 3*pair[1]), 1))
    if mode == 'quadratic':
        for b in surviving[1:]:
            for i in range(4):
                z = f'z_{b}_{i}'; auxiliaries.append(z)
                terms = [x(b, aux[JOIN[i]])]
                for j in range(4):
                    if j in (i, JOIN[i]): continue
                    terms.append(gate(f'route_product_{b}_{i}_{j}', '*', e(JOIN[i], JOIN[j]), x(b, aux[j])))
                rhs = add_list(f'route_rhs_{b}_{i}', terms)
                helpers[z] = rhs
                residuals.append(gate(f'route_residual_{b}_{i}', '-', z, rhs))
    for a, b in combinations(surviving, 2):
        terms = [x(a, b)]
        if mode == 'quadratic':
            for i in range(4): terms.append(gate(f'new_product_{a}_{b}_{i}', '*', x(a, aux[i]), f'z_{b}_{i}'))
        else:
            for i, j in DIRECT:
                terms.extend([gate(f'direct_{a}_{b}_{i}_{j}', '*', x(a, aux[i]), x(b, aux[j])),
                              gate(f'direct_{a}_{b}_{j}_{i}', '*', x(a, aux[j]), x(b, aux[i]))])
            for i, j in CROSS:
                first = gate(f'cross_{a}_{b}_{i}_{j}', '*', x(a, aux[i]), x(b, aux[j]))
                second = gate(f'cross_{a}_{b}_{j}_{i}', '*', x(a, aux[j]), x(b, aux[i]))
                total = gate(f'cross_sum_{a}_{b}_{i}_{j}', '+', first, second)
                terms.append(gate(f'cross_route_{a}_{b}_{i}_{j}', '*', e(JOIN[i], JOIN[j]), total))
        rhs = add_list(f'new_rhs_{a}_{b}', terms)
        residuals.append(gate(f'new_residual_{a}_{b}', '-', edge_name('y', a, b), rhs))
    c1 = gate('cycle_cross_one', '*', e(0, 1), e(2, 3))
    c2 = gate('cycle_cross_two', '*', e(0, 3), e(1, 2))
    delta = add_list('cycle_delta', [e(0, 2), e(1, 3), c1, c2])
    target = gate('cycle_new_count', '+', 'L0', delta)
    residuals.append(gate('cycle_residual', '-', 'L1', target))
    p = _finish(rows, residuals, parameters, auxiliaries)
    P = len(ports); s = len(surviving); v = max(s-1, 0); K = s*(s-1)//2
    if mode == 'quadratic':
        M = 8*v+4*K+2; A = (P*(P-1) if matching_rows else 0)+12*v+5*K+6
        E = (P if matching_rows else 0)+4*v+K+2
    else:
        M = 16*K+2; A = (P*(P-1) if matching_rows else 0)+13*K+6
        E = (P if matching_rows else 0)+K+2
    assert p['ledger']['certificate'] == {'M': M, 'A': A}
    assert len(residuals) == E and p['ledger']['polynomial'] == {'M': M+E, 'A': A+E-1}
    p.update(kind='selected_step', cells=cells, pair=pair, surviving_cells=surviving_cells, aux_ports=tuple(aux),
             helpers=helpers, mode=mode, matching_rows=matching_rows)
    return p



@lru_cache(None)
def _build_history(cells=(0, 1, 2, 3), pairs=((0, 1), (2, 3))):
    history_key(cells, pairs)
    current = cells; rows = []; residuals = []; parameters = []; auxiliaries = []; steps = []
    for t, pair in enumerate(pairs):
        p = _build_step(current, pair, 'quadratic', t == 0)
        mapping = {}
        for name in p['parameters']:
            mapping[name] = f'L_{t}' if name == 'L0' else f'X{t}'+name[1:]
        for name in p['auxiliaries']:
            mapping[name] = f'L_{t+1}' if name == 'L1' else (f'X{t+1}'+name[1:] if name.startswith('y_') else f'T{t}_{name}')
        for n, op, a, b in p['certificate_source']: mapping[n] = f'T{t}_{n}'
        at = lambda n: mapping[n] if isinstance(n, str) else n
        rows.extend((mapping[n], op, at(a), at(b)) for n, op, a, b in p['certificate_source'])
        residuals.extend(mapping[r] for r in p['residuals'])
        if t == 0: parameters = [mapping[n] for n in p['parameters']]
        auxiliaries.extend(mapping[n] for n in p['auxiliaries'])
        steps.append(dict(packet=p, mapping=mapping)); current = p['surviving_cells']
    assert len(parameters+auxiliaries) == len(set(parameters+auxiliaries))
    packet = _finish(rows, residuals, parameters, auxiliaries)
    packet.update(kind='selected_history', initial_cells=cells, final_cells=current, pairs=pairs, steps=tuple(steps))
    return packet



def build_step(cells=(0, 1, 2, 3), pair=(0, 1), mode='quadratic'):
    """A complete selected step, always including the source matching rows."""
    return deepcopy(_build_step(*step_key(cells, pair, mode), True))


def build_history(cells=(0, 1, 2, 3), pairs=((0, 1), (2, 3))):
    return deepcopy(_build_history(*history_key(cells, pairs)))


def checked(packet):
    assert type(packet) is dict and type(packet.get('kind')) is str
    if packet['kind'] == 'selected_step':
        key = step_key(packet.get('cells'), packet.get('pair'), packet.get('mode'))
        canonical = _build_step(*key, True)
    else:
        assert packet['kind'] == 'selected_history'
        key = history_key(packet.get('initial_cells'), packet.get('pairs'))
        canonical = _build_history(*key)
    assert exact(packet, canonical), 'complete exact-type canonical source packet required'


def _assignment(packet, values, allow_signed):
    assert type(allow_signed) is bool
    assert type(values) is dict
    assert all(type(n) is str and type(v) is int and (allow_signed or v >= 0) for n,v in values.items())
    assert set(values) == set(packet['parameters']+packet['auxiliaries']), 'complete named assignment required'


def execute(packet, values, *, allow_signed=False):
    """Run the actual full SOS schedule after canonical source validation."""
    checked(packet); _assignment(packet, values, allow_signed)
    return _execute(packet['source'], values)


def evaluate(packet, values):
    return execute(packet, values)[packet['output']]


def evaluate_integer(packet, values):
    """Signed algebraic evaluation only; no integer-domain graph claim."""
    return execute(packet, values, allow_signed=True)[packet['output']]


def polynomial_source(packet=None):
    if packet is None: packet = build_step()
    checked(packet)
    return deepcopy(dict(coordinates=packet['parameters']+packet['auxiliaries'],
                         source=packet['source'], output=packet['output'],
                         residuals=packet['residuals'], finalizer='sum of squares'))


def residual_polynomials(packet=None):
    if packet is None: packet = build_step()
    checked(packet); return deepcopy(packet['residual_polynomials'])


def ledger(packet=None):
    if packet is None: packet = build_step()
    checked(packet); return deepcopy(packet['ledger'])


def degree_certificate(packet=None):
    if packet is None: packet = build_step()
    checked(packet); return deepcopy(packet['degree_certificate'])


def _step_values(packet, net):
    oracle = _oracle(); oracle.check_net(net)
    assert tuple(net['cells']) == packet['cells'] and list(packet['pair']) in oracle.active_pairs(net)
    target = oracle.annihilate(net, list(packet['pair']))
    values = {n:0 for n in packet['parameters']+packet['auxiliaries']}
    for a,b in net['wires']: values[edge_name('x',a,b)] = 1
    for a,b in target['wires']: values[edge_name('y',a,b)] = 1
    values['L0'] = net['loops']; values['L1'] = target['loops']
    trial = _execute(packet['certificate_source'], values)
    for z,rhs in packet['helpers'].items(): values[z] = trial[rhs]
    return values


def step_values(packet, net):
    checked(packet); assert packet['kind'] == 'selected_step'
    return _step_values(packet, net)


def history_values(packet, net):
    checked(packet); assert packet['kind'] == 'selected_history'
    oracle = _oracle(); oracle.check_net(net)
    values = {}; current = deepcopy(net)
    for step in packet['steps']:
        local = _step_values(step['packet'], current)
        for name,value in local.items():
            mapped = step['mapping'][name]
            if mapped in values: assert values[mapped] == value
            values[mapped] = value
        current = oracle.annihilate(current, list(step['packet']['pair']))
    _assignment(packet, values, False)
    return values


def _sparse_value(poly, values):
    return sum(c*prod(values[n]**e for n,e in mon) for c,mon in poly)


def guard_audit():
    counts = Counter()
    def reject(fn):
        try: fn()
        except (AssertionError,ValueError,TypeError,KeyError): counts['rejected_callers'] += 1
        else: raise AssertionError('malformed caller accepted')
    for cells in ([0,1], (False,1), (0.0,1), (0,0), (1,0), (-1,0), (0,1,2), ()):
        reject(lambda cells=cells:build_step(cells))
        reject(lambda cells=cells:build_history(cells))
    for pair in ([0,1], (False,1), (0.0,1), (1,0), (0,0), (0,4), (), (0,)):
        reject(lambda pair=pair:build_step(pair=pair))
        reject(lambda pair=pair:build_history(pairs=(pair,)))
    for mode in (True,1,'quartic',None): reject(lambda mode=mode:build_step(mode=mode))
    for pairs in ([],(),((0,1),(0,2)),((0,1),(2,3),(4,5)),([0,1],)):
        reject(lambda pairs=pairs:build_history(pairs=pairs))
    for factory in (build_step,lambda:build_step(mode='cubic'),lambda:build_step((0,1),(0,1)),build_history):
        packet = factory(); net = _oracle().examples()['A']
        if packet['kind']=='selected_step' and packet['cells']==(0,1):
            net = _oracle().make_net((0,1),((0,3),(1,4),(2,5)))
        values = history_values(packet,net) if packet['kind']=='selected_history' else step_values(packet,net)
        for value in (True,1.0):
            bad=deepcopy(packet);rows=list(bad['source']);n,op,a,b=rows[-1];rows[-1]=(n,op,a,value);bad['source']=tuple(rows)
            for api in (checked,polynomial_source,residual_polynomials,ledger,degree_certificate):
                reject(lambda bad=bad,api=api:api(bad))
            bad=deepcopy(packet);bad['ledger']['residuals']=value
            reject(lambda bad=bad:checked(bad))
        for field,value in (('scope','universal'),('domain','integers'),('source',[]),('oracle_sha256','bad'),('residuals',()),('residual_polynomials',())):
            bad=deepcopy(packet);bad[field]=value
            reject(lambda bad=bad:checked(bad))
        for bad in ({},dict(values,extra=0),dict(values,**{next(iter(values)):False}),dict(values,**{next(iter(values)):0.0})):
            for api in (evaluate,evaluate_integer):reject(lambda bad=bad,api=api:api(packet,bad))
        bad=dict(values);bad[next(iter(values))]=-1
        reject(lambda bad=bad:evaluate(packet,bad))
        reject(lambda:execute(packet,values,allow_signed=1))
        # Exact sparse monomial/constant and schedule-schema mutations are guarded.
        bad=deepcopy(packet);polys=list(bad['residual_polynomials']);terms=list(polys[0]);c,mon=terms[0];terms[0]=(float(c),mon);polys[0]=tuple(terms);bad['residual_polynomials']=tuple(polys)
        reject(lambda bad=bad:checked(bad))
        if packet['kind']=='selected_step':
            bad=deepcopy(packet);bad['matching_rows']=False;reject(lambda bad=bad:checked(bad))
        # Cold construction must never expose mutable private cache objects.
        _build_step.cache_clear();_build_history.cache_clear()
        frozen=factory();damaged=factory();damaged['ledger']['residuals']=-1
        if 'steps' in damaged:damaged['steps'][0]['packet']['helpers'].clear()
        else:damaged['helpers'].clear()
        assert exact(factory(),frozen);checked(frozen)
        counts['cold_cache_isolation_checks']+=1
    net = _oracle().examples()['A'];packet=build_step()
    for key,badvalue in (('cells',[False,1,2,3]),('loops',False),('loops',0.0),('loops',-1),('wires',())):
        bad=deepcopy(net);bad[key]=badvalue;reject(lambda bad=bad:step_values(packet,bad))
    reject(lambda:history_values(build_history(),_oracle().examples()['B']))
    return dict(counts)


def exhaustive_audit():
    oracle = _oracle(); counts = Counter(); local_patterns=set(); digest=hashlib.sha256()
    for cells in ((0,1),(0,1,2,3)):
        for wires in oracle.matchings(tuple(range(3*len(cells)))):
            net=oracle.make_net(cells,wires);counts['complete_input_matchings']+=1
            for pair in oracle.active_pairs(net):
                counts['enabled_rewrites']+=1
                for mode in ('quadratic','cubic'):
                    p=_build_step(cells,tuple(pair),mode,True);values=_step_values(p,net)
                    env=_execute(p['source'],values)
                    assert env[p['output']]==0 and all(env[r]==0 for r in p['residuals'])
                    assert all(type(v) is int and v>=0 for v in values.values())
                    counts['complete_natural_zero_checks']+=1
                    wrong=dict(values);wrong['L1']+=1
                    assert _execute(p['source'],wrong)[p['output']]>0
                    counts['wrong_cycle_count_rejections']+=1
                    ys=[n for n in p['auxiliaries'] if n.startswith('y_')]
                    if ys:
                        wrong=dict(values);wrong[ys[0]]+=1
                        assert _execute(p['source'],wrong)[p['output']]>0
                        counts['wrong_successor_edge_rejections']+=1
                    es=tuple(values[edge_name('x',p['aux_ports'][i],p['aux_ports'][j])] for i,j in combinations(range(4),2))
                    local_patterns.add(es)
                    digest.update(json.dumps([mode,cells,pair,net['wires'],values['L1'],es],separators=(',',':')).encode())
    assert len(local_patterns)==10
    # A fixed whole history uses the same emitted source at every valid input.
    hist=build_history()
    for wires in oracle.matchings(tuple(range(12))):
        net=oracle.make_net((0,1,2,3),wires)
        if [0,1] not in oracle.active_pairs(net):continue
        second=oracle.annihilate(net,[0,1])
        if [2,3] not in oracle.active_pairs(second):continue
        values=history_values(hist,net)
        assert evaluate(hist,values)==0
        counts['fixed_two_step_history_zero_checks']+=1
    for loops in (0,1,7,10**30):
        net=deepcopy(oracle.examples()['A']);net['loops']=loops
        values=step_values(build_step(),net);assert values['L1']==loops
        values=history_values(hist,net);assert values['L_2']==loops+2 and evaluate(hist,values)==0
        counts['preexisting_cycle_history_checks']+=1
    # Check sparse residuals against the literal SLP off zero, with signed coordinates.
    for p in (build_step(),build_step(mode='cubic'),build_step((0,1),(0,1)),hist):
        for case in range(12):
            values={n:((i*7+case*11)%9)-4 for i,n in enumerate(p['parameters']+p['auxiliaries'])}
            env=execute(p,values,allow_signed=True)
            direct=[_sparse_value(r,values) for r in p['residual_polynomials']]
            assert direct==[env[r] for r in p['residuals']]
            assert sum(x*x for x in direct)==env[p['output']]
            counts['signed_sparse_and_slp_comparisons']+=1
    # Every helper is uniquely defined: perturb each independently on the full actual example.
    p=build_step();values=step_values(p,oracle.examples()['A'])
    for helper in p['helpers']:
        wrong=dict(values);wrong[helper]+=1
        assert evaluate(p,wrong)>0;counts['individual_helper_mutations_rejected']+=1
    signed=build_step((0,1),(0,1));bad={n:0 for n in signed['parameters']+signed['auxiliaries']}
    bad['x_0_3']=1;bad['L1']=4;aux=signed['aux_ports']
    for i,j,value in ((0,1,1),(2,3,1),(0,2,1),(1,3,1),(0,3,-1),(1,2,-1)):
        bad[edge_name('x',aux[i],aux[j])]=value
    assert min(bad.values())==-1 and evaluate_integer(signed,bad)==0
    try:evaluate(signed,bad)
    except AssertionError:pass
    else:raise AssertionError('natural evaluator accepted signed counterexample')
    return dict(counts=dict(counts),local_partial_matching_patterns=len(local_patterns),
                record_sha256=digest.hexdigest(),signed_domain_counterexample=bad)


def verify():
    oracle=_oracle()
    four=build_step();cubic=build_step(mode='cubic');two=build_step((0,1),(0,1));history=build_history()
    assert four['ledger']['polynomial']==dict(M=151,A=321)
    assert cubic['ledger']['polynomial']==dict(M=271,A=361)
    assert two['ledger']['polynomial']==dict(M=10,A=43)
    assert history['ledger']['polynomial']==dict(M=155,A=329)
    examples={name:dict(net=net,one_step_assignment=step_values(four,net)) for name,net in oracle.examples().items()}
    examples['A']['history_assignment']=history_values(history,examples['A']['net'])
    examples['A']['history_final_net']=oracle.normalize(examples['A']['net'])[-1]['net']
    after_B=oracle.annihilate(examples['B']['net'],[0,1])
    assert [2,3] not in oracle.active_pairs(after_B)
    examples['B']['second_principal_edge']=0
    return dict(status='PASS_INTERACTION_COMBINATOR_QUADRATIC_TOPOLOGY',
        source_file_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        oracle_file=ORACLE_FILE,oracle_source_sha256=ORACLE_SHA256,primary_source=oracle.REFERENCE,
        packets=dict(four_cell_quadratic=four,four_cell_cubic=cubic,two_cell_quadratic=two,fixed_two_step_quadratic=history),
        examples=examples,evidence=exhaustive_audit(),guards=guard_audit(),scope=SCOPE)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['evidence']['counts']);print(result['guards'])

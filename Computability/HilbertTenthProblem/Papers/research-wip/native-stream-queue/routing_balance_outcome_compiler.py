"""Paid history-free sink outcomes for explicitly periodic RLE routing.

Positive coordinates encode zero loads/counts by +1. Balanced candidate
odometers need not be exact; their sink outputs always are. This is not a
universal routing interface or a canonical-witness compiler.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random

from queue_causality_sentinel_fold import DAG, execute


def topology_of(topology, sinks):
    topology = tuple(tuple(row) for row in topology)
    n = len(topology)
    assert n >= 1 and type(sinks) is int and sinks >= 1
    assert all(row for row in topology)
    assert all(type(w) is int and 0 <= w < n+sinks for row in topology for w in row)
    return topology


def build(topology=((0, 1, 2), (0, 3)), sinks=2, *, mode='outcome'):
    topology = topology_of(topology, sinks)
    assert mode in ('outcome', 'canonical')
    n, m = len(topology), sum(map(len, topology))
    lengths = [[f'length_{v}_{j}' for j in range(len(row))]
               for v, row in enumerate(topology)]
    parameters = ([f'load_hat_{v}' for v in range(n)]
        + [name for row in lengths for name in row]
        + [f'sink_hat_{s}' for s in range(sinks)])
    if mode == 'outcome':
        auxiliaries = [f'{field}_{v}' for v in range(n)
                       for field in ('quotient_hat', 'position_hat', 'suffix')]
        auxiliaries += [f'select_hat_{v}_{j}' for v, row in enumerate(topology)
                        for j in range(len(row))]
    else:
        auxiliaries = [f'{field}_hat_{v}' for v in range(n)
                       for field in ('u', 'q', 'z', 'height')]
        auxiliaries += [f'{field}_hat_{v}_{j}' for v, row in enumerate(topology)
                        for j in range(len(row)) for field in ('b', 't', 'alpha', 'beta')]
    c = DAG(parameters+auxiliaries)
    residuals, labels = [], []
    def residual(label, value):
        labels.append(label)
        residuals.append(value)
    if mode == 'outcome':
        balances = [c.sub(1, f'load_hat_{v}') for v in range(n)]
        sink_rows = [c.sub(1, f'sink_hat_{s}') for s in range(sinks)]
        for v, row in enumerate(topology):
            qhat, phat, suffix = [f'{field}_{v}' for field in
                                  ('quotient_hat', 'position_hat', 'suffix')]
            state, selected_length = qhat, 0
            for j, destination in enumerate(row):
                bit = c.sub(f'select_hat_{v}_{j}', 1)
                length = lengths[v][j]
                selected_length = c.add(selected_length, c.mul(length, bit))
                if destination != v:
                    flow = c.sub(c.mul(length, state), c.mul(bit, suffix))
                    balances[v] = c.add(balances[v], flow)
                    if destination < n:
                        balances[destination] = c.sub(balances[destination], flow)
                    else:
                        s = destination-n
                        sink_rows[s] = c.add(sink_rows[s], flow)
                state = c.sub(state, bit)
            residual(f'selection_{v}', c.add(c.sub(state, qhat), 1))
            residual(f'position_{v}', c.sub(c.sub(c.add(phat, suffix), 1),
                                            selected_length))
        for v, value in enumerate(balances): residual(f'balance_{v}', value)
        for s, value in enumerate(sink_rows): residual(f'sink_{s}', value)
    else:
        # Literal report12 equations, with all natural coordinates shifted
        # by one; sink counts are query parameters in both compared modes.
        natural = {name: c.sub(name, 1) for name in auxiliaries}
        flow = [[0]*(n+sinks) for _ in range(n)]
        for v, row in enumerate(topology):
            u, q, z, height = [natural[f'{field}_hat_{v}']
                               for field in ('u', 'q', 'z', 'height')]
            previous = [0]*(n+sinks)
            selection = phase = height_sum = period = 0
            for j, destination in enumerate(row):
                length = lengths[v][j]
                b, t, alpha, beta = [natural[f'{field}_hat_{v}_{j}']
                                     for field in ('b', 't', 'alpha', 'beta')]
                period = c.add(period, length)
                selection = c.add(selection, b)
                phase = c.add(phase, c.add(c.mul(c.total(previous), b), t))
                for w in range(n+sinks):
                    flow[v][w] = c.add(flow[v][w], c.mul(previous[w], b))
                flow[v][destination] = c.add(flow[v][destination],
                                             c.add(t, c.mul(length, q)))
                if destination < n:
                    height_sum = c.add(height_sum,
                        c.mul(b, natural[f'height_hat_{destination}']))
                residual(f'lower_{v}_{j}', c.sub(c.sub(t, b), alpha))
                residual(f'upper_{v}_{j}', c.sub(c.add(t, beta), c.mul(length, b)))
                previous[destination] = c.add(previous[destination], length)
            residual(f'active_{v}', c.mul(z, c.sub(z, 1)))
            residual(f'selection_{v}', c.sub(selection, z))
            residual(f'quotient_{v}', c.mul(q, c.sub(1, z)))
            residual(f'odometer_{v}', c.sub(c.sub(u, c.mul(period, q)), phase))
            residual(f'height_{v}', c.sub(c.sub(height, z), height_sum))
        for v in range(n):
            residual(f'balance_{v}', c.sub(c.sub(natural[f'u_hat_{v}'],
                c.sub(f'load_hat_{v}', 1)), c.total([row[v] for row in flow])))
        for s in range(sinks):
            residual(f'sink_{s}', c.sub(c.sub(f'sink_hat_{s}', 1),
                                       c.total([row[n+s] for row in flow])))
    output = c.total([c.mul(r, r) for r in residuals])
    source = c.close(output)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    degrees = dict.fromkeys(parameters+auxiliaries, 1)
    deg = lambda v: degrees[v] if isinstance(v, str) else 0
    for name, op, a, b in source:
        degrees[name] = deg(a)+deg(b) if op == '*' else max(deg(a), deg(b))
    nonself = sum(w != v for v, row in enumerate(topology) for w in row)
    assert deg(output) <= 4
    if mode == 'outcome':
        assert len(auxiliaries) == 3*n+m
        assert len(residuals) == 3*n+sinks
        assert count['M'] <= m+2*nonself+3*n+sinks
        assert count['A'] <= 3*m+3*nonself+8*n+2*sinks-1
    else:
        assert len(auxiliaries) == 4*n+4*m
        assert len(residuals) == 6*n+2*m+sinks
    return dict(source=source, output=output, parameters=parameters,
        auxiliaries=auxiliaries, residuals=list(zip(labels, residuals)),
        topology=topology, sinks=sinks, mode=mode, degree_upper_bound=deg(output),
        operations=len(source), M=count['M'], A=count['A'],
        witnesses=len(auxiliaries), comparisons=len(residuals),
        vertices=n, blocks=m, nonself_blocks=nonself,
        positive_domain=True, exact_sink_outputs=True,
        exact_odometer=(mode == 'canonical'), canonical_witness=(mode == 'canonical'))


def evaluate(packet, values):
    env = execute(packet['source'], values)
    return env[packet['output']]


def oracle(packet, values):
    """Direct scalar equations, without executing any generated DAG rows."""
    topology, sinks = packet['topology'], packet['sinks']
    n = len(topology)
    lengths = [[values[f'length_{v}_{j}'] for j in range(len(row))]
               for v, row in enumerate(topology)]
    if packet['mode'] == 'outcome':
        balances = [1-values[f'load_hat_{v}'] for v in range(n)]
        ys = [1-values[f'sink_hat_{s}'] for s in range(sinks)]
        residuals = []
        for v, row in enumerate(topology):
            b = [values[f'select_hat_{v}_{j}']-1 for j in range(len(row))]
            Q, P, S = [values[f'{field}_{v}'] for field in
                       ('quotient_hat', 'position_hat', 'suffix')]
            residuals += [1-sum(b), P+S-1-sum(a*d for a, d in zip(lengths[v], b))]
            for j, w in enumerate(row):
                if w == v: continue
                e = lengths[v][j]*(Q-sum(b[:j]))-b[j]*S
                balances[v] += e
                if w < n: balances[w] -= e
                else: ys[w-n] += e
        return residuals+balances+ys
    flow = [[0]*(n+sinks) for _ in range(n)]
    residuals = []
    val = lambda key: values[key]-1
    for v, row in enumerate(topology):
        u, q, z, h = [val(f'{field}_hat_{v}') for field in ('u','q','z','height')]
        b = [val(f'b_hat_{v}_{j}') for j in range(len(row))]
        t = [val(f't_hat_{v}_{j}') for j in range(len(row))]
        a = [val(f'alpha_hat_{v}_{j}') for j in range(len(row))]
        be = [val(f'beta_hat_{v}_{j}') for j in range(len(row))]
        for j in range(len(row)):
            residuals += [t[j]-b[j]-a[j], t[j]+be[j]-lengths[v][j]*b[j]]
        residuals += [z*(z-1), sum(b)-z, q*(1-z),
            u-sum(lengths[v])*q-sum(sum(lengths[v][:j])*b[j]+t[j]
                                       for j in range(len(row))),
            h-z-sum(b[j]*val(f'height_hat_{w}') for j,w in enumerate(row) if w<n)]
        for j, w in enumerate(row):
            flow[v][w] += lengths[v][j]*(q+sum(b[j+1:]))+t[j]
    residuals += [val(f'u_hat_{v}')-val(f'load_hat_{v}')
                  -sum(row[v] for row in flow) for v in range(n)]
    residuals += [val(f'sink_hat_{s}')-sum(row[n+s] for row in flow)
                  for s in range(sinks)]
    return residuals


def literal_periods(topology, lengths):
    assert len(topology) == len(lengths)
    assert all(len(a) == len(b) for a,b in zip(topology,lengths))
    assert all(type(x) is int and x >= 1 for row in lengths for x in row)
    return [tuple(w for w, length in zip(row, sizes) for _ in range(length))
            for row, sizes in zip(topology, lengths)]


def simulate(topology, lengths, loads, sinks):
    periods = literal_periods(topology, lengths)
    n = len(topology)
    active, outputs, u = list(loads), [0]*sinks, [0]*n
    assert len(loads) == n and all(type(x) is int and x >= 0 for x in loads)
    seen = set()
    while any(active):
        state = tuple(active), tuple(u[v] % len(periods[v]) for v in range(n))
        if state in seen:
            return dict(terminates=False, odometer=u, outputs=outputs, states=len(seen))
        seen.add(state)
        v = next(v for v in range(n) if active[v])
        w = periods[v][u[v] % len(periods[v])]
        u[v] += 1
        active[v] -= 1
        if w < n: active[w] += 1
        else: outputs[w-n] += 1
    return dict(terminates=True, odometer=u, outputs=outputs, states=len(seen))


def prefix_counts(topology, lengths, u, sinks):
    periods = literal_periods(topology, lengths)
    return [[(u[v]//len(period))*period.count(w)+period[:u[v]%len(period)].count(w)
             for w in range(len(topology)+sinks)] for v,period in enumerate(periods)]


def parameter_values(packet, lengths, loads, outputs):
    return ({f'load_hat_{v}':x+1 for v,x in enumerate(loads)}
        | {f'sink_hat_{s}':y+1 for s,y in enumerate(outputs)}
        | {f'length_{v}_{j}':a for v,row in enumerate(lengths) for j,a in enumerate(row)})


def witness(packet, lengths, u):
    n = len(packet['topology'])
    values = {}
    successors = {}
    for v, sizes in enumerate(lengths):
        D = sum(sizes)
        if packet['mode'] == 'outcome':
            q, r = divmod(u[v], D)
            j = 0
            while r >= sizes[j]:
                r -= sizes[j]
                j += 1
            values.update({f'quotient_hat_{v}':q+1, f'position_hat_{v}':r+1,
                           f'suffix_{v}':sizes[j]-r})
            values.update({f'select_hat_{v}_{i}':1+int(i==j) for i in range(len(sizes))})
        else:
            values[f'u_hat_{v}'] = u[v]+1
            values[f'z_hat_{v}'] = int(u[v]>0)+1
            q, rem = divmod(u[v]-1, D) if u[v] else (0, -1)
            rem += 1
            j = 0
            while rem > sizes[j]: rem, j = rem-sizes[j], j+1
            values[f'q_hat_{v}'] = q+1
            for i,length in enumerate(sizes):
                b = int(u[v]>0 and i==j)
                t = rem if b else 0
                values.update({f'b_hat_{v}_{i}':b+1, f't_hat_{v}_{i}':t+1,
                    f'alpha_hat_{v}_{i}':t-b+1, f'beta_hat_{v}_{i}':length*b-t+1})
            if u[v]: successors[v] = packet['topology'][v][j]
    if packet['mode'] == 'canonical':
        heights = {}
        def height(v, path=()):
            if v >= n or v not in successors: return 0
            if v in path: raise ValueError('cyclic last exits')
            if v not in heights: heights[v] = 1+height(successors[v], path+(v,))
            return heights[v]
        for v in range(n): values[f'height_hat_{v}'] = height(v)+1
    assert set(values) == set(packet['auxiliaries'])
    assert all(x >= 1 for x in values.values())
    return values


def ledger(packet):
    keys = ('mode','vertices','blocks','nonself_blocks','sinks','operations','M','A',
            'witnesses','comparisons','degree_upper_bound')
    return {key:packet[key] for key in keys} | dict(
        source_sha256=hashlib.sha256(repr(packet['source']).encode()).hexdigest())


def algebra_audit():
    rng = random.Random(121903)
    checked = signed = 0
    ledgers = []
    for case in range(32):
        n, s = rng.randrange(1,5), rng.randrange(1,4)
        topology = tuple(tuple(rng.randrange(n+s) for _ in range(rng.randrange(1,5)))
                         for _ in range(n))
        for mode in ('outcome','canonical'):
            packet = build(topology,s,mode=mode)
            ledgers.append(ledger(packet))
            for trial in range(16):
                draw = lambda: rng.randrange(-4,5) if trial % 2 else rng.randrange(1,6)
                values = {name:draw() for name in packet['parameters']+packet['auxiliaries']}
                direct = oracle(packet,values)
                env = execute(packet['source'],values)
                actual = [env[r] if isinstance(r,str) else r for _,r in packet['residuals']]
                assert actual == direct
                assert env[packet['output']] == sum(x*x for x in direct)
                checked += 1
                signed += trial % 2
    return dict(whole_source_oracle_identities=checked, signed=signed, ledgers=ledgers)


def semantic_audit():
    candidates = roots = fake = terminations = total_steps = 0
    canonical_roots = wrong_outputs = 0
    for flat in product(range(4),repeat=4):
        topology = (flat[:2],flat[2:])
        lengths = ((1,1),(1,1))
        packet, canonical = build(topology,2),build(topology,2,mode='canonical')
        for loads in product(range(2),repeat=2):
            run = simulate(topology,lengths,loads,2)
            terminations += run['terminates']
            total_steps += sum(run['odometer'])
            if run['terminates']:
                values = parameter_values(canonical,lengths,loads,run['outputs'])
                values.update(witness(canonical,lengths,run['odometer']))
                assert evaluate(canonical,values) == 0
                new_values = parameter_values(packet,lengths,loads,run['outputs'])
                new_values.update(witness(packet,lengths,run['odometer']))
                assert evaluate(packet,new_values) == 0
                canonical_roots += 1
            for u in product(range(7),repeat=2):
                counts = prefix_counts(topology,lengths,u,2)
                balanced = all(u[v]==loads[v]+sum(row[v] for row in counts) for v in range(2))
                outputs = [sum(row[2+s] for row in counts) for s in range(2)]
                values = parameter_values(packet,lengths,loads,outputs)
                values.update(witness(packet,lengths,u))
                assert (evaluate(packet,values)==0) == balanced
                if balanced:
                    assert run['terminates'] and outputs == run['outputs']
                    roots += 1
                    fake += list(u) != run['odometer']
                    for s in range(2):
                        bad = dict(values)
                        bad[f'sink_hat_{s}'] += 1
                        assert evaluate(packet,bad) > 0
                        wrong_outputs += 1
                candidates += 1
    return dict(topologies=256, initial_cases=1024, balanced_candidates=candidates,
        terminating_cases=terminations, simulated_firings=total_steps,
        accepted_balanced_candidates=roots, inexact_odometers_accepted=fake,
        canonical_execution_roots=canonical_roots, wrong_sink_queries_rejected=wrong_outputs)


def variable_length_audit():
    rng = random.Random(126887)
    contexts = terminating = firings = 0
    for _ in range(192):
        n, sinks = rng.randrange(1,4), rng.randrange(1,4)
        topology = tuple(tuple(rng.randrange(n+sinks) for _ in range(rng.randrange(1,5)))
                         for _ in range(n))
        lengths = tuple(tuple(rng.randrange(1,5) for _ in row) for row in topology)
        loads = tuple(rng.randrange(4) for _ in range(n))
        run = simulate(topology,lengths,loads,sinks)
        contexts += 1
        firings += sum(run['odometer'])
        if not run['terminates']: continue
        terminating += 1
        for mode in ('outcome','canonical'):
            packet = build(topology,sinks,mode=mode)
            values = parameter_values(packet,lengths,loads,run['outputs'])
            values.update(witness(packet,lengths,run['odometer']))
            assert evaluate(packet,values) == 0
        counts = prefix_counts(topology,lengths,run['odometer'],sinks)
        assert all(run['odometer'][v]==loads[v]+sum(row[v] for row in counts)
                   for v in range(n))
        assert run['outputs']==[sum(row[n+s] for row in counts) for s in range(sinks)]
    return dict(contexts=contexts,terminating=terminating,simulated_firings=firings)


def invalid_audit():
    checked = zeros = 0
    packet = build(((0,1),),1)
    lengths = ((2,1),)
    for loads, outputs in product(range(3),repeat=2):
      for selectors in product(range(1,4),repeat=2):
       for q,p,s in product(range(1,4),repeat=3):
        values = parameter_values(packet,lengths,(loads,),(outputs,))
        values.update(dict(quotient_hat_0=q,position_hat_0=p,suffix_0=s,
                           select_hat_0_0=selectors[0],select_hat_0_1=selectors[1]))
        if evaluate(packet,values)==0:
            assert sum(x-1 for x in selectors)==1
            run=simulate(packet['topology'],lengths,(loads,),1)
            assert run['terminates'] and run['outputs']==[outputs]
            zeros += 1
        checked += 1
    # Same accepted sink query, two different candidate odometers.
    packet=build(((0,1),),1)
    args=parameter_values(packet,((1,1),),(1,),(1,))
    for u in (2,3): assert evaluate(packet,args|witness(packet,((1,1),),(u,)))==0
    return dict(full_positive_assignments=checked,zeros=zeros,
        circulation_fixture=dict(topology=[[0,1]],lengths=[[1,1]],load=1,
                                 sink=1,actual_odometer=2,accepted_odometer=3))


def verify():
    default, parent = build(),build(mode='canonical')
    return dict(status='PASS_ROUTING_BALANCE_OUTCOME_COMPILER',
        default=ledger(default), canonical_comparison=ledger(parent),
        default_source=default, algebra=algebra_audit(), semantics=semantic_audit(),
        variable_lengths=variable_length_audit(),invalid=invalid_audit(),
        scope='Exact termination and sink-output projection for fixed explicit RLE topology; '
              'positive load/output hats and positive block-length parameters; '
              'no exact odometer or unique witness claim, no universal routing bound.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=verify()
    normalized=json.loads(json.dumps(result))
    path=Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(normalized,indent=2)+'\n')
    else: assert normalized==json.loads(path.read_text()),'receipt mismatch'
    print(result['status'])
    print(result['default'])
    print(result['canonical_comparison'])
    print(result['semantics'])

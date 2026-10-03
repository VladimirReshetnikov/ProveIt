"""Same natural zeros with fewer rows in report11's bounded reaction quartic.

No straight-line operation bound or fixed-arity universal improvement is claimed.
The delivered compiler is imported read-only under its complete SHA-256 guard.
"""
from collections import Counter
from copy import deepcopy
from functools import lru_cache
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCE = ROOT / 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/11-reaction-fallback-reaction_compiler.py'
EXPECTED_SOURCE = 'f9c0e8730fd9f0a712c476e18c8d70bb9758e0d4d3fc9b26e1afdcfc8d42cbc3'
assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED_SOURCE, 'complete report11 source changed'
spec = importlib.util.spec_from_file_location('_reaction_projection_frozen_report11', SOURCE)
report = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = report
spec.loader.exec_module(report)
P = report.Poly
MACHINES = ('universal', 'doubling', 'halt', 'increment', 'false_zero')


def source_guard():
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED_SOURCE


def machine(key):
    assert type(key) is str and key in MACHINES
    I = report.Instruction
    if key == 'universal': return report.universal_machine()
    if key == 'doubling': return report.doubling_machine()
    if key == 'halt': return report.Machine(1, {'H': I('halt')}, 'H')
    if key == 'increment': return report.Machine(1, {'0': I('inc', 0, 'H'), 'H': I('halt')}, '0')
    return report.Machine(1, {'0': I('dec', 0, '1', 'H'), '1': I('inc', 0, '1'), 'H': I('halt')}, '0')


def network(key, low_index=None):
    net = report.compile_machine(machine(key))
    if low_index is None: low_index = len(net.reactions) - 1
    assert type(low_index) is int and 0 <= low_index < len(net.reactions)
    rows = list(net.reactions)
    low = rows.pop()
    assert low.priority == 0 and all(r.priority == 1 for r in rows)
    rows.insert(low_index, low)
    net = report.Network(net.machine, net.species, tuple(rows))
    assert all(len(set(r.reactants)) == 2 for r in rows)
    return net


def rows(cert):
    return [[name, poly.records()] for name, poly in cert.residuals]


def freeze_certificate(cert):
    return dict(witnesses=list(cert.witnesses), residuals=rows(cert))


def thaw_certificate(data):
    return report.Certificate(list(data['witnesses']), [(name, P({tuple(v['variables']): v['coefficient'] for v in terms})) for name, terms in data['residuals']])


def _compress(old, *, linear_zero=False):
    """Internal transformation; public build/checked guard full parent and metadata."""
    assert type(linear_zero) is bool
    keep = []; guards = {}
    for name, poly in old.residuals:
        parts = name.split(':')
        if parts[1] == 'zero':
            if parts[-1] in ('0', '1'): continue
            if parts[-1] == '2' and linear_zero:
                _, _, t, s, _ = parts
                poly = P.var(f't_x_{t}_{s}') - P.var(f't_b_{t}_{s}') + P.var(f't_z_{t}_{s}') - 1
        if parts[1] == 'selector': continue
        if parts[1] in ('eligible', 'priority', 'idle'):
            label = f't:permitted:{parts[2]}'
            guards[label] = guards.get(label, P()) + poly
        else: keep.append((name, poly))
    keep.extend(guards.items())
    assert max((p.degree() for _, p in keep), default=0) <= 2
    return report.Certificate(list(old.witnesses), keep)


def config(machine_key, horizon, low_index, linear_zero):
    assert type(horizon) is int and horizon >= 0
    assert type(linear_zero) is bool
    net = network(machine_key, low_index)
    low = next(j for j, r in enumerate(net.reactions) if r.priority == 0)
    return machine_key, horizon, low, linear_zero


@lru_cache(None)
def _canonical(machine_key, horizon, low_index, linear_zero):
    source_guard()
    net = network(machine_key, low_index)
    old = report.trace_certificate(net, {s: P.var('in_' + s) for s in net.species}, horizon, P.var('eta'))
    new = _compress(old, linear_zero=linear_zero)
    by_name = dict(new.residuals)
    for t in range(horizon):
        e = [P.var(f't_e_{t}_{j}') for j in range(len(net.reactions))]
        sel = [P.var(f't_s_{t}_{j}') for j in range(len(net.reactions)+1)]
        direct = sum((sel[j]*(1-e[j]) for j in range(len(e))), P())
        direct += sel[low_index]*sum((e[j] for j in range(len(e)) if j != low_index), P())
        direct += sel[-1]*sum(e, P())
        assert by_name[f't:permitted:{t}'].terms == direct.terms
    d, r = len(net.species), len(net.reactions)
    assert len(old.witnesses) == len(new.witnesses) == (3*d + 2*r + 1)*horizon + d
    assert len(old.residuals) == (5*d + 5*r + 1)*horizon + d + 1
    assert len(new.residuals) == (3*d + r + 2)*horizon + d + 1
    parameters = ['in_' + s for s in net.species] + ['eta']
    assert len(set(parameters + old.witnesses)) == len(parameters) + len(old.witnesses)
    all_names = set(parameters + old.witnesses)
    assert all(v in all_names for cert in (old, new) for _, p in cert.residuals for monomial in p.terms for v in monomial)
    return dict(schema='reaction_priority_residual_projection-v1', machine=machine_key, horizon=horizon,
                low_index=low_index, linear_zero=linear_zero, source_sha256=EXPECTED_SOURCE,
                network=report.network_json(net), parameters=parameters,
                initial_interface='Every initial species count is a free natural parameter; eta is the natural final halt-species count.',
                witness_domain='N including zero', parent=freeze_certificate(old), projected=freeze_certificate(new),
                ledger=dict(species=d, reactions=r, witnesses=len(new.witnesses), parent_residuals=len(old.residuals),
                            projected_residuals=len(new.residuals), removed_residuals=(2*d+4*r-1)*horizon,
                            maximum_residual_degree=max(p.degree() for _, p in new.residuals), polynomial_degree_bound=4 if horizon else 2),
                same_natural_zero_set=True, same_supplied_coordinates=True, integer_zero_equivalence_claimed=False,
                off_zero_polynomial_identity=False, straight_line_operation_bound=None,
                fixed_arity_universal_improvement=False,
                scope='Fixed finite horizon and compiled network; same complete natural zero set, including arbitrary initial markings. Simulation uniqueness applies only to legal invariant markings.')


def build(*, machine_key='universal', horizon=1, low_index=None, linear_zero=False):
    source_guard()
    return deepcopy(_canonical(*config(machine_key, horizon, low_index, linear_zero)))


def _same_typed(a, b):
    if type(a) is not type(b): return False
    if type(a) is dict:
        return (len(a) == len(b) and all(type(k) is str for k in a)
                and all(k in b and _same_typed(v, b[k]) for k, v in a.items()))
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(_same_typed(x, y) for x, y in zip(a, b))
    return a == b


def checked(packet):
    source_guard()
    assert type(packet) is dict
    key = config(packet.get('machine'), packet.get('horizon'), packet.get('low_index'), packet.get('linear_zero'))
    assert _same_typed(packet, _canonical(*key)), 'complete type-sensitive canonical source and metadata required'


def certificate(packet, *, parent=False):
    assert type(parent) is bool
    checked(packet)
    return thaw_certificate(packet['parent' if parent else 'projected'])


def ledger(packet=None):
    if packet is None: packet = build()
    checked(packet)
    return deepcopy(packet['ledger'])


def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def local_audit():
    counts = Counter()
    for x, z, b in itertools.product(range(16), range(7), range(19)):
        old = z*(z-1) == 0 and x*z == 0 and x-(1-z)*(b+1) == 0 and z*b == 0
        quadratic = x-(1-z)*(b+1) == 0 and z*b == 0
        linear = x-b+z-1 == 0 and z*b == 0
        assert old == quadratic == linear
        counts['zero_gadget_assignments'] += 1
    for r in range(1, 9):
        for low in range(r):
            for enabled in itertools.product(range(2), repeat=r):
                for selected in range(r+1):
                    exact = (selected == r and not any(enabled)) or (selected < r and enabled[selected] and (selected != low or not any(enabled[j] for j in range(r) if j != low)))
                    penalty = (1-enabled[selected] if selected < r else 0) + (sum(enabled[j] for j in range(r) if j != low) if selected == low else 0) + (sum(enabled) if selected == r else 0)
                    assert bool(exact) == (penalty == 0)
                    counts['all_enabled_selector_priority_cases'] += 1
    # Domain and dependency limits: the reduced gadget has an extra signed zero.
    assert (-1) - (1-2)*(0+1) == 0 and 2*0 == 0 and 2*(2-1) != 0
    assert 1*(1-2) < 0  # guard summands need the retained enabling equations
    return dict(counts)


def shape_audit():
    out = []
    for key in MACHINES:
        r = len(network(key).reactions)
        for low in sorted({0, r//2, r-1}):
            for t, linear in itertools.product((0, 1, 2), (False, True)):
                packet = build(machine_key=key, horizon=t, low_index=low, linear_zero=linear)
                checked(packet)
                out.append(dict(machine=key, horizon=t, low_index=low, linear_zero=linear,
                                **packet['ledger'], parent_source_sha256=digest(packet['parent']),
                                projected_source_sha256=digest(packet['projected']), full_packet_sha256=digest(packet)))
    return out


def trace_audit():
    counts = Counter()
    for key in MACHINES:
        r = len(network(key).reactions)
        for low in sorted({0, r-1}):
            net = network(key, low)
            for t in (0, 1, 3, 8):
                original = certificate(build(machine_key=key, horizon=t, low_index=low), parent=True)
                variants = [certificate(build(machine_key=key, horizon=t, low_index=low, linear_zero=v)) for v in (False, True)]
                for seed in range(6):
                    cs = [(seed+j) % 3 for j in range(net.machine.registers)]
                    initial = net.initial(cs, seed % 3)
                    witness = report.trace_assignment(net, initial, t)
                    assignment = {**{'in_'+s:n for s,n in initial.items()}, **witness, 'eta': witness[f't_x_{t}_Q_{net.machine.halt}']}
                    assert original.value(assignment) == 0
                    assert all(c.value(assignment) == 0 for c in variants)
                    counts['canonical_traces_two_variants'] += 1
                    if seed == 0 and t == 1:
                        for name in original.witnesses:
                            for change in (-1, 1, 2):
                                altered = assignment.copy(); altered[name] += change
                                if altered[name] < 0: continue
                                truth = original.value(altered) == 0
                                assert not truth and all((c.value(altered) == 0) == truth for c in variants)
                                counts['single_coordinate_adversaries'] += 1
                    wrong = assignment.copy(); wrong['eta'] += 1
                    assert original.value(wrong) > 0 and all(c.value(wrong) > 0 for c in variants)
                    counts['wrong_endpoints'] += 1
    net = network('false_zero', 0)
    names = {r.name:j for j,r in enumerate(net.reactions)}
    initial = net.initial([1], 0)
    witness = report.trace_assignment(net, initial, 3, forced=[names['enter_0'], names['fallback'], names['zero_0']])
    assignment = {**{'in_'+s:n for s,n in initial.items()}, **witness, 'eta':1}
    for linear in (False, True):
        packet = build(machine_key='false_zero', horizon=3, low_index=0, linear_zero=linear)
        assert certificate(packet, parent=True).value(assignment) == certificate(packet).value(assignment) == 1
        counts['spurious_zero_branches_rejected'] += 1
    return dict(counts)


def arbitrary_marking_audit():
    counts = Counter(); rng = random.Random(2601002)
    for key in MACHINES:
        r = len(network(key).reactions)
        for low in sorted({0, r//2, r-1}):
            net = network(key, low)
            old = certificate(build(machine_key=key, low_index=low), parent=True)
            variants = [certificate(build(machine_key=key, low_index=low, linear_zero=v)) for v in (False, True)]
            for _ in range(24):
                x = {s: rng.randrange(4) for s in net.species}
                for chosen in range(r+1):
                    y = {s: max(0, x[s]+(net.reactions[chosen].delta(s) if chosen < r else 0)) for s in net.species}
                    a = {**{'in_'+s:n for s,n in x.items()}, 'eta': y[f'Q_{net.machine.halt}']}
                    for s in net.species:
                        a['t_x_0_'+s] = x[s]; a['t_x_1_'+s] = y[s]
                        a['t_z_0_'+s] = int(x[s] == 0); a['t_b_0_'+s] = max(x[s]-1, 0)
                    for j, rr in enumerate(net.reactions): a['t_e_0_'+str(j)] = int(rr.enabled(x))
                    for j in range(r+1): a['t_s_0_'+str(j)] = int(j == chosen)
                    truth = old.value(a) == 0
                    legal = chosen in net.choices(x) if chosen < r else not net.choices(x)
                    assert truth == legal and all((c.value(a) == 0) == truth for c in variants)
                    counts['all_rule_idle_choices'] += 1
                    counts['accepted_choices' if truth else 'rejected_choices'] += 1
                    for kind in ('z', 'b', 'e', 's'):
                        altered = a.copy()
                        name = rng.choice([v for v in old.witnesses if v.startswith('t_'+kind+'_')])
                        altered[name] += rng.choice((1, 2, 3))
                        altered_truth = old.value(altered) == 0
                        assert all((c.value(altered) == 0) == altered_truth for c in variants)
                        counts['corrupted_helpers'] += 1
    return dict(counts)


def guard_audit():
    packet = build(); counts = Counter()
    altered = []
    for key, value in [('horizon', True), ('linear_zero', 1), ('low_index', False), ('same_natural_zero_set', False), ('source_sha256', 'bad'), ('scope', 'bad')]:
        p = deepcopy(packet); p[key] = value; altered.append(p)
    p = deepcopy(packet); p['parent']['residuals'][0][1][0]['coefficient'] += 1; altered.append(p)
    p = deepcopy(packet); p['projected']['residuals'][0][1][0]['coefficient'] += 1; altered.append(p)
    p = deepcopy(packet); p['network']['reactions'][0]['priority'] = 0; altered.append(p)
    p = deepcopy(packet); p['parameters'].reverse(); altered.append(p)
    p = deepcopy(packet); p['projected']['witnesses'].pop(); altered.append(p)
    p = deepcopy(packet); p['ledger']['projected_residuals'] -= 1; altered.append(p)
    p = deepcopy(packet); p['extra_unchecked'] = True; altered.append(p)
    for value in (1.0, True):
        p = deepcopy(packet)
        term = next(v for _, terms in p['projected']['residuals'] for v in terms if v['coefficient'] == 1)
        term['coefficient'] = value; altered.append(p)
    p = deepcopy(packet); p['ledger']['species'] = float(p['ledger']['species']); altered.append(p)
    p = deepcopy(packet); p['parent']['witnesses'] = tuple(p['parent']['witnesses']); altered.append(p)
    # Equal Python numeric values must not permit float arithmetic at huge endpoints.
    p = build(machine_key='halt', horizon=0)
    endpoint = next(terms for name, terms in p['projected']['residuals'] if name == 't:endpoint')
    for term in endpoint: term['coefficient'] = float(term['coefficient'])
    huge = 2**100
    assert float(huge+1) - float(huge) == 0.0 and (huge+1)-huge == 1
    altered.append(p)
    for p in altered:
        try: checked(p)
        except (AssertionError, KeyError, TypeError, ValueError): counts['bad_packets_rejected'] += 1
        else: raise AssertionError('mutated packet accepted')
    for kwargs in ({'horizon':-1}, {'horizon':True}, {'linear_zero':1}, {'low_index':True}, {'machine_key':'unknown'}):
        try: build(**kwargs)
        except (AssertionError, KeyError, TypeError, ValueError): counts['bad_callers_rejected'] += 1
        else: raise AssertionError('bad caller accepted')
    old = certificate(packet, parent=True); new = certificate(packet)
    a = dict.fromkeys(packet['parameters']+old.witnesses, 0)
    a['t_z_0_'+packet['network']['species'][0]] = 2
    assert old.value(a) != new.value(a)
    counts['off_zero_inequality_checked'] += 1
    # Full natural source fixture: unsquaring the conditionally nonnegative guard is unsound.
    halt_packet = build(machine_key='halt', horizon=1)
    halt_net = network('halt')
    initial = dict.fromkeys(halt_net.species, 1)
    witness = report.trace_assignment(halt_net, initial, 1)
    assignment = {**{'in_'+s:n for s,n in initial.items()}, **witness, 'eta':witness['t_x_1_Q_H']}
    halt_cert = certificate(halt_packet)
    assert halt_cert.value(assignment) == 0
    assignment['t_e_0_0'] = 2
    violations = halt_cert.violations(assignment)
    assert violations == {'t:enabled:0:0':1, 't:permitted:0':-1}
    assert halt_cert.value(assignment) == 2
    unsafe = sum(v*v for name,v in violations.items() if name != 't:permitted:0') + violations['t:permitted:0']
    assert unsafe == 0
    counts['full_natural_unsquared_guard_false_zero'] += 1
    return dict(counts)


def run():
    result = dict(status='PASS', assurance='Proof in companion note plus finite exact source checks; not a formal proof.',
                  source_hashes={str(SOURCE.relative_to(ROOT)):EXPECTED_SOURCE,
                                 Path(__file__).name:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
                  local=local_audit(), shapes=shape_audit(), traces=trace_audit(),
                  arbitrary_markings=arbitrary_marking_audit(), guards=guard_audit(),
                  scope='Natural zero equivalence, bounded horizon, residual ledger only; no new universal operation count.')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run()
    if args.output: args.output.write_text(json.dumps(result, indent=2)+'\n')
    summary = {k:v for k,v in result.items() if k != 'shapes'}
    summary['shape_count'] = len(result['shapes'])
    print(json.dumps(summary, indent=2))

#!/usr/bin/env python3
"""Certificate, edge-case, corruption, and actual CA-microstep replay tests."""
from pathlib import Path
from fractions import Fraction
from itertools import product
import argparse
import copy
import hashlib
import importlib.util
import json
import random
import sys
import time
from types import SimpleNamespace

from certificate import (Machine, Instruction, export_certificate, make_witness,
                         polynomial_value, expand_polynomial)
from checker import check

HERE = Path(__file__).resolve().parent

def rejected(f):
    try: f()
    except (ValueError, AssertionError, KeyError, TypeError): return True
    raise AssertionError('expected rejection')

def cofactor(N):
    for p in (2, 3):
        while N % p == 0: N //= p
    return N

def load_generator(path):
    name = 'audited_three_mass_generator'
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

def test_clock_scale(gen, machines, radius_one_path):
    """Scale only physical time; compare committed observer at every new tick."""
    spec = importlib.util.spec_from_file_location('clock_scale_radius_one', radius_one_path)
    radius = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(radius)
    def require(ok, message):
        if not ok: raise AssertionError(message)
    def value_error(f):
        try: f()
        except ValueError: return
        raise AssertionError('expected explicit ValueError')
    # Scale 4 denotes the chosen four-phase lift, even when default r is smaller.
    for speed in (1, 3):
        toy = SimpleNamespace(names=('moving',), velocity=[speed], single={0:0}, pairs={})
        default_lift = radius.RadiusOneCA(toy)
        four_lift = radius.RadiusOneCA(toy, r=4)
        require(default_lift.r == speed and four_lift.r == 4, 'incorrect lift choice')
        conf = four_lift.embed(((0, 0),))
        for _ in range(4): conf = four_lift.step(conf)
        require(four_lift.project(conf) == ((speed, 0),), 'four-phase block mismatch')
    checked, new_ticks = [], 0
    for label, machine, q0, horizon in machines:
        ca = gen.ThreeMassCA(machine.states, machine.halt,
                            [gen.Instruction(**i.__dict__) for i in machine.instructions])
        slow = radius.RadiusOneCA(ca, r=4)
        for N in ((1, 5) if label == 'arithmetic-chain' else (1, 2, 3, 5)):
            args = (machine, q0, horizon, {'mode': 'fixed_raw', 'N': N},
                    {'mode': 'free'}, {'mode': 'free'})
            native = export_certificate(*args)
            require(native == export_certificate(*args, clock_scale=1), 'default changed')
            scaled = export_certificate(*args, clock_scale=4)
            wn, ws = make_witness(native), make_witness(scaled)
            rn, rs = check(native, wn), check(scaled, ws)
            require(rs['physical_time'] == 4*rn['physical_time'], 'wrong scaled clock')
            for field in native:
                if field not in ('physical_time', 'squares'):
                    require(native[field] == scaled[field], 'non-clock field changed: '+field)
            require(scaled['physical_time'] == {k:4*v for k,v in native['physical_time'].items()},
                    'physical-time form not scaled')
            for n, s in zip(native['squares'], scaled['squares']):
                if n['label'] != 'terminal:physical-time':
                    require(n == s, 'non-clock square changed')
            require({k:v for k,v in wn.items() if k != 'physical_time'} ==
                    {k:v for k,v in ws.items() if k != 'physical_time'}, 'source witness changed')
            conf, ready = slow.embed(ca.initial(q0, N)), []
            require(not slow.committed_halt(conf, ca), 'premature initial halt')
            for tick in range(1, rs['physical_time']+1):
                conf = slow.step(conf)
                require(slow.committed_halt(conf, ca) == (tick == rs['physical_time']),
                        'committed observer clock mismatch')
                if tick % 4 == 0:
                    native_conf = slow.project(conf)
                    section = ca.ready(native_conf)
                    if section is not None: ready.append((tick, *section))
            expected = [(row['microtime'], row['state'], row['N']) for row in rs['source_trace'][1:]]
            require(ready == expected, 'source boundaries disagree with radius-one replay')
            require(conf == slow.embed(ca.initial(machine.halt, rs['final_N'])), 'wrong final state')
            new_ticks += rs['physical_time']
            checked.append({'machine': label, 'N': N, 'native_time': rn['physical_time'],
                            'radius_one_time': rs['physical_time']})
    machine = machines[0][1]
    q0, horizon = machines[0][2:]
    fibers = [({'mode':'fixed_raw', 'N':5}, {}),
              ({'mode':'free_raw'}, {'raw_input_minus_one':4}),
              ({'mode':'bounded_counters', 'A':1, 'B':1}, {'input_a':1, 'input_b':1}),
              ({'mode':'bounded_counters', 'A':1, 'B':1, 'a':1, 'b':0}, {})]
    mode_cases = 0
    for inp, free in fibers:
        baseline = export_certificate(machine, q0, horizon, inp, {'mode':'free'}, {'mode':'free'})
        receipt = check(baseline, make_witness(baseline, free))
        for clock in (1, 4):
            for output in (None, {'mode':'free'}, {'mode':'fixed', 'value':receipt['final_N']}):
                for endpoint in (None, {'mode':'free'},
                                 {'mode':'fixed', 'value':clock*receipt['physical_time']}):
                    c = export_certificate(machine, q0, horizon, inp, output, endpoint, clock)
                    w = make_witness(c, free)
                    require(check(c, w)['physical_time'] == clock*receipt['physical_time'],
                            'mode-specific clock mismatch')
                    c['expanded_polynomial'] = expand_polynomial(c)
                    check(c, w)
                    mode_cases += 1
    args = (machine, q0, horizon, {'mode':'fixed_raw', 'N':1}, {'mode':'free'}, {'mode':'free'})
    good = export_certificate(*args, clock_scale=4)
    witness = make_witness(good)
    bad_scales = (0, 2, 3, 5, -1, True, False, 1.0, 4.0, '4', None, [], {})
    for bad in bad_scales:
        value_error(lambda: export_certificate(*args, clock_scale=bad))
        corrupt = copy.deepcopy(good); corrupt['clock_scale'] = bad
        value_error(lambda: make_witness(corrupt))
        value_error(lambda: check(corrupt, witness))
    corrupt = copy.deepcopy(good); del corrupt['clock_scale']
    value_error(lambda: check(corrupt, witness))
    corrupt = copy.deepcopy(good); corrupt['clock_scale'] = 1
    value_error(lambda: check(corrupt, witness))
    empty = Machine(('s', 'halt'), 'halt', ())
    for clock in (1, 4):
        c = export_certificate(empty, 'halt', 0, {'mode':'fixed_raw', 'N':5},
                               {'mode':'free'}, {'mode':'free'}, clock)
        require(check(c, make_witness(c))['physical_time'] == 0, 'h=0 time changed')
    return {'status':'passed', 'mode_cases':mode_cases, 'invalid_scales_rejected':len(bad_scales),
            'explicit_r4_low_speed_cases':2,
            'radius_one_runs':len(checked), 'radius_one_microsteps':new_ticks, 'cases':checked}


def run(generator_path, output_dir=None, radius_one_path=None):
    started = time.time()
    output_dir = HERE if output_dir is None else Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if radius_one_path is None:
        radius_one_path = HERE/'radius_one.py'
    gen = load_generator(generator_path)
    checks, lattice, rejects = [], [], 0
    one_inc = Machine(('s', 'halt'), 'halt', (Instruction('s', 'halt', 'inc', 0),))
    # Exhaustive natural search on one-branch, one-step instances, not just witness construction.
    exhaustive = []
    for N in range(1, 7):
        c = export_certificate(one_inc, 's', 1, {'mode': 'fixed_raw', 'N': N})
        zeros = []
        for e, u in product(range(4), range(9)):
            w = {'e_0_0': e, 'u_0_0': u}
            if polynomial_value(c, w) == 0: zeros.append(w)
        assert zeros == [make_witness(c)]
        check(c, zeros[0])
        exhaustive.append({'N': N, 'assignments': 36, 'zero_count': len(zeros)})
    checks.append({'exhaustive_one_branch': exhaustive})
    # Full branch selection, all four arithmetic factors, no-op, free outputs and exact time.
    chain = Machine(tuple(f'q{i}' for i in range(5))+('halt',), 'halt', (
        Instruction('q0', 'q1', 'inc', 0), Instruction('q1', 'q2', 'inc', 1),
        Instruction('q2', 'q3', 'dec', 0), Instruction('q3', 'q4', 'dec', 1),
        Instruction('q4', 'halt', 'nop', 0)))
    machines = [('arithmetic-chain', chain, 'q0', 5)]
    for counter in (0, 1):
        m = Machine(('s', 'z', 'p', 'halt'), 'halt', (
            Instruction('s', 'z', 'zero', counter), Instruction('s', 'p', 'positive', counter),
            Instruction('z', 'halt', 'zero', counter), Instruction('p', 'halt', 'positive', counter)))
        machines.append((f'test-counter-{counter}', m, 's', 2))
    physical_ticks = 0
    sample_cert = sample_wit = None
    for label, m, q0, h in machines:
        ca = gen.ThreeMassCA(m.states, m.halt, [gen.Instruction(**i.__dict__) for i in m.instructions])
        for N in range(1, 9):
            c = export_certificate(m, q0, h, {'mode': 'fixed_raw', 'N': N},
                                   {'mode': 'free'}, {'mode': 'free'})
            w = make_witness(c)
            r = check(c, w)
            assert cofactor(N) == cofactor(r['final_N'])
            expected = [(row['microtime'], row['state'], row['N']) for row in r['source_trace'][1:]]
            config, got = ca.initial(q0, N), []
            for tick in range(1, r['physical_time']+1):
                config = ca.step(config, require_specified=True)
                assert len(config) == 3
                ready = ca.ready(config)
                if ready is not None: got.append((tick, *ready))
            assert expected == got, (label, N, expected, got)
            assert config == ca.initial(m.halt, r['final_N'])
            physical_ticks += r['physical_time']
            lattice.append({'machine': label, 'N': N, 'source_horizon': h,
                            'physical_time': r['physical_time'], 'ready_boundaries': got})
            # Every single-coordinate increment invalidates the unique full witness.
            for name in w:
                mutant = dict(w); mutant[name] += 1
                assert polynomial_value(c, mutant) > 0
                rejects += rejected(lambda: check(c, mutant))
            for wrong_h in (h-1, h+1):
                bad = export_certificate(m, q0, wrong_h, {'mode': 'fixed_raw', 'N': N})
                rejects += rejected(lambda: make_witness(bad))
            if label == 'arithmetic-chain' and N == 5: sample_cert, sample_wit = c, w
        del ca
    # Free positive raw N: positivity is a substitution, exactly one extra input variable.
    c = export_certificate(chain, 'q0', 5, {'mode': 'free_raw'}, {'mode': 'free'}, {'mode': 'free'})
    for x in (0, 1, 4, 6, 10):
        w = make_witness(c, {'raw_input_minus_one': x}); check(c, w)
        assert w['output_N'] == x+1
    assert c['ledger']['total_variables'] == 53
    checks.append({'free_raw_input_fibers': 5, 'ledger': c['ledger']})
    # Fully paid bounded counter loader. Natural one-hot selectors require no Boolean gates.
    c = export_certificate(chain, 'q0', 5, {'mode': 'bounded_counters', 'A': 2, 'B': 2},
                           {'mode': 'free'}, {'mode': 'free'})
    for a, b in product(range(3), repeat=2):
        w = make_witness(c, {'input_a': a, 'input_b': b}); check(c, w)
        assert w['output_N'] == 2**a*3**b
    assert c['ledger']['total_variables'] == 63
    assert c['ledger']['total_squares'] == 21
    rejects += rejected(lambda: make_witness(c, {'input_a': 3, 'input_b': 0}))
    fixed_counter = export_certificate(one_inc, 's', 1,
        {'mode': 'bounded_counters', 'A': 2, 'B': 1, 'a': 2, 'b': 1})
    check(fixed_counter, make_witness(fixed_counter))
    checks.append({'bounded_counter_fibers': 9, 'ledger': c['ledger']})
    # h=0 is literal immediate halting, never a padded source run.
    empty = Machine(('s', 'halt'), 'halt', ())
    c = export_certificate(empty, 'halt', 0, {'mode': 'fixed_raw', 'N': 5},
                           {'mode': 'fixed', 'value': 5}, {'mode': 'fixed', 'value': 0})
    assert make_witness(c) == {}; check(c, {})
    assert c['ledger']['total_variables'] == 0 and c['ledger']['total_squares'] == 3
    for m, q0, h in ((empty, 's', 0), (empty, 's', 1), (empty, 'halt', 1), (one_inc, 'halt', 1)):
        c = export_certificate(m, q0, h, {'mode': 'fixed_raw', 'N': 5})
        rejects += rejected(lambda: make_witness(c))
    c = export_certificate(empty, 'halt', 0, {'mode': 'free_raw'}, {'mode': 'free'}, {'mode': 'free'})
    check(c, make_witness(c, {'raw_input_minus_one': 4}))
    checks.append({'zero_horizon': 'fixed/free input and output; nonfinal and padded runs rejected'})
    # Stuck nonfinal raw inputs are not a source-safe-subclass assumption.
    trap_cases = []
    for op, p, values in [('dec', 2, (1, 3, 5, 7)), ('dec', 3, (1, 2, 5, 7)),
                           ('zero', 2, (2, 6)), ('positive', 3, (1, 5))]:
        counter = 0 if p == 2 else 1
        m = Machine(('s', 'halt'), 'halt', (Instruction('s', 'halt', op, counter),))
        ca = gen.ThreeMassCA(m.states, m.halt, [gen.Instruction(**i.__dict__) for i in m.instructions])
        for N in values:
            c = export_certificate(m, 's', 1, {'mode': 'fixed_raw', 'N': N})
            rejects += rejected(lambda: make_witness(c))
            conf = ca.initial('s', N)
            # Dispatch into escape at 2*(4L+1)+2+1 = 8L+5; then inspect indefinitely separating geometry.
            dispatch_tick = 96*N+5
            for tick in range(1, dispatch_tick+250):
                conf = ca.step(conf, require_specified=True)
                assert ca.ready(conf) is None
            names = [ca.names[t] for _, t in conf]
            assert any(name[0] == 'escape' for name in names)
            assert any(name[0] == 'trap' for name in names)
            escape_x = next(x for x,t in conf if ca.names[t][0] == 'escape')
            trap_x = next(x for x,t in conf if ca.names[t][0] == 'trap')
            assert escape_x < trap_x < 0
            trap_cases.append({'operation': op, 'prime': p, 'N': N, 'tested_ticks': dispatch_tick+249})
        del ca
    checks.append({'stuck_source_escape_cases': trap_cases})
    # Explicit counterexample to any nonnegative-real exactness claim.
    dec = Machine(('s', 'halt'), 'halt', (Instruction('s', 'halt', 'dec', 0),))
    c = export_certificate(dec, 's', 1, {'mode': 'fixed_raw', 'N': 3})
    rational_zero = {'e_0_0': Fraction(1), 'u_0_0': Fraction(1, 2)}
    assert polynomial_value(c, rational_zero, allow_rational=True) == 0
    rejects += rejected(lambda: check(c, rational_zero))
    rejects += rejected(lambda: make_witness(c))
    checks.append({'real_relaxation_counterexample': 'DEC2 at N=3: e=1, u=1/2, P=0; no natural witness'})
    # Invalid source syntax/inputs are explicitly rejected, not silently assumed.
    bad_machines = [Machine(('s', 'halt'), 'halt', (Instruction('halt', 's', 'nop'),)),
        Machine(('s', 'halt'), 'halt', (Instruction('s', 'halt', 'inc'), Instruction('s', 'halt', 'zero'))),
        Machine(('s', 't', 'halt'), 'halt', (Instruction('s', 'halt', 'inc'), Instruction('t', 'halt', 'dec'))),
        Machine(('s', 't', 'halt'), 'halt', (Instruction('s', 'halt', 'zero', 0), Instruction('t', 'halt', 'positive', 1)))]
    for m in bad_machines: rejects += rejected(m.validate)
    for N in (0, -1, 1.5, True):
        rejects += rejected(lambda: export_certificate(one_inc, 's', 1, {'mode': 'fixed_raw', 'N': N}))
    # Structural corruption checks: check derives constraints independently of exporter.
    for field in ('squares', 'products', 'steps', 'ledger', 'branches'):
        corrupt = copy.deepcopy(sample_cert)
        if field == 'squares': corrupt[field][0]['affine'][''] = -2
        elif field == 'products': corrupt[field][0]['left'] = {}
        elif field == 'steps': corrupt[field][0][0]['ticks']['e_0_0'] += 1
        elif field == 'ledger': corrupt[field]['total_variables'] += 1
        else: corrupt[field][0]['prime'] = 3
        rejects += rejected(lambda: check(corrupt, sample_wit))
    # Strict scalar rejection and immutable snapshots of caller-owned descriptors.
    for bad_counter in (True, False, 0.0, 1.0):
        bad = Machine(('s', 'halt'), 'halt', (Instruction('s', 'halt', 'inc', bad_counter),))
        rejects += rejected(bad.validate)
    mutable_states = ['s', 'halt']
    mutable_instructions = [Instruction('s', 'halt', 'inc', 0)]
    stable_machine = Machine(mutable_states, 'halt', mutable_instructions)
    mutable_states[0] = 'changed'; mutable_instructions.clear()
    assert stable_machine.states == ('s', 'halt') and len(stable_machine.instructions) == 1
    in_spec = {'mode': 'fixed_raw', 'N': 5}
    out_spec = {'mode': 'free', 'name': 'answer'}
    time_spec = {'mode': 'free', 'name': 'ticks'}
    stable = export_certificate(stable_machine, 's', 1, in_spec, out_spec, time_spec)
    before = json.dumps(stable, sort_keys=True)
    in_spec['N'] = 99; out_spec['name'] = 'changed'; time_spec.clear()
    assert json.dumps(stable, sort_keys=True) == before
    check(stable, make_witness(stable))
    for scalar in (True, 1.0):
        corrupt = copy.deepcopy(sample_cert)
        corrupt['steps'][0][0]['old']['e_0_0'] = scalar
        rejects += rejected(lambda: check(corrupt, sample_wit))
    checks.append({'descriptor_hardening': 'strict integer scalars and caller-mutation isolation passed'})
    # Expanded sparse polynomial equals presentation at arbitrary natural assignments.
    expanded = expand_polynomial(sample_cert)
    rng = random.Random(20261002)
    for _ in range(30):
        w = {v: rng.randrange(4) for v in sample_cert['variables']}
        val = 0
        for term in expanded:
            part = term['coefficient']
            for name in term['monomial']: part *= w[name]
            val += part
        assert val == polynomial_value(sample_cert, w)
    sample_cert['expanded_polynomial'] = expanded
    corrupt = copy.deepcopy(sample_cert)
    corrupt['expanded_polynomial'][0]['coefficient'] += 1
    rejects += rejected(lambda: check(corrupt, sample_wit))
    clock_checks = test_clock_scale(gen, machines, radius_one_path)
    checks.append({'clock_scale': clock_checks})
    (output_dir/'example_certificate.json').write_text(json.dumps(sample_cert, indent=2)+'\n')
    (output_dir/'example_witness.json').write_text(json.dumps(sample_wit, indent=2)+'\n')
    (output_dir/'example_check.json').write_text(json.dumps(check(sample_cert, sample_wit), indent=2)+'\n')
    return {'status': 'passed', 'generator_path': str(generator_path),
            'generator_sha256': hashlib.sha256(Path(generator_path).read_bytes()).hexdigest(),
            'lattice_replay_cases': len(lattice), 'lattice_microsteps': physical_ticks,
            'lattice_cases': lattice, 'rejections': rejects, 'checks': checks,
            'sample_ledger': sample_cert['ledger'], 'expanded_sample_monomials': len(expanded),
            'elapsed_seconds': round(time.time()-started, 3)}

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    default = HERE/'three_mass_collision_generator.py'
    if not default.exists(): default = HERE.parent/'three_mass_collision_generator.py'
    p.add_argument('--generator', type=Path, default=default)
    p.add_argument('--receipt', type=Path, default=HERE/'test_receipt.json')
    p.add_argument('--output-dir', type=Path, default=HERE)
    p.add_argument('--radius-one', type=Path)
    a = p.parse_args()
    result = run(a.generator, a.output_dir, a.radius_one)
    a.receipt.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('lattice_cases', 'checks')}, indent=2))

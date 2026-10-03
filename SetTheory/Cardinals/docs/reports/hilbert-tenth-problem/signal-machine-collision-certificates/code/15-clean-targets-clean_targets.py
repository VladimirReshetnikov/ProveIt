#!/usr/bin/env python3
"""Fresh-start reversible source cleanup and compact exact-target certificates.

This composes a proved source transform with the frozen three-mass compiler.
The certificate witnesses only the original forward source run. It is not an
arbitrary CA trajectory verifier, and its target depends on its input raw N.
"""
from copy import deepcopy
from dataclasses import asdict
from pathlib import Path
import argparse
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / 'vendor'))
import certificate as core

Instruction, Machine = core.Instruction, core.Machine


def clean_source(machine, initial):
    machine.validate()
    if type(initial) is not str or initial not in machine.states:
        raise ValueError('initial state must belong to the source')
    if any(i.target == initial for i in machine.instructions):
        raise ValueError('fresh initial state must have no incoming instruction')
    f = {q: 'F:'+q for q in machine.states}
    b = {q: 'B:'+q for q in machine.states}
    reverse = {'inc': 'dec', 'dec': 'inc', 'nop': 'nop', 'zero': 'zero', 'positive': 'positive'}
    instructions = [Instruction(f[i.source], f[i.target], i.operation, i.counter)
                    for i in machine.instructions]
    instructions += [Instruction(b[i.target], b[i.source], reverse[i.operation], i.counter)
                     for i in machine.instructions]
    instructions += [Instruction(f[machine.halt], b[machine.halt], 'nop'),
                     Instruction(b[initial], 'H', 'nop')]
    wrapped = Machine(tuple(f.values())+tuple(b.values())+('H',), 'H', tuple(instructions)).validate()
    return wrapped, f[initial]


def source_ledger(machine):
    machine.validate()
    return {'states': len(machine.states), 'instructions': len(machine.instructions),
            'instruction_modulus': len(machine.instructions)+1,
            'arithmetic_instructions': sum(i.operation in ('inc', 'dec') for i in machine.instructions),
            'expanded_branches': len(machine.branches())}


def machine_json(machine):
    return {'states': list(machine.states), 'halt': machine.halt,
            'instructions': [asdict(i) for i in machine.instructions]}


def export_clean_certificate(machine, initial, horizon, input_spec, time_spec=None,
                             model='native'):
    if model not in ('native', 'spatial-radius-one', 'phase-radius-one'):
        raise ValueError('model must be native, spatial-radius-one, or phase-radius-one')
    wrapped, wrapped_initial = clean_source(machine, initial)
    forward = core.export_certificate(machine, initial, horizon, input_spec)
    scale = 4 if model == 'phase-radius-one' else 1
    native_time = core.add(core.scale(forward['physical_time'], 2),
                           core.scale(forward['final_N'], 192),
                           core.scale(forward['initial_N'], 192), core.affine(16))
    clock = core.scale(native_time, scale)
    variables = list(forward['variables'])
    outputs, squares = [], deepcopy(forward['squares'])
    if time_spec is not None:
        if type(time_spec) is not dict or time_spec.get('mode') not in ('fixed', 'free'):
            raise ValueError('time endpoint must be fixed or free')
        allowed = {'mode', 'value'} if time_spec['mode'] == 'fixed' else {'mode', 'name'}
        if set(time_spec)-allowed:
            raise ValueError('unknown time endpoint fields')
        if time_spec['mode'] == 'fixed':
            value = time_spec.get('value')
            if type(value) is not int or value < 0:
                raise ValueError('fixed time must be natural')
            target = core.affine(value)
        else:
            name = time_spec.get('name', 'cleaned_physical_time')
            if type(name) is not str or not name or name in variables:
                raise ValueError('time output name must be nonempty and fresh')
            variables.append(name); outputs.append(name); target = core.var(name)
        squares.append({'label': 'terminal:cleaned-physical-time', 'affine': core.sub(clock, target)})
    return {'format': 'three-mass-clean-exact-target-v1', 'domain': 'nonnegative integers',
            'forward_certificate': forward,
            'cleaned_machine': machine_json(wrapped), 'cleaned_initial_state': wrapped_initial,
            'cleaned_source_horizon': 2*horizon+2,
            'model': model, 'clock_scale': scale,
            'initial_N': deepcopy(forward['initial_N']),
            'exact_target_N': deepcopy(forward['initial_N']),
            'exact_target_state': 'H',
            'source_ledger': source_ledger(machine), 'cleaned_source_ledger': source_ledger(wrapped),
            'variables': variables, 'input_variables': list(forward['input_variables']),
            'output_variables': outputs, 'time_spec': deepcopy(time_spec),
            'physical_time': clock, 'squares': squares, 'products': deepcopy(forward['products']),
            'ledger': {'forward_source_horizon': horizon, 'cleaned_source_horizon': 2*horizon+2,
                       'branch_count': len(machine.branches()),
                       'core_variables': 2*len(machine.branches())*horizon,
                       'input_variables': len(forward['input_variables']),
                       'loader_variables': forward['ledger']['loader_variables'],
                       'output_variables': len(outputs), 'total_variables': len(variables),
                       'core_squares': 3*horizon+1,
                       'loader_squares': forward['ledger']['loader_squares'],
                       'endpoint_squares': int(time_spec is not None), 'total_squares': len(squares),
                       'product_slots': len(forward['products']), 'maximum_degree': 2}}


def make_clean_witness(cert, free_inputs=None):
    witness = core.make_witness(cert['forward_certificate'], free_inputs)
    if cert['output_variables']:
        witness[cert['output_variables'][0]] = core.evaluate_affine(cert['physical_time'], witness)
    if core.polynomial_value(cert, witness):
        raise ValueError('cleaned time endpoint disagrees with the execution')
    return witness



def affine_full_witness_lift(cert):
    """Return the naive certificate and affine lift, valid on compact zero fibers.

    The bridge base forms Nh-1 and N0-1 need not be natural off that zero set.
    No identity of off-zero polynomial values is asserted.
    """
    forward = cert['forward_certificate']
    original = core.machine_from_json(forward['machine'])
    wrapped, initial = clean_source(original, forward['initial_state'])
    h, B = forward['horizon'], len(forward['branches'])
    # A legal original interface name may collide with a NEW naive e/u slot.
    # Rename such external coordinates hygienically; the affine map records it.
    reserved = {f'{kind}_{t}_{b}' for kind in ('e', 'u')
                for t in range(2*h+2) for b in range(2*B+2)}
    used, aliases = reserved | set(cert['variables']), {}
    def coordinate(old, role):
        if old not in reserved: return old
        j = 0
        while f'clean_lift_{role}_{j}' in used: j += 1
        new = f'clean_lift_{role}_{j}'; used.add(new); aliases[new] = old
        return new
    input_spec = deepcopy(forward['input_spec'])
    if input_spec['mode'] == 'free_raw':
        input_spec['name'] = coordinate(forward['input_variables'][0], 'input')
    elif input_spec['mode'] == 'bounded_counters':
        for key in ('a', 'b'):
            if input_spec.get(key) is None:
                input_spec[key+'_name'] = coordinate(input_spec.get(key+'_name', 'input_'+key), 'input')
    time_spec = deepcopy(cert['time_spec'])
    if time_spec is not None and time_spec['mode'] == 'free':
        time_spec['name'] = coordinate(cert['output_variables'][0], 'output')
    naive = core.export_certificate(wrapped, initial, cert['cleaned_source_horizon'],
                                   input_spec, time_spec=time_spec, clock_scale=cert['clock_scale'])
    forms = {v: {} for v in naive['variables']}
    step_variables = {row[k] for local in naive['steps'] for row in local for k in ('e', 'u')}
    # Loader selectors and genuine coordinates keep exactly their original roles.
    for v in naive['variables']:
        if v not in step_variables:
            forms[v] = core.var(aliases.get(v, v))
    for t, local in enumerate(forward['steps']):
        for b, row in enumerate(local):
            for key in ('e', 'u'):
                forms[naive['steps'][t][b][key]] = core.var(row[key])
                forms[naive['steps'][2*h-t][B+b][key]] = core.var(row[key])
    for t, b, raw in ((h, 2*B, forward['final_N']),
                       (2*h+1, 2*B+1, forward['initial_N'])):
        row = naive['steps'][t][b]
        forms[row['e']] = core.affine(1)
        forms[row['u']] = core.sub(raw, core.affine(1))
    return naive, forms


def lift_clean_witness(cert, witness):
    """Validate a compact zero and lift it to the unique full cleaned witness."""
    from check_clean_targets import check
    check(cert, witness)
    naive, forms = affine_full_witness_lift(cert)
    lifted = {v: core.evaluate_affine(form, witness) for v, form in forms.items()}
    if core.polynomial_value(naive, lifted):
        raise ValueError('internal error: affine lift did not produce a cleaned zero')
    return naive, lifted


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    e = sub.add_parser('export'); e.add_argument('request'); e.add_argument('certificate')
    e.add_argument('--expanded', action='store_true')
    w = sub.add_parser('witness'); w.add_argument('certificate'); w.add_argument('witness')
    w.add_argument('--inputs', default='{}')
    args = p.parse_args()
    if args.command == 'export':
        request = json.loads(Path(args.request).read_text())
        cert = export_clean_certificate(core.machine_from_json(request['machine']),
                 request['initial_state'], request['horizon'], request['input_spec'],
                 request.get('time_spec'), request.get('model', 'native'))
        if args.expanded: cert['expanded_polynomial'] = core.expand_polynomial(cert)
        Path(args.certificate).write_text(json.dumps(cert, indent=2)+'\n')
    else:
        cert = json.loads(Path(args.certificate).read_text())
        witness = make_clean_witness(cert, json.loads(args.inputs))
        Path(args.witness).write_text(json.dumps(witness, indent=2)+'\n')

if __name__ == '__main__': main()

#!/usr/bin/env python3
"""Paid, quadratic, natural-domain source-horizon certificate for three-mass CA.

No third-party dependencies. The horizon counts source instructions, not CA ticks.
The emitted polynomial is the sum of recorded affine squares and affine products.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from copy import deepcopy
import argparse
import json
from pathlib import Path
from typing import Any

# Affine expressions are sparse maps; key '' is the constant coefficient.
def affine(constant=0, **coefficients):
    return {k: v for k, v in {'': constant, **coefficients}.items() if v}
def add(*expressions):
    out = {}
    for a in expressions:
        for k, v in a.items(): out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}
def scale(a, c): return {k: c*v for k, v in a.items() if c*v}
def sub(a, b): return add(a, scale(b, -1))
def var(name): return {name: 1}
def evaluate_affine(a, assignment):
    return sum(v*(assignment[k] if k else 1) for k, v in a.items())

@dataclass(frozen=True)
class Instruction:
    source: str
    target: str
    operation: str
    counter: int = 0

@dataclass(frozen=True)
class Branch:
    instruction: int
    source: str
    target: str
    operation: str
    prime: int
    residue: int = 0

@dataclass(frozen=True)
class Machine:
    states: tuple[str, ...]
    halt: str
    instructions: tuple[Instruction, ...]

    def __post_init__(self):
        object.__setattr__(self, 'states', tuple(self.states))
        object.__setattr__(self, 'instructions', tuple(self.instructions))

    def validate(self):
        if any(type(q) is not str or not q for q in self.states) or type(self.halt) is not str:
            raise ValueError('state names must be nonempty strings')
        if not self.states or len(set(self.states)) != len(self.states):
            raise ValueError('states must be a nonempty ordered set')
        if self.halt not in self.states: raise ValueError('halt is not a state')
        for ins in self.instructions:
            if type(ins) is not Instruction:
                raise ValueError('instructions must be immutable Instruction records')
            if any(type(x) is not str for x in (ins.source, ins.target, ins.operation)):
                raise ValueError('instruction names and operations must be strings')
            if ins.source not in self.states or ins.target not in self.states:
                raise ValueError('instruction has unknown state')
            if ins.source == self.halt: raise ValueError('halt must have no outgoing instructions')
            if ins.operation not in ('inc', 'dec', 'nop', 'zero', 'positive'):
                raise ValueError('unknown operation')
            if type(ins.counter) is not int or ins.counter not in (0, 1): raise ValueError('counter must be 0 or 1')
        # Morita separated syntax, both forward and inverse; missing branches allowed.
        for side in ('source', 'target'):
            for state in self.states:
                group = [i for i in self.instructions if getattr(i, side) == state]
                if len(group) <= 1: continue
                if any(i.operation not in ('zero', 'positive') for i in group):
                    raise ValueError(f'{side} {state} overlaps motion instructions')
                if len({i.counter for i in group}) != 1:
                    raise ValueError(f'{side} {state} tests different counters')
                if len({i.operation for i in group}) != len(group):
                    raise ValueError(f'{side} {state} overlaps test guards')
        return self

    def branches(self):
        self.validate()
        result = []
        for j, ins in enumerate(self.instructions):
            p = (2, 3)[ins.counter]
            for r in (range(1, p) if ins.operation == 'zero' else [0]):
                result.append(Branch(j, ins.source, ins.target, ins.operation, p, r))
        return result


def branch_forms(branch, e, u):
    """Return affine old N, new N, and exact CA ticks, with inactive value zero."""
    s = add(e, u)
    op, p = branch.operation, branch.prime
    if op == 'inc': old, new = s, scale(s, p)
    elif op == 'dec': old, new = scale(s, p), s
    elif op == 'positive': old = new = scale(s, p)
    elif op == 'zero': old = new = add(scale(u, p), scale(e, branch.residue))
    else: old = new = s
    if op == 'inc': ticks = add(scale(old, 108), scale(new, 96), scale(e, 8))
    elif op == 'dec': ticks = add(scale(old, 96), scale(new, 108), scale(e, 8))
    else: ticks = add(scale(old, 192), scale(e, 8))
    return old, new, ticks


def export_certificate(machine: Machine, q0: str, horizon: int,
                       input_spec: dict[str, Any],
                       output_spec: dict[str, Any] | None = None,
                       time_spec: dict[str, Any] | None = None):
    """Input modes: fixed_raw N; free_raw x; bounded_counters A,B and a,b.

    In bounded_counters, a,b may be fixed natural numbers or None for free
    coordinates. Optional output/time modes: fixed value or free name.
    """
    machine.validate()
    def snapshot_spec(spec, optional=False):
        if spec is None and optional: return None
        if type(spec) is not dict: raise ValueError('specification must be a dictionary')
        result = deepcopy(spec)
        if any(type(k) is not str for k in result): raise ValueError('specification keys must be strings')
        if any(v is not None and type(v) not in (str, int) for v in result.values()):
            raise ValueError('specification values must be strings, strict integers, or null')
        return result
    input_spec = snapshot_spec(input_spec)
    output_spec = snapshot_spec(output_spec, True)
    time_spec = snapshot_spec(time_spec, True)
    allowed_input = {'fixed_raw': {'mode', 'N'}, 'free_raw': {'mode', 'name'},
                     'bounded_counters': {'mode', 'A', 'B', 'a', 'b', 'a_name', 'b_name'}}
    if input_spec.get('mode') not in allowed_input or set(input_spec)-allowed_input[input_spec['mode']]:
        raise ValueError('unknown input specification fields')
    for spec in (output_spec, time_spec):
        if spec is None: continue
        allowed = {'fixed': {'mode', 'value'}, 'free': {'mode', 'name'}}
        if spec.get('mode') not in allowed or set(spec)-allowed[spec['mode']]:
            raise ValueError('unknown endpoint specification fields')
    if type(q0) is not str or q0 not in machine.states: raise ValueError('initial state unknown')
    if type(horizon) is not int or horizon < 0: raise ValueError('horizon is a fixed natural number')
    branches = machine.branches()
    variables, inputs, outputs, squares, products, loader = [], [], [], [], [], {}
    def new_var(name, role):
        if not isinstance(name, str) or not name or name in variables:
            raise ValueError('variable names must be nonempty and unique')
        variables.append(name)
        if role == 'input': inputs.append(name)
        elif role == 'output': outputs.append(name)
        return var(name)
    def sq(label, form): squares.append({'label': label, 'affine': form})
    mode = input_spec.get('mode')
    if mode == 'fixed_raw':
        N = input_spec.get('N')
        if type(N) is not int or N < 1: raise ValueError('fixed raw N must be an integer >=1')
        initial_N = affine(N)
    elif mode == 'free_raw':
        name = input_spec.get('name', 'raw_input_minus_one')
        initial_N = add(affine(1), new_var(name, 'input'))
    elif mode == 'bounded_counters':
        A, C = input_spec.get('A'), input_spec.get('B')
        if any(type(x) is not int or x < 0 for x in (A, C)):
            raise ValueError('counter bounds must be fixed natural numbers')
        values = []
        for key in ('a', 'b'):
            value = input_spec.get(key)
            if value is None:
                values.append(new_var(input_spec.get(key+'_name', 'input_'+key), 'input'))
            elif type(value) is int and value >= 0: values.append(affine(value))
            else: raise ValueError('counter input must be natural or free')
        selectors, a_form, b_form, N_form = [], {}, {}, {}
        for a in range(A+1):
            for b in range(C+1):
                name = f'load_{a}_{b}'
                sel = new_var(name, 'loader')
                selectors.append(sel)
                a_form = add(a_form, scale(sel, a))
                b_form = add(b_form, scale(sel, b))
                N_form = add(N_form, scale(sel, 2**a * 3**b))
        sq('loader:one-hot', sub(add(*selectors), affine(1)))
        sq('loader:counter-a', sub(values[0], a_form))
        sq('loader:counter-b', sub(values[1], b_form))
        initial_N = N_form
        loader = {'selector_count': (A+1)*(C+1), 'square_count': 3,
                  'counter_a': values[0], 'counter_b': values[1]}
    else: raise ValueError('unknown input mode')
    initial_q = affine(machine.states.index(q0))
    previous_N, previous_q, total_ticks = initial_N, initial_q, {}
    steps = []
    for t in range(horizon):
        local = []
        for j, branch in enumerate(branches):
            en, un = f'e_{t}_{j}', f'u_{t}_{j}'
            e, u = new_var(en, 'witness'), new_var(un, 'witness')
            old, new, ticks = branch_forms(branch, e, u)
            local.append({'branch': j, 'e': en, 'u': un, 'old': old, 'new': new, 'ticks': ticks})
        selector_sum = add(*(var(row['e']) for row in local))
        old_sum = add(*(row['old'] for row in local))
        new_sum = add(*(row['new'] for row in local))
        source_q = add(*(scale(var(row['e']), machine.states.index(branches[j].source))
                         for j, row in enumerate(local)))
        target_q = add(*(scale(var(row['e']), machine.states.index(branches[j].target))
                         for j, row in enumerate(local)))
        sq(f'step-{t}:one-hot', sub(selector_sum, affine(1)))
        sq(f'step-{t}:control', sub(source_q, previous_q))
        sq(f'step-{t}:value', sub(old_sum, previous_N))
        for row in local:
            e, u = var(row['e']), var(row['u'])
            products.append({'label': f"step-{t}:inactive-{row['branch']}",
                             'left': sub(selector_sum, e), 'right': add(e, u)})
        total_ticks = add(total_ticks, *(row['ticks'] for row in local))
        previous_N, previous_q = new_sum, target_q
        steps.append(local)
    sq('terminal:halt', sub(previous_q, affine(machine.states.index(machine.halt))))
    def endpoint(spec, default_name, expr, label):
        if spec is None: return
        if spec.get('mode') == 'fixed':
            value = spec.get('value')
            if type(value) is not int or value < 0: raise ValueError('fixed endpoint is natural')
            target = affine(value)
        elif spec.get('mode') == 'free':
            target = new_var(spec.get('name', default_name), 'output')
        else: raise ValueError('endpoint mode must be fixed or free')
        sq(label, sub(expr, target))
    endpoint(output_spec, 'output_N', previous_N, 'terminal:output-N')
    endpoint(time_spec, 'physical_time', total_ticks, 'terminal:physical-time')
    cert = {'format': 'three-mass-source-horizon-v1', 'domain': 'nonnegative integers',
            'machine': {'states': list(machine.states), 'halt': machine.halt,
                        'instructions': [asdict(i) for i in machine.instructions]},
            'initial_state': q0, 'horizon': horizon, 'input_spec': input_spec,
            'output_spec': output_spec, 'time_spec': time_spec,
            'branches': [asdict(b) for b in branches], 'variables': variables,
            'input_variables': inputs, 'output_variables': outputs,
            'squares': squares, 'products': products, 'steps': steps,
            'initial_N': initial_N, 'final_N': previous_N, 'physical_time': total_ticks,
            'loader': loader,
            'ledger': {'branch_count': len(branches), 'source_horizon': horizon,
                       'core_variables': 2*len(branches)*horizon,
                       'input_variables': len(inputs), 'output_variables': len(outputs),
                       'loader_variables': loader.get('selector_count', 0),
                       'total_variables': len(variables), 'core_squares': 3*horizon+1,
                       'loader_squares': loader.get('square_count', 0),
                       'endpoint_squares': (output_spec is not None)+(time_spec is not None),
                       'total_squares': len(squares), 'product_slots': len(products),
                       'maximum_degree': 2}}
    return cert


def natural_assignment(cert, assignment):
    if set(assignment) != set(cert['variables']): raise ValueError('assignment has missing or excess variables')
    if any(type(v) is not int or v < 0 for v in assignment.values()):
        raise ValueError('every variable must be a nonnegative integer')


def polynomial_value(cert, assignment, allow_rational=False):
    if not allow_rational: natural_assignment(cert, assignment)
    terms = [evaluate_affine(row['affine'], assignment)**2 for row in cert['squares']]
    terms += [evaluate_affine(row['left'], assignment)*evaluate_affine(row['right'], assignment)
              for row in cert['products']]
    return sum(terms)


def expand_polynomial(cert):
    """Canonical integer sparse polynomial, degree at most two; constants use []."""
    terms = {}
    def mul(a, b):
        for x, c in a.items():
            for y, d in b.items():
                monomial = tuple(sorted(k for k in (x, y) if k))
                terms[monomial] = terms.get(monomial, 0) + c*d
    for row in cert['squares']: mul(row['affine'], row['affine'])
    for row in cert['products']: mul(row['left'], row['right'])
    return [{'monomial': list(k), 'coefficient': v} for k, v in sorted(terms.items()) if v]


def make_witness(cert, free_inputs=None):
    """Construct the sole witness in a specified input fiber; reject other horizons."""
    free_inputs = free_inputs or {}
    if set(free_inputs) != set(cert['input_variables']): raise ValueError('supply exactly the free inputs')
    assignment = dict.fromkeys(cert['variables'], 0)
    assignment.update(free_inputs)
    spec = cert['input_spec']
    if spec['mode'] == 'bounded_counters':
        a = evaluate_affine(cert['loader']['counter_a'], assignment)
        b = evaluate_affine(cert['loader']['counter_b'], assignment)
        if not 0 <= a <= spec['A'] or not 0 <= b <= spec['B']: raise ValueError('counter outside paid bound')
        assignment[f'load_{a}_{b}'] = 1
    N = evaluate_affine(cert['initial_N'], assignment)
    q, ticks = cert['initial_state'], 0
    for local in cert['steps']:
        if q == cert['machine']['halt']: raise ValueError('horizon extends after first halt')
        enabled = []
        for j, b in enumerate(cert['branches']):
            if b['source'] != q: continue
            p, op = b['prime'], b['operation']
            if op in ('dec', 'positive') and N % p: continue
            if op == 'zero' and N % p != b['residue']: continue
            enabled.append(j)
        if len(enabled) != 1: raise ValueError('source is stuck or ambiguous')
        j = enabled[0]
        b, row = cert['branches'][j], local[j]
        op, p = b['operation'], b['prime']
        if op in ('dec', 'positive'): u = N//p - 1
        elif op == 'zero': u = (N-b['residue'])//p
        else: u = N-1
        assignment[row['e']], assignment[row['u']] = 1, u
        N = evaluate_affine(row['new'], assignment)
        ticks += evaluate_affine(row['ticks'], assignment)
        q = b['target']
    if q != cert['machine']['halt']: raise ValueError('horizon does not end at halt')
    for spec, value, default in ((cert['output_spec'], N, 'output_N'),
                                 (cert['time_spec'], ticks, 'physical_time')):
        if spec is not None and spec['mode'] == 'free': assignment[spec.get('name', default)] = value
    if polynomial_value(cert, assignment) != 0: raise ValueError('requested endpoints disagree with execution')
    return assignment


def machine_from_json(obj):
    return Machine(tuple(obj['states']), obj['halt'],
                   tuple(Instruction(**ins) for ins in obj['instructions'])).validate()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='command', required=True)
    exp = sub.add_parser('export')
    exp.add_argument('request'); exp.add_argument('certificate')
    exp.add_argument('--expanded', action='store_true')
    wit = sub.add_parser('witness')
    wit.add_argument('certificate'); wit.add_argument('witness')
    wit.add_argument('--inputs', default='{}')
    args = ap.parse_args()
    if args.command == 'export':
        request = json.loads(Path(args.request).read_text())
        cert = export_certificate(machine_from_json(request['machine']), request['initial_state'],
                                  request['horizon'], request['input_spec'],
                                  request.get('output_spec'), request.get('time_spec'))
        if args.expanded: cert['expanded_polynomial'] = expand_polynomial(cert)
        Path(args.certificate).write_text(json.dumps(cert, indent=2)+'\n')
    else:
        cert = json.loads(Path(args.certificate).read_text())
        witness = make_witness(cert, json.loads(args.inputs))
        Path(args.witness).write_text(json.dumps(witness, indent=2)+'\n')

if __name__ == '__main__': main()

#!/usr/bin/env python3
"""Independent finite Grill word-closure audit; no universality bound."""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import types

PIN = '144129bb04e271588ed1c95d9c91f5682d30c6b5a540154c6c0b9b0c40331d96'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def load(path):
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == PIN, 'source pin before execution')
    module = types.ModuleType('_independent_grill_word_closure')
    module.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module

def const(n):
    return {(): n} if n else {}

def var(n):
    return {(n,): 1}

def add(a, b, sign=1):
    ans = dict(a)
    for key, value in b.items():
        ans[key] = ans.get(key, 0) + sign * value
    return {key: value for key, value in ans.items() if value}

def mul(a, b):
    ans = {}
    for left, x in a.items():
        for right, y in b.items():
            key = tuple(sorted(left + right))
            ans[key] = ans.get(key, 0) + x * y
    return {key: value for key, value in ans.items() if value}

def scale(a, n):
    return {key: value * n for key, value in a.items() if value * n}

def formal(packet):
    names = packet['inputs'] + packet['witnesses']
    need(len(names) == len(set(names)), 'unique free coordinates')
    env = {name: var(name) for name in names}
    counts = Counter()
    for name, op, a, b in packet['source']:
        need(type(name) is str and name not in env and op in ('+', '-', '*'), 'typed SSA')
        need(all(type(v) in (int, str) and (type(v) is int or v in env) for v in (a, b)), 'typed source closure')
        need(not (type(a) is int and type(b) is int), 'constant-only gate')
        need(not (op == '*' and (a in (0, 1) or b in (0, 1))), 'neutral product')
        aa = env[a] if type(a) is str else const(a)
        bb = env[b] if type(b) is str else const(b)
        env[name] = mul(aa, bb) if op == '*' else add(aa, bb, 1 if op == '+' else -1)
        counts['M' if op == '*' else 'A'] += 1
    live = {packet['output']}
    for name, op, a, b in reversed(packet['source']):
        need(name in live, 'dead output gate')
        live.update(v for v in (a, b) if type(v) is str)
    need(live & set(names) == set(names), 'all stated coordinates consumed')
    return env, counts

def manual(program, t):
    width = add(scale(var('x'), 3), var('Z0'))
    aggregate = {}; bits = {}; booleans = []
    for i in range(t):
        d = add(var('D' + str(i)), const(-1))
        term = mul(d, width)
        aggregate = add(aggregate, term)
        bits = add(bits, scale(d, 2**i))
        width = add(width, scale(term, 2 * 4**program[i % len(program)] - 1))
        booleans.append(mul(d, add(d, const(-1))))
    r1 = add(width, const(-(2**t)))
    r2 = add(add(add(var('Z0'), aggregate), scale(bits, 3)), const(-(2**t)))
    output = add(mul(r1, r1), mul(r2, r2))
    for b in booleans:
        output = add(output, b)
    return [r1, r2], booleans, output

def independent_run(program, x, width, heads):
    need(width > 3 * x > 0 and width & (width - 1) == 0, 'initial positive cone')
    word = ''.join(str((x >> i) & 1) for i in range(width.bit_length() - 1))
    initial = word
    for i, head in enumerate(heads):
        if not word:
            return initial, i
        need(int(word[0]) == head, 'causal prefix head')
        word = word[1:] + ('0' + '10' * program[i % len(program)] if head else '')
    need(not word, 'empty at or before terminal index')
    return initial, len(heads)


def census(programs, last_t=10):
    count = Counter(); fixtures = []
    for program, t in itertools.product(programs, range(1, last_t + 1)):
        for heads in itertools.product((0, 1), repeat=t):
            count['all_boolean_words'] += 1
            exponent = t - sum(d * (1 + 2 * program[i % len(program)]) for i, d in enumerate(heads))
            if exponent < 0:
                continue
            initial_width = 2**exponent; width = initial_width; aggregate = 0
            for i, d in enumerate(heads):
                term = d * width; aggregate += term
                width += (2 * 4**program[i % len(program)] - 1) * term
            need(width == 2**t, 'independent terminal width')
            bit_value = sum(d * 2**i for i, d in enumerate(heads))
            z0 = 2**t - aggregate - 3 * bit_value
            if z0 <= 0 or initial_width <= z0 or (initial_width - z0) % 3:
                continue
            x = (initial_width - z0) // 3
            initial, halt = independent_run(program, x, initial_width, heads)
            appended = ''.join('0' + '10' * program[i % len(program)] for i, d in enumerate(heads) if d)
            need(''.join(map(str, heads)) == initial + appended, 'exact global word closure')
            count['positive_word_closures'] += 1
            count['halts_exactly_t' if halt == t else 'posthalt_closures'] += 1
            fixtures.append(dict(program=list(program), t=t, heads=list(heads), x=x, Z0=z0, halt=halt))
    return count, fixtures

def verify(source):
    module = load(source); counts = Counter()
    programs = ((0,), (1,), (0, 1, 1), (1, 0), (2, 0, 1), (0, 0, 2, 1))
    for program, t in itertools.product(programs, range(1, 7)):
        main_rows, booleans, expected = manual(program, t)
        reference = expected
        for b in booleans:
            reference = add(add(reference, mul(b, b)), b, -1)
        outputs = {}
        for mode, squared in itertools.product(('scaled', 'direct'), (False, True)):
            packet = module.build(program, t, mode=mode, square_boolean=squared)
            env, gate_counts = formal(packet)
            residuals = main_rows + booleans
            need(all(env[name] == wanted for name, wanted in zip(packet['residuals'], residuals)), 'all literal residual identities')
            wanted = reference if squared else expected
            need(env[packet['output']] == wanted, 'entire source polynomial identity')
            need(max(map(len, wanted)) == 2 * t + 2, 'exact expanded full degree')
            z = sum(program[i % len(program)] == 0 for i in range(t))
            m = (4 if mode == 'scaled' else 5) * t + 3 - z + t * squared
            a = 6 * t + 4
            need(gate_counts == dict(M=m, A=a), 'independently charged full source')
            need(packet['ledger'] == dict(M=m, A=a, operations=m+a, positive_witnesses=t+1, residuals=t+2, exact_degree=2*t+2), 'all ledger fields')
            outputs[(mode, squared)] = env[packet['output']]
            counts['literal_complete_sources'] += 1
            counts['literal_residual_identities'] += len(residuals)
            counts['exact_expanded_degrees'] += 1
            for seed in range(3):
                values = {name: (seed + 2*i) % 9 - 4 for i, name in enumerate(packet['inputs'] + packet['witnesses'])}
                independent = sum(coef * product(values[name] for name in term) for term, coef in wanted.items())
                need(module.evaluate(packet, values, signed=True) == independent, 'full signed public evaluation')
                counts['signed_full_outputs'] += 1
        need(outputs['direct', False] == outputs['scaled', False], 'identical unshared/shared polynomial')
        need(outputs['direct', True] == outputs['scaled', True], 'identical reference polynomial')
        counts['shared_direct_full_identities'] += 2
    finite_counts, fixtures = census(programs)
    counts.update(finite_counts)
    for fixture in fixtures:
        program = tuple(fixture['program']); t = fixture['t']
        values = dict(x=fixture['x'], Z0=fixture['Z0'], **{'D'+str(i): d+1 for i, d in enumerate(fixture['heads'])})
        for mode in ('scaled', 'direct'):
            packet = module.build(program, t, mode=mode)
            need(module.evaluate(packet, values) == 0, 'entire census source zero')
            decoded = module.decode_zero(packet, values)
            need(decoded['actual_first_halt'] == fixture['halt'], 'independent causal halt')
            counts['positive_source_zero_decodings'] += 1
    # The explicit noncausal extension cannot restore the old positive width history.
    packet = module.build((0, 1, 1), 6)
    values = {'x': 1, 'Z0': 1, **{'D'+str(i): int(d)+1 for i, d in enumerate('100010')}}
    decoded = module.decode_zero(packet, values)
    need(decoded['actual_first_halt'] == 3 and decoded['formal_widths'][4] == '1/2', 'posthalt scope counterexample')
    # Use our literal polynomial to independently verify the exact positive rational false zero.
    _, _, real_poly = manual((0, 1, 1), 3)
    real = dict(x=1, Z0=1, D0=2, D1=1+Fraction(1, 3333), D2=1)
    real_value = sum(coef * product(real[name] for name in term) for term, coef in real_poly.items())
    need(real_value == 0, 'positive rational false zero')
    delta_poly = {}
    for term, coefficient in real_poly.items():
        value = const(coefficient)
        for name in term:
            factor = add(const(1), var('delta')) if name == 'D1' else const(real[name])
            value = mul(value, factor)
        delta_poly = add(delta_poly, value)
    need(delta_poly == {('delta',): -1, ('delta', 'delta'): 3333}, 'whole rational-slice identity')
    counts['scope_counterexamples'] = 2
    def reject(fn):
        try:
            fn()
        except (ValueError, TypeError, KeyError):
            counts['malformed_rejected'] += 1
        else:
            raise ValueError('invalid caller accepted')
    for bad in ([], [0], (), (True,), (0.0,), (-1,), None):
        reject(lambda bad=bad: module.build(bad, 3))
    for bad in (True, 1.0, 0, -1, None):
        reject(lambda bad=bad: module.build((0,), bad))
    for bad in (0, 1, True, None, 'other'):
        reject(lambda bad=bad: module.build((0,), 3, mode=bad))
    for bad in (0, 1, 0.0, None):
        reject(lambda bad=bad: module.build((0,), 3, square_boolean=bad))
    for name in values:
        for bad in (True, 1.0, 0, -1, None):
            candidate = dict(values); candidate[name] = bad
            reject(lambda candidate=candidate: module.evaluate(packet, candidate))
    reject(lambda: module.evaluate(packet, dict(values, surplus=1)))
    reject(lambda: module.evaluate(packet, {'x': 1}))
    reject(lambda: module.evaluate(packet, values, signed=1))
    reject(lambda: module.evaluate(module.build((0, 1, 1), 3), real))
    for key in packet:
        candidate = dict(packet); candidate[key] = None
        reject(lambda candidate=candidate: module.checked(candidate))
    for bad in (True, 3.0):
        candidate = module.build((0, 1, 1), 3)
        row = list(candidate['source'][0]); index = next(i for i in (2, 3) if type(row[i]) is int)
        row[index] = bad; candidate['source'][0] = tuple(row)
        reject(lambda candidate=candidate: module.checked(candidate))
    for mode in ('direct', 'scaled'):
        before = module.build((0, 1, 1), 3, mode=mode)
        changed = module.build((0, 1, 1), 3, mode=mode)
        changed['source'].clear(); changed['registers']['scales'].clear()
        need(exact(before, module.build((0, 1, 1), 3, mode=mode)), 'no mutable canonical cache')
        counts['fresh_packet_isolation'] += 1
    result = dict(status='PASS_INDEPENDENT_FINITE_WORD_CLOSURE', source_sha256=PIN,
                  helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), checks=dict(counts),
                  census_programs=programs, census_max_horizon=10, positive_closure_census=fixtures,
                  scope='Literal finite word-closure sources and integer halting soundness; no positive-history bijection, fixed-arity horizon, universal program or decoder claim.',
                  posthalt_fixture=dict(values=values, decoded=decoded),
                  real_counterexample=dict(values={k:str(v) for k,v in real.items()}, slice_polynomial='3333*delta^2-delta'))
    return json.loads(json.dumps(result, sort_keys=True))

def product(values):
    result = 1
    for value in values:
        result *= value
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).with_name('grill_tag_word_closure.py'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args(); result = verify(args.source)
    if args.expect:
        need(exact(result, json.loads(args.expect.read_text())), 'exact typed receipt mismatch')
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(status=result['status'], checks=result['checks']), sort_keys=True))

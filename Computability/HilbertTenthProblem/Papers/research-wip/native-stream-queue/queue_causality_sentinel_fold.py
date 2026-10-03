"""Paid positive-coordinate cyclic-tag certificates via a sentinel right fold.

This is a fixed-horizon compiler. The first-failure guard remains paid;
no fixed-arity or universal-operation bound follows from its linear size.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random


def word(value):
    result = tuple(int(c) for c in value) if isinstance(value, str) else tuple(value)
    assert all(type(x) is int and x in (0, 1) for x in result)
    return result


def code(value):
    return sum(b << i for i, b in enumerate(value))


def sentinel(value):
    return (1 << len(value))+code(value)


class DAG:
    def __init__(self, names):
        assert len(names) == len(set(names))
        self.names, self.rows, self.cache = list(names), [], {}
    def op(self, op, a, b):
        if isinstance(a, int) and isinstance(b, int):
            return a+b if op == '+' else a-b if op == '-' else a*b
        if op == '+':
            if a == 0: return b
            if b == 0: return a
        if op == '-' and b == 0: return a
        if op == '*':
            if a == 0 or b == 0: return 0
            if a == 1: return b
            if b == 1: return a
        # Identical expressions share one paid register in both schedules.
        if op in ('+', '*') and repr(a) > repr(b):
            a, b = b, a
        key = op, a, b
        if key not in self.cache:
            name = f'r{len(self.rows)}'
            self.rows.append((name, op, a, b))
            self.cache[key] = name
        return self.cache[key]
    def add(self, a, b): return self.op('+', a, b)
    def sub(self, a, b): return self.op('-', a, b)
    def mul(self, a, b): return self.op('*', a, b)
    def total(self, values):
        result = 0
        for value in values:
            result = self.add(result, value)
        return result
    def close(self, output):
        rows = {n: (a, b) for n, _, a, b in self.rows}
        seen, todo = set(), [output]
        while todo:
            name = todo.pop()
            if not isinstance(name, str) or name not in rows or name in seen:
                continue
            seen.add(name)
            todo.extend(rows[name])
        source = [row for row in self.rows if row[0] in seen]
        available = set(self.names)
        for n, _, a, b in source:
            assert n not in available
            assert all(not isinstance(v, str) or v in available for v in (a, b))
            available.add(n)
        assert not isinstance(output, str) or output in available
        return source


def guard_divisor(program, initial_length, horizon):
    """Only positive factors constant as polynomials are omitted."""
    divisor, variable = 1, False
    for i in range(horizon):
        if not variable and initial_length-i > 0:
            divisor *= initial_length-i
        variable |= bool(program[i % len(program)])
    return divisor


def build(appendants, initial, horizon, terminal=(), *, mode='sentinel', exact=True):
    program = tuple(word(a) for a in appendants)
    initial, terminal = word(initial), word(terminal)
    T = horizon
    assert program and type(T) is int and T >= 1
    assert mode in ('sentinel', 'forward', 'forward_nonnegative')
    assert exact or (mode == 'sentinel' and not terminal)
    names = [f'bit{i}_hat' for i in range(T)]+(['guard'] if exact else [])
    c = DAG(names)
    bits = [c.sub(name, 1) for name in names[:T]]
    booleans = [c.mul(b, c.sub(b, 1)) for b in bits]
    phase = [program[i % len(program)] for i in range(T)]
    lengths = [len(initial)]
    G = 1
    for i, b in enumerate(bits):
        if not (isinstance(lengths[-1], int) and lengths[-1] > 0):
            G = c.mul(G, lengths[-1])
        if i < T-1 or mode != 'sentinel':
            lengths.append(c.add(c.sub(lengths[-1], 1), c.mul(len(phase[i]), b)))
    guard_residual = c.sub(G, 'guard') if exact else None
    if mode == 'sentinel':
        produced = 1
        for b, app in reversed(list(zip(bits, phase))):
            increment = c.add(code(app), c.mul((1 << len(app))-1, produced))
            produced = c.add(produced, c.mul(b, increment))
        consumed = sentinel(terminal)
        for b in reversed(bits):
            consumed = c.add(c.mul(2, consumed), b)
        all_produced = c.add(code(initial), c.mul(1 << len(initial), produced))
        word_residual = c.sub(all_produced, consumed)
        terms = booleans+[c.mul(word_residual, word_residual)]
        if exact:
            terms.append(c.mul(guard_residual, guard_residual))
        output = c.total(terms)
    else:
        # Same forward formulas as report07, with the same positive shifts,
        # constant folding, common-expression sharing and dead-code removal.
        prefix, appended, consumed = 1, 0, 0
        for i, (b, app) in enumerate(zip(bits, phase)):
            appended = c.add(appended, c.mul(code(app), c.mul(b, prefix)))
            prefix = c.mul(prefix, c.add(1, c.mul((1 << len(app))-1, b)))
            consumed = c.add(consumed, c.mul(1 << i, b))
        content = c.sub(c.add(code(initial), c.mul(1 << len(initial), appended)),
                        c.add(consumed, (1 << T)*code(terminal)))
        length_residual = c.sub(lengths[-1], len(terminal))
        terms = ([c.mul(v, v) for v in booleans] if mode == 'forward' else booleans)
        output = c.total(terms+[c.mul(v, v) for v in (length_residual, content, guard_residual)])
    source = c.close(output)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    degree = dict.fromkeys(names, 1)
    value = lambda v: degree[v] if isinstance(v, str) else 0
    for n, op, a, b in source:
        degree[n] = value(a)+value(b) if op == '*' else max(value(a), value(b))
    return dict(source=source, output=output, auxiliaries=names, parameters=[],
        operations=len(source), M=count['M'], A=count['A'], witnesses=len(names),
        degree_upper_bound=value(output), mode=mode, horizon=T,
        appendants=program, initial=initial, terminal=terminal,
        positive_domain=True, exact_duration=exact,
        guard_divisor=guard_divisor(program, len(initial), T) if exact else None)


def choose(appendants, initial, horizon, terminal=()):
    """Cheapest of two proved positive-zero-equivalent sources; no optimality claim."""
    candidates = [build(appendants, initial, horizon, terminal, mode=mode)
                  for mode in ('sentinel', 'forward_nonnegative')]
    result = min(candidates, key=lambda p: (p['operations'], p['degree_upper_bound'], p['M']))
    return dict(result, planner_candidates=[summary(p) for p in candidates])


def execute(source, values):
    env = dict(values)
    for n, op, a, b in source:
        x = env[a] if isinstance(a, str) else a
        y = env[b] if isinstance(b, str) else b
        env[n] = x+y if op == '+' else x-y if op == '-' else x*y
    return env


def evaluate(packet, values):
    env = execute(packet['source'], values)
    return env[packet['output']] if isinstance(packet['output'], str) else packet['output']


def run(program, initial, horizon):
    queue = tuple(initial)
    reads, states = [], [queue]
    for i in range(horizon):
        if not queue: break
        b, queue = queue[0], queue[1:]
        if b: queue += tuple(program[i % len(program)])
        reads.append(b)
        states.append(queue)
    return reads, states


def witness(packet):
    assert packet['exact_duration']
    bits, states = run(packet['appendants'], packet['initial'], packet['horizon'])
    if len(bits) != packet['horizon'] or states[-1] != packet['terminal']:
        return None
    G = 1
    for q in states[:-1]: G *= len(q)
    assert G % packet['guard_divisor'] == 0
    return dict(zip(packet['auxiliaries'], [b+1 for b in bits]+[G//packet['guard_divisor']]))


def independent_values(program, initial, bits, terminal):
    """Forward scalar oracle, including arbitrary signed candidate digits."""
    length, G, prefix, appended = len(initial), 1, 1, 0
    lengths = []
    for i, b in enumerate(bits):
        app = program[i % len(program)]
        lengths.append(length)
        G *= length
        appended += code(app)*b*prefix
        prefix *= 1+((1 << len(app))-1)*b
        length += len(app)*b-1
    consumed = sum(b << i for i, b in enumerate(bits))
    content = code(initial)+(1 << len(initial))*appended-consumed-(1 << len(bits))*code(terminal)
    sent = content+(1 << len(initial))*prefix-(1 << (len(bits)+len(terminal)))
    divisor = guard_divisor(program, len(initial), len(bits))
    assert G % divisor == 0
    return dict(length=length-len(terminal), content=content, sentinel=sent,
                guard=G//divisor, full_guard=G, guard_divisor=divisor,
                boolean=[b*(b-1) for b in bits], lengths=lengths)


def summary(packet):
    return {key: packet[key] for key in ('mode', 'horizon', 'operations', 'M', 'A',
        'witnesses', 'degree_upper_bound', 'exact_duration', 'guard_divisor')} | dict(source_sha256=hashlib.sha256(
            repr(packet['source']).encode()).hexdigest())


def algebra_audit():
    rng = random.Random(703141)
    identities = signed = 0
    for _ in range(24):
        program = tuple(tuple(rng.randrange(2) for _ in range(rng.randrange(5)))
                        for _ in range(rng.randrange(1, 5)))
        initial = tuple(rng.randrange(2) for _ in range(rng.randrange(5)))
        terminal = tuple(rng.randrange(2) for _ in range(rng.randrange(4)))
        T = rng.randrange(1, 10)
        packets = [build(program, initial, T, terminal, mode=mode)
                   for mode in ('sentinel', 'forward', 'forward_nonnegative')]
        for case in range(16):
            draw = lambda: rng.randrange(1, 5) if case < 8 else rng.randrange(-3, 5)
            values = {n: draw() for n in packets[0]['auxiliaries']}
            bits = [values[f'bit{i}_hat']-1 for i in range(T)]
            v = independent_values(program, initial, bits, terminal)
            new = sum(v['boolean'])+v['sentinel']**2+(v['guard']-values['guard'])**2
            old = sum(t*t for t in v['boolean'])+v['length']**2+v['content']**2+(v['guard']-values['guard'])**2
            assert evaluate(packets[0], values) == new
            assert evaluate(packets[1], values) == old
            improved = sum(v['boolean'])+v['length']**2+v['content']**2+(v['guard']-values['guard'])**2
            assert evaluate(packets[2], values) == improved
            identities += 3
            signed += 3*(case >= 8)
    return dict(complete_scalar_oracle_identities=identities, signed_cases=signed)


def exhaustive_audit():
    words = [tuple(b) for n in range(3) for b in product((0, 1), repeat=n)]
    # Full Boolean candidates, including every impossible continuation after
    # an empty queue, are checked against a separately executed queue.
    candidates = exact = bad_balance = 0
    for a in words:
      for b in words:
        program = (a, b)
        for initial in words:
          for T in range(1, 6):
            actual, states = run(program, initial, T)
            terminals = list(dict.fromkeys([(), (0,), (1,), states[-1]]))
            for terminal in terminals:
              new = build(program, initial, T, terminal)
              old = build(program, initial, T, terminal, mode='forward')
              expected = len(actual) == T and states[-1] == terminal
              good = 0
              for bits in product((0, 1), repeat=T):
                v = independent_values(program, initial, bits, terminal)
                values = dict(zip(new['auxiliaries'], [x+1 for x in bits]+[max(1, v['guard'])]))
                nv, ov = evaluate(new, values), evaluate(old, values)
                assert (nv == 0) == (ov == 0) == (expected and list(bits) == actual)
                if nv == 0:
                    good += 1
                    assert witness(new) == values
                    for delta in (-1, 1):
                        if values['guard']+delta > 0:
                            other = dict(values, guard=values['guard']+delta)
                            assert evaluate(new, other) > 0
                if v['sentinel'] == 0 and not (expected and list(bits) == actual):
                    assert v['guard'] == 0
                    bad_balance += 1
                candidates += 1
              assert good == int(expected)
              exact += good
    # Non-Boolean supplied hats cannot be hidden by other residuals.
    boxes = 0
    for program, initial, terminal in [(((1, 0), ()), (1,), ()),
                                       (((1,),), (0,), ()),
                                       (((1, 1),), (0,), (1,))]:
      for T in range(1, 4):
        p = build(program, initial, T, terminal)
        for hats in product(range(1, 4), repeat=T):
          for guard in range(1, 13):
            values = dict(zip(p['auxiliaries'], hats+(guard,)))
            if evaluate(p, values) == 0:
                assert values == witness(p)
            boxes += 1
    return dict(boolean_candidates=candidates, exact_execution_zeros=exact,
                uncausal_sentinel_equalities_rejected=bad_balance,
                full_positive_box_assignments=boxes)


def obstruction_audit():
    rows = []
    for T in range(2, 17):
        program, initial, terminal = ((1,),), (0,), ()
        bits = (0,)+(1,)*(T-1)
        v = independent_values(program, initial, bits, terminal)
        assert v['sentinel'] == v['length'] == v['content'] == v['guard'] == 0
        actual, states = run(program, initial, T)
        assert actual == [0] and len(states) == 2
        rows.append(dict(horizon=T, claimed_bits='0'+'1'*(T-1), first_halt=1, guard=0))
    # A false nonempty endpoint, not just a noncanonical later emptying time.
    v = independent_values(((1, 1),), (0,), (0, 1), (1,))
    assert v['sentinel'] == 0 and v['guard'] == 0
    return dict(exact_time_family=rows,
                false_nonempty_endpoint=dict(appendants=['11'], initial='0', bits='01', terminal='1'))


def eventual_audit():
    """Only the union over horizons has an eventual-halting equivalence."""
    words = [tuple(b) for n in range(3) for b in product((0, 1), repeat=n)]
    candidates = zeros = late = unions = 0
    for program in product(words, repeat=2):
      for initial in words:
        seen = not initial  # The separately handled zero-step halt.
        for T in range(1, 6):
            packet = build(program, initial, T, exact=False)
            actual, states = run(program, initial, T)
            halted = not states[-1]
            for bits in product((0, 1), repeat=T):
                values = dict(zip(packet['auxiliaries'], [b+1 for b in bits]))
                v = independent_values(program, initial, bits, ())
                value = evaluate(packet, values)
                assert value == sum(v['boolean'])+v['sentinel']**2
                if value == 0:
                    assert halted
                    seen = True
                    zeros += 1
                    late += len(actual) < T
                if halted and len(actual) == T and list(bits) == actual:
                    assert value == 0
                candidates += 1
            assert seen == halted
            assert packet['witnesses'] == T
            assert packet['operations'] <= 10*T+1
            assert packet['degree_upper_bound'] <= 2*T
            unions += 1
    rng = random.Random(710981)
    identities = signed = 0
    for case in range(128):
        program = tuple(rng.choice(words) for _ in range(3))
        initial, T = rng.choice(words), rng.randrange(1, 12)
        packet = build(program, initial, T, exact=False)
        values = {n: rng.randrange(-4, 5) if case % 2 else rng.randrange(1, 6)
                  for n in packet['auxiliaries']}
        v = independent_values(program, initial,
                               [values[f'bit{i}_hat']-1 for i in range(T)], ())
        assert evaluate(packet, values) == sum(v['boolean'])+v['sentinel']**2
        identities += 1
        signed += case % 2
    return dict(boolean_candidates=candidates, balance_zeros=zeros,
                later_than_actual_halt=late, bounded_horizon_unions=unions,
                scalar_oracle_identities=identities, signed_cases=signed)


def verify():
    ledgers = []
    for program, initial, terminal in [(((1, 0),), (1, 0, 1), ()),
                                      (((1, 0), ()), (1,), ()),
                                      (((1, 0, 1), (0,), (1, 1)), (1, 1), (0,))]:
      for T in (1, 2, 4, 8, 16, 32):
        new = build(program, initial, T, terminal)
        old = build(program, initial, T, terminal, mode='forward')
        improved = build(program, initial, T, terminal, mode='forward_nonnegative')
        selected = choose(program, initial, T, terminal)
        eventual = build(program, initial, T, exact=False)
        assert selected['operations'] == min(new['operations'], improved['operations'])
        assert selected['operations'] <= old['operations']
        assert new['witnesses'] == old['witnesses'] == T+1
        assert new['degree_upper_bound'] <= 2*T
        # Uniform bound uses no favourable constant zero/one cancellation.
        if T >= 2:
            assert new['operations'] <= 14*T-2
        ledgers.append(dict(appendants=[''.join(map(str, a)) for a in program],
            initial=''.join(map(str, initial)), terminal=''.join(map(str, terminal)),
            sentinel=summary(new), forward=summary(old),
            forward_nonnegative=summary(improved), selected=summary(selected),
            eventual=summary(eventual),
            saved_operations=old['operations']-new['operations']))
    fallback = choose(['00'], '00', 8)
    assert fallback['mode'] == 'forward_nonnegative'
    return dict(status='PASS_QUEUE_CAUSALITY_SENTINEL_FOLD', ledgers=ledgers,
        zero_content_fallback=summary(fallback),
        algebra=algebra_audit(), exhaustive=exhaustive_audit(), obstruction=obstruction_audit(),
        eventual=eventual_audit(),
        scope='Canonical positive exact-horizon cyclic-tag certificate; fixed input/program/terminal. '
              'Guard-free family represents halting only after existentially choosing a horizon '
              '(initially empty input handled separately at horizon zero). '
              'No uniform fixed-horizon-free polynomial, universal cost, or faithful online scalar queue memory.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status'])
    print(result['algebra'])
    print(result['exhaustive'])
    print([(v['sentinel']['horizon'], v['sentinel']['operations'], v['saved_operations'])
           for v in result['ledgers'][:6]])

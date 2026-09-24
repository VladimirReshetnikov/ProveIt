"""Constant-length nine-symbol raw queue; fully paid interface and transport.

This checks a machine theorem and a conditional 14-operation arithmetic
interface.  It does not implement a controller/mask/Pell certificate.
"""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import argparse
import json
import sympy as sp

PLAIN = ((0, 0), (1, 0), (2, 0), (0, 2))
MARKED = ((1, 1), (2, 1), (1, 2), (2, 2))
DELIM = (0, 1)
ALPHABET = PLAIN + MARKED + (DELIM,)
BLANK = 3
DECODE = {symbol: (a, marked) for marked, symbols in
          ((False, PLAIN), (True, MARKED)) for a, symbol in enumerate(symbols)}
assert len(set(ALPHABET)) == 9


@dataclass(frozen=True)
class State:
    kind: str
    q: str = ''
    held: tuple | None = None
    next_q: str | None = None
    seen: bool = False
    right: bool = False


class Machine:
    def __init__(self, name, transitions, initial='s', accept=('accept',), reject=('reject',)):
        self.name = name
        self.delta = dict(transitions)
        self.initial = initial
        self.accept = set(accept)
        self.reject = set(reject)
        assert not self.accept & self.reject
        self.states = {initial} | self.accept | self.reject | {
            q for q, _, _ in self.delta} | {v[0] for v in self.delta.values()}
        assert all(a in range(4) and b in range(4) and move in (-1, 0, 1)
                   for (_, a, _), (_, b, move) in self.delta.items())

    def start(self, q):
        return State('erase' if q in self.accept else 'loop' if q in self.reject else 'scan', q)

    def transition(self, state, symbol):
        assert symbol in ALPHABET
        bad = (State('loop'), symbol, 'reject')
        if state.kind in ('accept', 'loop'):
            return state, symbol, ''
        if state.kind == 'erase':
            return (State('accept', state.q), PLAIN[0], 'zero') if symbol == DELIM else (
                state, PLAIN[0], '')
        if state.kind in ('mark_first', 'mark_rest'):
            if symbol == DELIM:
                return bad if state.kind == 'mark_first' else (self.start(self.initial), DELIM, 'loaded')
            a, marked = DECODE[symbol]
            if marked:
                return bad
            return State('mark_rest'), MARKED[a] if state.kind == 'mark_first' else symbol, ''
        if state.kind == 'rotate':
            return (self.start(state.q), DELIM, 'pass') if symbol == DELIM else bad
        assert state.kind == 'scan'
        if symbol == DELIM:
            if not state.seen or state.held is None or state.right:
                return bad
            return State('rotate', state.next_q), state.held, ''
        a, marked = DECODE[symbol]
        held, seen, pending, nq = state.held, state.seen, state.right, state.next_q
        if marked:
            if seen or pending:
                return bad
            entry = self.delta.get((state.q, a, held is None))
            if entry is None:
                return bad
            nq, write, move = entry
            seen = True
            if move == -1:
                if held is None or DECODE[held][1]:
                    return bad
                output = MARKED[DECODE[held][0]]
                current = PLAIN[write]
            else:
                output = DELIM if held is None else held
                current = MARKED[write] if move == 0 else PLAIN[write]
                pending = move == 1
        else:
            output = DELIM if held is None else held
            current = MARKED[a] if pending else PLAIN[a]
            pending = False
        return State('scan', state.q, current, nq, seen, pending), output, ''

    def compile(self):
        initial = State('mark_first')
        states, todo, table = {initial}, [initial], {}
        while todo:
            state = todo.pop()
            for symbol in ALPHABET:
                nxt, output, event = self.transition(state, symbol)
                assert output in ALPHABET
                table[state, symbol] = (nxt, output, event)
                if nxt not in states:
                    states.add(nxt)
                    todo.append(nxt)
        return initial, table, states


def normalizer(client):
    delta = dict(client.delta)
    names = {'norm.scan', 'norm.trim', 'norm.return', 'norm.reject'}
    assert not client.states & names
    for left in (False, True):
        for a in range(4):
            delta['norm.scan', a, left] = (('norm.reject', a, 0) if left else
                ('norm.trim', a, -1)) if a == BLANK else ('norm.scan', a, 1)
            if a == BLANK:
                entry = ('norm.reject', a, 0)
            elif a == 0 and not left:
                entry = ('norm.trim', BLANK, -1)
            elif left:
                entry = (client.initial, a, 0)
            else:
                entry = ('norm.return', a, -1)
            delta['norm.trim', a, left] = entry
            delta['norm.return', a, left] = ((client.initial, a, 0) if left else
                                                    ('norm.return', a, -1))
    result = Machine(client.name, delta, 'norm.scan', client.accept, client.reject | {'norm.reject'})
    result.client_initial = client.initial
    return result


def coordinate(word, i):
    return sum(symbol[i] * 3 ** j for j, symbol in enumerate(word))


def step(machine, state, word, table=None):
    nxt, output, event = (table[state, word[0]] if table is not None else
                           machine.transition(state, word[0]))
    result = word[1:] + (output,)
    W = 3 ** len(word)
    for i in range(2):
        assert 3 * coordinate(result, i) == coordinate(word, i) - word[0][i] + output[i] * W
        assert coordinate(word, i) + output[i] * W < 3 * W
    assert len(result) == len(word)
    return nxt, result, event


def decode(word):
    assert word[-1] == DELIM and DELIM not in word[:-1]
    entries = [DECODE[a] for a in word[:-1]]
    heads = [i for i, (_, marked) in enumerate(entries) if marked]
    assert len(heads) == 1
    return [a for a, _ in entries], heads[0]


def direct(machine, q, tape, head):
    entry = machine.delta.get((q, tape[head], head == 0))
    if entry is None:
        return None, 'undefined'
    nq, write, move = entry
    nh = head + move
    if nh < 0 or nh >= len(tape):
        return None, 'left' if nh < 0 else 'right'
    result = list(tape)
    result[head] = write
    return (nq, result, nh), ''


def canonical(x):
    result = []
    while x:
        result.append(x % 3)
        x //= 3
    return result or [0]


def fixtures():
    clients = [Machine('initial_accept', {}, 'accept'), Machine('initial_reject', {}, 'reject'),
               Machine('undefined', {})]
    for name, move, target in [('stay_accept', 0, 'accept'), ('left_reject', -1, 'accept'),
                                ('infinite_stay', 0, 's')]:
        clients.append(Machine(name, {('s', a, left): (target, a, move)
                                      for a in range(4) for left in (False, True)}))
    delta = {('s', a, left): ('s', a, 1) if a != BLANK else ('extra1', a, 1)
             for a in range(4) for left in (False, True)}
    for q, nq in [('extra1', 'extra2'), ('extra2', 'accept')]:
        delta.update({(q, a, left): (nq, a, 1) for a in range(4) for left in (False, True)})
    clients.append(Machine('needs_extra_space', delta))
    return [normalizer(c) for c in clients]


def source_check():
    names = 'x L W R I1 alpha q X0 X1 D0 D1 A0 A1'.split()
    symbols = dict(zip(names, sp.symbols(' '.join(names))))
    dag = [('I1calc', '*', 5, 'L'), ('Wcalc', '*', 9, 'L'), ('Rcalc', '*', 3, 'W'),
           ('input_bound', '+', 'x', 'alpha')]
    for i, initial in ((0, 'x'), (1, 'I1')):
        dag += [(f'weighted{i}', '*', 'W', f'A{i}'), (f'cut{i}', '-', f'X{i}', f'D{i}'),
                (f'append{i}', '+', f'cut{i}', f'weighted{i}'), (f'left{i}', '*', 'W', f'append{i}'),
                (f'right{i}', '-', f'X{i}', initial)]
    env = dict(symbols)
    for name, op, a, b in dag:
        a, b = env[a] if isinstance(a, str) else a, env[b] if isinstance(b, str) else b
        env[name] = a * b if op == '*' else a + b if op == '+' else a - b
    comparisons = [('I1', 'I1calc'), ('W', 'Wcalc'), ('R', 'Rcalc'),
                   ('input_bound', 'L'), ('left0', 'right0'), ('left1', 'right1')]
    x, L, W, R, I1, alpha, q, X0, X1, D0, D1, A0, A1 = [symbols[a] for a in names]
    sources = [I1-5*L, W-9*L, R-3*W, x+alpha-L,
               W*(X0-D0+W*A0)-X0+x, W*(X1-D1+W*A1)-X1+I1]
    assert all(sp.expand(env[a]-env[b]-source) == 0
               for (a, b), source in zip(comparisons, sources))
    for Xi, Di, Ai, Ii in ((X0, D0, A0, x), (X1, D1, A1, I1)):
        old = R*(Xi-Di+W*Ai)-3*(Xi-Ii)
        new = W*(Xi-Di+W*Ai)-Xi+Ii
        assert sp.expand(old-3*new-(R-3*W)*(Xi-Di+W*Ai)) == 0
    return {'operations': len(dag), 'multiplications': sum(row[1] == '*' for row in dag),
            'additions_subtractions': sum(row[1] != '*' for row in dag),
            'initialization_operations': 4, 'transport_operations': 10,
            'instructions': dag, 'comparisons': comparisons, 'sources': [sp.sstr(s) for s in sources]}


def all_scans():
    counts = dict(cases=0, valid=0, left=0, right=0, queue_steps=0)
    for length in range(1, 5):
        for tape in product(range(4), repeat=length):
            for head in range(length):
                for write, move in product(range(4), (-1, 0, 1)):
                    machine = Machine('one', {('s', a, left): ('accept', write, move)
                                              for a in range(4) for left in (False, True)})
                    word = tuple(MARKED[a] if i == head else PLAIN[a] for i, a in enumerate(tape)) + (DELIM,)
                    state = machine.start('s')
                    expected, reason = direct(machine, 's', list(tape), head)
                    while True:
                        state, word, event = step(machine, state, word)
                        counts['queue_steps'] += 1
                        if event in ('pass', 'reject'):
                            break
                    if expected is None:
                        assert event == 'reject' and state.kind == 'loop'
                        counts[reason] += 1
                    else:
                        nq, wanted, nh = expected
                        assert event == 'pass' and state.kind == 'erase' and decode(word) == (wanted, nh)
                        counts['valid'] += 1
                    counts['cases'] += 1
    return counts


def runs():
    counts = dict(machines=0, compiled_states=0, compiled_entries=0, inputs=0, normalizations=0,
                  tm_steps=0, queue_steps=0, accepted=0, rejected=0, named_stay_cutoffs=0,
                  accepting_transports=0, positive_history_tuples=0, zero_endpoint_checks=0,
                  rejecting_loop_steps=0)
    outcomes = {}
    for machine in fixtures():
        initial, table, states = machine.compile()
        counts['machines'] += 1
        counts['compiled_states'] += len(states)
        counts['compiled_entries'] += len(table)
        for x in range(20):
            minimal = 1
            while 3 ** minimal <= x:
                minimal += 1
            for pad in (0, 2, 4):
                ell = minimal + pad
                L = 3 ** ell
                W, R = 9 * L, 27 * L
                word = tuple(PLAIN[x // 3**i % 3] for i in range(ell)) + (PLAIN[BLANK], DELIM)
                assert coordinate(word, 0) == x and coordinate(word, 1) == 5*L
                assert 3**len(word) == W and R == 3*W
                state, rows = initial, []

                def advance():
                    nonlocal state, word
                    nxt, output, event = table[state, word[0]]
                    rows.append((coordinate(word, 0), coordinate(word, 1), word[0], output))
                    state, word, checked_event = step(machine, state, word, table)
                    assert state == nxt and event == checked_event and len(word) == ell+2
                    assert all(a == PLAIN[0] for a in word) == (state.kind == 'accept')
                    counts['zero_endpoint_checks'] += 1
                    counts['queue_steps'] += 1
                    return event

                for _ in range(len(word)):
                    event = advance()
                assert event == 'loaded'
                tape, head = decode(word)
                qstate = machine.initial
                normalized = False
                for _ in range(100):
                    if qstate in machine.accept | machine.reject:
                        break
                    expected, reason = direct(machine, qstate, tape, head)
                    while advance() not in ('pass', 'reject'):
                        pass
                    if expected is None:
                        assert state.kind == 'loop'
                        qstate = 'reject'
                        break
                    oldstate = qstate
                    qstate, tape, head = expected
                    assert decode(word) == (tape, head)
                    counts['tm_steps'] += 1
                    if oldstate.startswith('norm.') and qstate == machine.client_initial:
                        wanted = canonical(x)
                        assert tape == wanted + [BLANK] * (ell+1-len(wanted)) and head == 0
                        normalized = True
                        counts['normalizations'] += 1
                assert normalized
                if state.kind == 'erase':
                    for _ in range(len(word)):
                        event = advance()
                    assert event == 'zero' and state.kind == 'accept' and all(a == PLAIN[0] for a in word)
                result = 'accept' if state.kind == 'accept' else 'reject' if state.kind == 'loop' else 'cutoff'
                outcomes[machine.name, x, pad] = result
                if result == 'cutoff':
                    assert machine.name == 'infinite_stay'
                    counts['named_stay_cutoffs'] += 1
                else:
                    counts['accepted' if result == 'accept' else 'rejected'] += 1
                if result == 'reject':
                    for _ in range(5):
                        advance()
                        assert state.kind == 'loop' and DELIM in word
                        counts['rejecting_loop_steps'] += 1
                if result == 'accept':
                    power, X, D, A = 1, [0, 0], [0, 0], [0, 0]
                    for n0, n1, removed, appended in rows:
                        for i, value in enumerate((n0, n1)):
                            X[i] += value * power
                            D[i] += removed[i] * power
                            A[i] += appended[i] * power
                        power *= R
                    F = [coordinate(word, i) for i in range(2)]
                    for i, I in enumerate((x, 5*L)):
                        assert W*(X[i]-D[i]+W*A[i]) == X[i]-I+power*F[i]
                    assert F == [0, 0] and all(value > 0 for value in X+D+A)
                    counts['positive_history_tuples'] += 1
                    counts['accepting_transports'] += 1
                counts['inputs'] += 1
    improvements = sum(outcomes['needs_extra_space', x, 0] == 'reject' and
                       outcomes['needs_extra_space', x, 4] == 'accept' for x in range(20))
    assert improvements > 0
    counts['strict_padding_improvements'] = improvements
    bad = fixtures()[0]
    state, word = State('mark_first'), (PLAIN[BLANK], DELIM)
    assert coordinate(word, 0) == 0 and coordinate(word, 1) == 5
    while state.kind != 'loop':
        state, word, event = step(bad, state, word)
    assert state.kind == 'loop' and DELIM in word and len(word) == 2
    counts['ell_zero_rejections'] = 1
    return counts


def verify():
    return dict(status='PASS_CONSTANT_LENGTH_RAW_QUEUE_COMPONENT', source=source_check(),
                runs=runs(), all_short_scans=all_scans(),
                proof='../1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md',
                review='Author and two independent complete scoped proof/source reviews pass; fresh exact receipt checks pass',
                scope='Universal ordinary-input machine contract and exact 14-operation initialization/transport component. No controller, masks, complete power geometry or Pell operation bound is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text(encoding='utf-8')) == json.loads(json.dumps(result))
    print(result['status'], result['source']['operations'])
    print(result['runs'])
    print(result['all_short_scans'])

"""Thirteen-operation raw queue interface with an internal delayed blank loader.

The frozen constant-length queue supplies the scan, normalizer and erasure
implementations. This successor changes only the loader and paid raw interface.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp
import explore_constant_length_raw_queue as old


class DelayedLoader(old.Machine):
    def transition(self, state, symbol):
        bad = (old.State('loop'), symbol, 'reject')
        if state.kind == 'mark_first':
            if symbol not in old.PLAIN[:3]:
                return bad
            a = old.PLAIN.index(symbol)
            return old.State('load_tail', held=old.MARKED[a]), old.DELIM, ''
        if state.kind == 'load_tail':
            if symbol == old.DELIM:
                a, marked = old.DECODE[state.held]
                if a != 0:
                    return bad
                blank = old.MARKED[old.BLANK] if marked else old.PLAIN[old.BLANK]
                return old.State('load_rotate'), blank, ''
            if symbol not in old.PLAIN[:3]:
                return bad
            return old.State('load_tail', held=symbol), state.held, ''
        if state.kind == 'load_rotate':
            return (self.start(self.initial), old.DELIM, 'loaded') if symbol == old.DELIM else bad
        return super().transition(state, symbol)


def wrap(machine):
    result = DelayedLoader(machine.name, machine.delta, machine.initial, machine.accept, machine.reject)
    result.client_initial = machine.client_initial
    return result


def source_check():
    names = 'x L W R alpha X0 X1 D0 D1 A0 A1'.split()
    env = dict(zip(names, sp.symbols(' '.join(names))))
    symbols = dict(env)
    dag = [('Wcalc', '*', 3, 'L'), ('Rcalc', '*', 3, 'W'), ('input_bound', '+', 'x', 'alpha')]
    for i, initial in ((0, 'x'), (1, 'L')):
        dag += [(f'weighted{i}', '*', 'W', f'A{i}'), (f'cut{i}', '-', f'X{i}', f'D{i}'),
                (f'append{i}', '+', f'cut{i}', f'weighted{i}'), (f'left{i}', '*', 'W', f'append{i}'),
                (f'right{i}', '-', f'X{i}', initial)]
    for name, op, a, b in dag:
        a, b = env[a] if isinstance(a, str) else a, env[b] if isinstance(b, str) else b
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    comparisons = [('W', 'Wcalc'), ('R', 'Rcalc'), ('input_bound', 'L'),
                   ('left0', 'right0'), ('left1', 'right1')]
    x, L, W, R, alpha, X0, X1, D0, D1, A0, A1 = [symbols[a] for a in names]
    sources = [W-3*L, R-3*W, x+alpha-L,
               W*(X0-D0+W*A0)-X0+x, W*(X1-D1+W*A1)-X1+L]
    assert all(sp.expand(env[a]-env[b]-source) == 0
               for (a, b), source in zip(comparisons, sources))
    for Xi, Di, Ai, Ii in ((X0, D0, A0, x), (X1, D1, A1, L)):
        original = R*(Xi-Di+W*Ai)-3*(Xi-Ii)
        divided = W*(Xi-Di+W*Ai)-Xi+Ii
        assert sp.expand(original-3*divided-(R-3*W)*(Xi-Di+W*Ai)) == 0
    return dict(operations=len(dag), multiplications=sum(row[1] == '*' for row in dag),
                additions_subtractions=sum(row[1] != '*' for row in dag),
                initialization_operations=3, transport_operations=10,
                instructions=dag, comparisons=comparisons, sources=[sp.sstr(s) for s in sources],
                initial_coordinates=['x', 'L'], final_coordinates=[0, 0],
                unpaid_geometry='L=3^ell and q=R^t for a common finite history; controller and row masks also unpaid')


def pack_and_check(rows, R, W, x, L):
    X, D, A, power = [0, 0], [0, 0], [0, 0], 1
    for coord, removed, appended in rows:
        for i in range(2):
            X[i] += coord[i]*power
            D[i] += removed[i]*power
            A[i] += appended[i]*power
        power *= R
    assert min(X+D+A) > 0
    for i, initial in enumerate((x, L)):
        assert W*(X[i]-D[i]+W*A[i]) == X[i]-initial
    return power


def exhaustive_loader():
    machine = wrap(old.fixtures()[0])
    initial, table, states = machine.compile()
    counts = dict(controls=len(states), entries=len(table), initial_words=0, accepted=0, rejected=0,
                  normalized=0, queue_steps=0, positive_transports=0,
                  ell_zero_rejections=0, ell_one_rejections=0, high_nonzero_rejections=0)
    for ell in range(7):
        L, W, R = 3**ell, 3**(ell+1), 3**(ell+2)
        for x in range(L):
            state = initial
            word = tuple(old.PLAIN[x//3**j % 3] for j in range(ell)) + (old.DELIM,)
            assert old.coordinate(word, 0) == x and old.coordinate(word, 1) == L
            rows = []
            for _ in range(1000):
                nxt, output, event = table[state, word[0]]
                rows.append((tuple(old.coordinate(word, i) for i in range(2)), word[0], output))
                state, word, checked = old.step(machine, state, word, table)
                assert state == nxt and event == checked and len(word) == ell+1
                assert all(a == old.PLAIN[0] for a in word) == (state.kind == 'accept')
                if state.kind not in ('erase', 'accept'):
                    assert old.DELIM in word
                if event == 'loaded':
                    assert old.decode(word) == ([x//3**j % 3 for j in range(ell-1)]+[old.BLANK], 0)
                if event == 'pass' and state.kind == 'erase':
                    wanted = old.canonical(x)
                    assert old.decode(word) == (wanted+[old.BLANK]*(ell-len(wanted)), 0)
                    counts['normalized'] += 1
                counts['queue_steps'] += 1
                if state.kind in ('accept', 'loop'):
                    break
            else:
                raise AssertionError('unexpected bounded loader cutoff')
            accepted = ell >= 2 and x < 3**(ell-1)
            assert (state.kind == 'accept') == accepted
            if accepted:
                pack_and_check(rows, R, W, x, L)
                counts['positive_transports'] += 1
                counts['accepted'] += 1
            else:
                counts['rejected'] += 1
                counts['ell_zero_rejections'] += ell == 0
                counts['ell_one_rejections'] += ell == 1
                counts['high_nonzero_rejections'] += ell >= 2 and x >= 3**(ell-1)
            counts['initial_words'] += 1
    return counts


def runs():
    counts = dict(machines=0, compiled_states=0, compiled_entries=0, inputs=0, loaded=0,
                  normalizations=0, tm_steps=0, queue_steps=0, accepted=0, rejected=0,
                  named_stay_cutoffs=0, positive_transports=0, rejecting_loop_steps=0)
    outcomes = {}
    for original in old.fixtures():
        machine = wrap(original)
        initial, table, states = machine.compile()
        counts['machines'] += 1
        counts['compiled_states'] += len(states)
        counts['compiled_entries'] += len(table)
        for x in range(20):
            minimal = 1
            while 3**minimal <= x:
                minimal += 1
            for pad in (0, 2, 4):
                ell = minimal+pad
                L, W, R = 3**ell, 3**(ell+1), 3**(ell+2)
                word = tuple(old.PLAIN[x//3**j % 3] for j in range(ell)) + (old.DELIM,)
                state, rows = initial, []

                def advance():
                    nonlocal state, word
                    nxt, output, event = table[state, word[0]]
                    rows.append((tuple(old.coordinate(word, i) for i in range(2)), word[0], output))
                    state, word, checked = old.step(machine, state, word, table)
                    assert state == nxt and checked == event and len(word) == ell+1
                    assert all(a == old.PLAIN[0] for a in word) == (state.kind == 'accept')
                    if state.kind not in ('erase', 'accept'):
                        assert old.DELIM in word
                    counts['queue_steps'] += 1
                    return event

                while True:
                    event = advance()
                    if event == 'loaded' or state.kind == 'loop':
                        break
                normalized = False
                if event == 'loaded':
                    counts['loaded'] += 1
                    tape, head = old.decode(word)
                    qstate = machine.initial
                    for _ in range(100):
                        if qstate in machine.accept | machine.reject:
                            break
                        expected, reason = old.direct(machine, qstate, tape, head)
                        while advance() not in ('pass', 'reject'):
                            pass
                        if expected is None:
                            assert state.kind == 'loop'
                            break
                        prior = qstate
                        qstate, tape, head = expected
                        assert old.decode(word) == (tape, head)
                        counts['tm_steps'] += 1
                        if prior.startswith('norm.') and qstate == machine.client_initial:
                            wanted = old.canonical(x)
                            assert tape == wanted+[old.BLANK]*(ell-len(wanted)) and head == 0
                            normalized = True
                            counts['normalizations'] += 1
                if state.kind == 'erase':
                    for _ in range(len(word)):
                        event = advance()
                    assert event == 'zero' and state.kind == 'accept'
                result = 'accept' if state.kind == 'accept' else 'reject' if state.kind == 'loop' else 'cutoff'
                outcomes[machine.name, x, pad] = result
                if result == 'accept':
                    assert normalized
                    pack_and_check(rows, R, W, x, L)
                    counts['accepted'] += 1
                    counts['positive_transports'] += 1
                elif result == 'reject':
                    counts['rejected'] += 1
                    for _ in range(5):
                        advance()
                        assert state.kind == 'loop' and old.DELIM in word
                        counts['rejecting_loop_steps'] += 1
                else:
                    assert machine.name == 'infinite_stay' and normalized
                    counts['named_stay_cutoffs'] += 1
                counts['inputs'] += 1
    counts['strict_padding_improvements'] = sum(
        outcomes['needs_extra_space', x, 0] == 'reject' and outcomes['needs_extra_space', x, 4] == 'accept'
        for x in range(20))
    assert counts['strict_padding_improvements'] == 20
    return counts


def verify():
    root = Path(__file__).resolve().parents[1]
    dependencies = {}
    for relative in ('1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md',
                     'verification/explore_constant_length_raw_queue.py',
                     'verification/explore_constant_length_raw_queue.json'):
        canonical = (root/relative).read_bytes().replace(b'\r\n', b'\n')
        dependencies[relative] = hashlib.sha256(canonical).hexdigest()
    return dict(status='PASS_DELAYED_BLANK_RAW_QUEUE_COMPONENT', source=source_check(),
                exhaustive_loader=exhaustive_loader(), runs=runs(), all_short_scans=old.all_scans(),
                dependency_canonical_lf_sha256=dependencies,
                proof='../1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md',
                review='Author and two independent complete scoped proof/source reviews pass; fresh exact receipt checks pass',
                scope='Universal ordinary-input constant-length queue and exact13-operation initialization/transport component. No complete arithmetic controller, masks, power geometry or universal operation bound is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(path.read_text(encoding='utf-8')) == json.loads(json.dumps(result))
    print(result['status'], result['source']['operations'])
    print(result['exhaustive_loader'])
    print(result['runs'])
    print(result['all_short_scans'])

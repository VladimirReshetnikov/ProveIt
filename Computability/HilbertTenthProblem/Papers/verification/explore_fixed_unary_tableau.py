#!/usr/bin/env python3
"""Fixed unary tableau, uniform block markers, and exact cyclic input link."""
from itertools import product
from pathlib import Path
import json
import sys

import explore_marked_periodic_tm_padding as old
import explore_three_cell_period_lift as blocks

OUT = Path(__file__).with_suffix('.json')
PHASES = ('L', 'I', 'Q', 'R')
PAIRS = {('L', 'L'), ('L', 'I'), ('I', 'I'), ('I', 'Q'), ('Q', 'R'), ('R', 'R')}


def phase_payload(phase, machine):
    return (0, None) if phase in ('L', 'R') else (1, machine.start if phase == 'Q' else None)


def local_valid(center, at, machine):
    v, h, payload, phase = center
    if v not in (0, 1) or h not in (0, 1):
        return False
    left, right, down, up = at(-1, 0), at(1, 0), at(0, -1), at(0, 1)
    if v != up[0] or h != right[1] or (v and right[0]) or (h and up[1]):
        return False
    if v or h:
        return payload is None and phase is None
    if payload is None or payload[0] not in machine.alphabet:
        return False
    if payload[1] is not None and payload[1] not in machine.states:
        return False
    if down[1]:
        if phase not in PHASES or (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase, right[3]) not in PAIRS:
            return False
        if payload != phase_payload(phase, machine):
            return False
    elif phase is not None:
        return False
    symbol, state = payload
    if up[1] and state is not None and state != machine.halt:
        return False
    if state is not None:
        move = machine.delta(state, symbol)[2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        blank = (machine.blank, None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = old.next_payload(blank if left[0] else left[2], payload,
                                    blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def predicate(machine):
    return lambda window: local_valid(window[4], lambda dx, dy: window[(dy+1)*3+dx+1], machine)


def fixed_markers(machine):
    q1, written, move = machine.delta(machine.start, 1)
    assert written == 2 and move == -1 and q1 not in (machine.start, machine.halt)
    H = old.tile(0, 1)
    cell = lambda symbol, head=None, phase=None: old.tile(0, 0, (symbol, head), phase)
    S = (H, H, H, cell(1, phase='I'), cell(1, machine.start, 'Q'), cell(0, phase='R'),
         cell(1, q1), cell(2), cell(0))
    E = (H, H, H, cell(0, phase='L'), cell(1, phase='I'), cell(1, phase='I'),
         cell(0), cell(1), cell(1))
    return S, E


def residue_machine(modulus, residue):
    """Halts exactly when unary length is residue modulo modulus."""
    states = ('q0',) + tuple(f's{j}' for j in range(modulus)) + ('loop', 'H')
    alphabet = (0, 1, 2)
    transitions = {(q, a): ('loop', a, 0) for q in states for a in alphabet}
    transitions['q0', 1] = ('s0', 2, -1)
    for j in range(modulus):
        transitions[f's{j}', 1] = (f's{(j+1)%modulus}', 1, -1)
        transitions[f's{j}', 0] = ('H' if (j+1)%modulus == residue else 'loop', 0, 0)
    for a in alphabet:
        transitions['H', a] = ('H', a, 0)
    return old.Machine(states, alphabet, 'q0', 'H', 0, transitions)


def history_for(machine, t, limit=100):
    tape = {-j: 1 for j in range(t+1)}
    head, state = 0, machine.start
    history = []
    for _ in range(limit+1):
        history.append((dict(tape), head, state))
        assert head <= 0
        if state == machine.halt:
            break
        state, symbol, move = machine.delta(state, tape.get(head, 0))
        tape[head] = symbol
        head += move
    return history


def thresholds(history, t):
    e = min(head for _, head, _ in history)
    a = max(2, 1-e-t)
    return a+t+4, max(3, len(history)+1)


def build_torus(machine, t, history, width, height):
    wmin, hmin = thresholds(history, t)
    assert width >= wmin and height >= hmin
    start = width-3
    result = []
    for y in range(height):
        row = []
        for x in range(width):
            if not x or not y:
                row.append(old.tile(int(x == 0), int(y == 0)))
                continue
            tape, head, state = history[min(y-1, len(history)-1)]
            native = x-start
            payload = (tape.get(native, 0), state if native == head else None)
            phase = None
            if y == 1:
                phase = 'L' if native < -t else 'I' if native < 0 else 'Q' if native == 0 else 'R'
            row.append(old.tile(0, 0, payload, phase))
        result.append(row)
    return result


def verify_phases():
    cases = accepted = 0
    for length in range(1, 9):
        actual = set()
        for row in product(PHASES, repeat=length):
            if row[0] == 'L' and row[-1] == 'R' and all(pair in PAIRS for pair in zip(row, row[1:])):
                actual.add(row)
            cases += 1
        expected = {('L',)*a+('I',)*t+('Q',)+('R',)*b
                    for a in range(1, length) for t in range(1, length) for b in range(1, length)
                    if a+t+1+b == length}
        assert actual == expected
        accepted += len(actual)
    # A Q cannot occur in any boundary-free periodic phase row.
    cyclic = 0
    for length in range(1, 7):
        for row in product(PHASES, repeat=length):
            if all((row[i], row[(i+1)%length]) in PAIRS for i in range(length)):
                assert len(set(row)) == 1 and row[0] in ('L', 'I', 'R')
            cyclic += 1
    return dict(paths=cases,valid_paths=accepted,periodic_phase_rows=cyclic)


def verify_examples():
    padded = cyclic = uniform_start = uniform_endpoint = rejected = mutations = 0
    records = []
    for modulus, residue in ((1, 0), (2, 0), (3, 1), (5, 2)):
        machine = residue_machine(modulus, residue)
        S, E = fixed_markers(machine)
        pred = predicate(machine)
        assert S != E and pred(S) and pred(E)
        for t in range(1, 10):
            hist = history_for(machine, t, limit=20)
            halted = hist[-1][2] == machine.halt
            assert halted == ((t+1)%modulus == residue)
            wmin, hmin = thresholds(hist, t)
            if not halted:
                grid = build_torus(machine, t, hist, wmin, hmin)
                assert not blocks.old_valid(grid, pred)
                rejected += 1
                continue
            records.append(dict(modulus=modulus,residue=residue,input_length=t+1,steps=len(hist)-1))
            for dw, dh in product(range(3), repeat=2):
                width, height = wmin+dw, hmin+dh
                grid = build_torus(machine, t, hist, width, height)
                assert blocks.old_valid(grid, pred)
                lifted = blocks.lift(grid)
                assert blocks.new_valid(lifted, pred)
                assert sum(block == S for row in lifted for block in row) == 1
                assert lifted[1][width-3] == S
                uniform_start += 1
                if t >= 3:
                    assert lifted[1][width-3-t] == E
                    assert sum(block == E for row in lifted for block in row) == 1
                    uniform_endpoint += 1
                changed = [row[:] for row in grid]
                changed[1][width-3] = old.tile(0, 0, (0, machine.start), 'Q')
                assert not blocks.old_valid(changed, pred)
                mutations += 1
                padded += 1
            for h in range(max(wmin-1, hmin), max(wmin-1, hmin)+3):
                grid = build_torus(machine, t, hist, h+1, h)
                lifted = blocks.lift(grid)
                N = h*(h+1)
                word = [None]*N
                for y in range(h):
                    for x in range(h+1):
                        i = (-h*(x-(h-2))-(h+1)*(y-1))%N
                        assert word[i] is None
                        word[i] = lifted[y][x]
                assert word[0] == S and word.count(S) == 1 and h*t < N
                if t >= 3:
                    assert word[h*t] == E
                assert all(blocks.three_valid(word[i],word[(i-h)%N],word[(i-h-1)%N],pred)
                           for i in range(N))
                cyclic += 1
    return dict(halting_runs=records,padded_tori=padded,consecutive_cyclic_presentations=cyclic,
                uniform_start_including_short_inputs=uniform_start,uniform_endpoint_t_at_least_three=uniform_endpoint,
                rejected_nonhalting_truncations=rejected,rejected_initial_payload_mutations=mutations,
                local_rule_independent_of_input=True)


def verify_link():
    # Exhaust arbitrary mixed adjacent rectangles at the phase-row level.
    # A wrong preceding endpoint is always separated from Q by another Q.
    cases = wrong = 0
    for lengths in product(range(1, 5), repeat=3):
        for margins in ((1, 1), (2, 3), (3, 2)):
            a, b = margins
            row = []
            endpoints = []
            starts = []
            for t in lengths:
                row += ['V']+['L']*a
                endpoints.append(len(row))
                row += ['I']*t
                starts.append(len(row))
                row += ['Q']+['R']*b
            size = len(row)
            for start, own, t in zip(starts, endpoints, lengths):
                for endpoint in endpoints:
                    distance = (start-endpoint)%size
                    path = [row[(start-j)%size] for j in range(1, distance+1)]
                    if endpoint == own:
                        assert distance == t and 'Q' not in path
                    else:
                        assert 'Q' in path
                        wrong += 1
                    cases += 1
    # A concrete local-valid torus illustrates why an unqualified pin is wrong.
    machine = residue_machine(1, 0)
    t = 3
    hist = history_for(machine, t)
    width, height = thresholds(hist, t)
    grid = build_torus(machine, t, hist, width, height)
    repeated = [row*2 for row in grid]
    pred = predicate(machine)
    lifted = blocks.lift(repeated)
    S, E = fixed_markers(machine)
    assert blocks.new_valid(lifted, pred)
    assert sum(block == S for row in lifted for block in row) == 2
    start = width-3
    other_distance = width+t
    assert lifted[1][(start-other_distance)%(2*width)] == E
    assert other_distance != t
    return dict(mixed_rectangle_endpoint_cases=cases,cross_rectangle_endpoints_cross_another_start=wrong,
                concrete_repeated_torus_has_wrong_distance=other_distance,actual_input_distance=t,
                uniqueness_is_essential=True)


def verify():
    return dict(status='PASS_FIXED_UNARY_TABLEAU',phases=verify_phases(),examples=verify_examples(),
                input_identification=verify_link(),proof='../1980/EXPLORATION_FIXED_UNARY_TABLEAU.md',
                arithmetic_operation_count=None,complete_raw_input_arithmetic_certificate=False,
                scope='Fixed unary relation, two fixed lifted symbols, independent padding and unique-start cyclic input equivalence')


if __name__ == '__main__':
    result = verify()
    if sys.argv[1:] == ['--write']:
        OUT.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    else:
        assert not sys.argv[1:]
        assert result == json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'], result['examples']['padded_tori'], 'padded tori;',
          result['examples']['consecutive_cyclic_presentations'], 'cyclic presentations')

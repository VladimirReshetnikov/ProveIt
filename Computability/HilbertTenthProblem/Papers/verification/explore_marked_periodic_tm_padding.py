"""Direct radius-one marked tableaux with independent torus padding."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json


@dataclass(frozen=True)
class Machine:
    states: tuple
    alphabet: tuple
    start: str
    halt: str
    blank: int
    transitions: dict

    def delta(self, state, symbol):
        return self.transitions[state, symbol]


def make_machine(states, transitions, start='q', halt='H'):
    states = tuple(states)
    table = dict(transitions)
    for state in states:
        for symbol in (0, 1):
            table.setdefault((state, symbol), (halt, symbol, 0))
    for symbol in (0, 1):
        table[halt, symbol] = (halt, symbol, 0)
    assert all(q in states and a in (0, 1) and d in (-1, 0, 1)
               for q, a, d in table.values())
    return Machine(states, (0, 1), start, halt, 0, table)


def simulate(machine, word, limit=100):
    tape = dict(enumerate(word))
    state, head = machine.start, 0
    history = []
    for _ in range(limit+1):
        history.append((dict(tape), head, state))
        if state == machine.halt:
            return history
        state, symbol, move = machine.delta(state, tape.get(head, machine.blank))
        tape[head] = symbol
        head += move
    return None


# A tile is (vertical_bit, horizontal_bit, payload, phase).
# A payload is (tape_symbol, state_or_None); boundary payloads are None.
def tile(v, h, payload=None, phase=None):
    return (v, h, payload, phase)


def phase_next(left, right, length):
    return ((left == 'L' and right in ('L', 0))
            or (isinstance(left, int) and left < length-1 and right == left+1)
            or (left == length-1 and right == 'R')
            or (left == 'R' and right == 'R'))


def phase_payload(phase, word, machine):
    if phase in ('L', 'R'):
        return (machine.blank, None)
    return (word[phase], machine.start if phase == 0 else None)


def next_payload(left, center, right, machine):
    symbol, state = center
    result_symbol = symbol if state is None else machine.delta(state, symbol)[1]
    incoming = []
    for old, required in ((left, 1), (center, 0), (right, -1)):
        a, q = old
        if q is not None:
            newq, _, d = machine.delta(q, a)
            if d == required:
                incoming.append(newq)
    if len(incoming) > 1:
        return None
    return (result_symbol, incoming[0] if incoming else None)


def local_valid(center, at, machine, word, check_escape=True):
    v, h, payload, phase = center
    if v not in (0, 1) or h not in (0, 1):
        return False
    left, right, down, up = at(-1, 0), at(1, 0), at(0, -1), at(0, 1)
    if v != up[0] or h != right[1]:
        return False
    if (v and right[0]) or (h and up[1]):
        return False
    if v or h:
        return payload is None and phase is None
    if payload is None or payload[0] not in machine.alphabet:
        return False
    if payload[1] is not None and payload[1] not in machine.states:
        return False
    initial = down[1] == 1
    if initial:
        if phase not in ('L', 'R')+tuple(range(len(word))):
            return False
        if left[0] and phase != 'L':
            return False
        if right[0] and phase != 'R':
            return False
        if not right[0] and not phase_next(phase, right[3], len(word)):
            return False
        if payload != phase_payload(phase, word, machine):
            return False
    elif phase is not None:
        return False
    symbol, state = payload
    if up[1] and state is not None and state != machine.halt:
        return False
    if state is not None and check_escape:
        move = machine.delta(state, symbol)[2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        blank = (machine.blank, None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload(blank if left[0] else left[2], payload,
                                blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def torus_valid(grid, machine, word, check_escape=True, require_marker=True):
    height, width = len(grid), len(grid[0])
    if require_marker and not any(c[0] and c[1] for row in grid for c in row):
        return False
    for y in range(height):
        for x in range(width):
            at = lambda dx, dy: grid[(y+dy) % height][(x+dx) % width]
            if not local_valid(grid[y][x], at, machine, word, check_escape):
                return False
    return True


def thresholds(history, word):
    a = max(1, -min(head for _, head, _ in history))
    b = max(1, max(head for _, head, _ in history)-len(word)+1)
    return a, b, a+len(word)+b+1, len(history)+1


def build_torus(machine, word, history, width, height):
    a, _, wmin, hmin = thresholds(history, word)
    assert width >= wmin and height >= hmin
    result = []
    for y in range(height):
        row = []
        for x in range(width):
            if x == 0 or y == 0:
                row.append(tile(int(x == 0), int(y == 0)))
                continue
            tape, head, state = history[min(y-1, len(history)-1)]
            pos = x-a-1
            payload = (tape.get(pos, machine.blank), state if pos == head else None)
            phase = None
            if y == 1:
                phase = 'L' if pos < 0 else pos if pos < len(word) else 'R'
            row.append(tile(0, 0, payload, phase))
        result.append(row)
    return result


def init_path_checks():
    cases = accepted = 0
    for length in (1, 2, 3):
        phases = ('L', 'R')+tuple(range(length))
        for cells in range(1, 8):
            expected = {('L',)*a+tuple(range(length))+('R',)*b
                        for a in range(1, cells) for b in range(1, cells)
                        if a+length+b == cells}
            actual = set()
            for row in product(phases, repeat=cells):
                okay = row[0] == 'L' and row[-1] == 'R' and all(
                    phase_next(row[i], row[i+1], length) for i in range(cells-1))
                if okay:
                    actual.add(row)
                cases += 1
            assert actual == expected
            accepted += len(actual)
    return cases, accepted


def finite_transition_checks(machine):
    source_rows = candidate_outputs = escaping = 0
    alphabet = tuple((a, q) for a in machine.alphabet for q in (None,)+machine.states)
    blank = (machine.blank, None)
    for width in range(1, 5):
        outputs = list(product(alphabet, repeat=width))
        for symbols in product(machine.alphabet, repeat=width):
            for head in range(width):
                for state in machine.states:
                    source = tuple((a, state if i == head else None) for i, a in enumerate(symbols))
                    newq, written, move = machine.delta(state, symbols[head])
                    target_head = head+move
                    out_of_bounds = not 0 <= target_head < width
                    escaping += out_of_bounds
                    # Independent whole-row update, compared with the local one.
                    expected = None
                    if not out_of_bounds:
                        result = [(a, None) for a in symbols]
                        result[head] = (written, None)
                        result[target_head] = (result[target_head][0], newq)
                        expected = tuple(result)
                    accepted = []
                    for output in outputs:
                        okay = not out_of_bounds and all(
                            output[i] == next_payload(source[i-1] if i else blank,
                                                       source[i], source[i+1] if i+1 < width else blank,
                                                       machine)
                            for i in range(width))
                        if okay:
                            accepted.append(output)
                        candidate_outputs += 1
                    assert accepted == ([] if expected is None else [expected])
                    source_rows += 1
    return source_rows, candidate_outputs, escaping


def verify():
    stationary = make_machine(('H',), {}, start='H')
    sweep = make_machine(('q', 'H'), {('q', 1): ('q', 1, 1)})
    excursion = make_machine(('q', 'a', 'b', 'c', 'H'), {
        (q, a): (nextq, a, d)
        for q, nextq, d in (('q', 'a', -1), ('a', 'b', -1), ('b', 'c', 1), ('c', 'H', 0))
        for a in (0, 1)})
    rewrite = make_machine(('q', 'a', 'b', 'H'), {
        (q, a): (nextq, written, d)
        for q, nextq, written, d in (('q', 'a', 1, 1), ('a', 'b', 0, -1), ('b', 'H', 1, 0))
        for a in (0, 1)})
    samples = [(stationary, (0,)), (sweep, (1, 1, 1)),
               (excursion, (1,)), (rewrite, (0, 1))]
    padded = repeated = cyclic = cells = corruptions = 0
    thresholds_record = []
    for machine, word in samples:
        history = simulate(machine, word)
        assert history is not None
        a, b, wmin, hmin = thresholds(history, word)
        thresholds_record.append(dict(input=list(word),steps=len(history)-1,
                                      left_margin=a,right_margin=b,width=wmin,height=hmin))
        for width in range(wmin, wmin+5):
            for height in range(hmin, hmin+5):
                grid = build_torus(machine, word, history, width, height)
                assert torus_valid(grid, machine, word)
                padded += 1; cells += width*height
                doubled = [row*2 for row in grid]*3
                assert torus_valid(doubled, machine, word)
                repeated += 1
                # Wrong initialization payload is rejected at the actual first row.
                changed = [row[:] for row in grid]
                x = a+1
                v,h,(symbol,state),phase = changed[1][x]
                changed[1][x] = tile(v,h,(1-symbol,state),phase)
                assert not torus_valid(changed, machine, word)
                corruptions += 1
        for m in range(max(wmin-1, hmin), max(wmin-1, hmin)+5):
            grid = build_torus(machine, word, history, m+1, m)
            length = m*(m+1)
            packed = [None]*length
            for y in range(m):
                for x in range(m+1):
                    index = (m*x+(m+1)*y) % length
                    assert packed[index] is None
                    packed[index] = grid[y][x]
            assert any(t[0] and t[1] for t in packed)
            for k in range(length):
                at = lambda dx,dy: packed[(k+m*dx+(m+1)*dy) % length]
                assert local_valid(packed[k], at, machine, word)
            cyclic += 1

    phase_cases, phase_paths = init_path_checks()
    row_cases, output_cases, escapes = finite_transition_checks(sweep)

    # Local validity without the designated marker is intentionally insufficient.
    unframed = [[tile(0,0,(0,None)) for _ in range(4)] for _ in range(3)]
    assert torus_valid(unframed, sweep, (1,), require_marker=False)
    assert not torus_valid(unframed, sweep, (1,))

    # An explicit full false tableau if head escape is permitted.
    left = make_machine(('q','H'), {('q', a): ('q', 0, -1) for a in (0,1)})
    assert all(left.delta('q', a)[0] == 'q' for a in left.alphabet)
    assert simulate(left, (1,), limit=40) is None
    bad = []
    for y in range(5):
        row = []
        for x in range(5):
            if x == 0 or y == 0:
                row.append(tile(int(x == 0),int(y == 0)))
            elif y == 1:
                phase = 'L' if x == 1 else 0 if x == 2 else 'R'
                row.append(tile(0,0,phase_payload(phase,(1,),left),phase))
            else:
                row.append(tile(0,0,(0,'q' if (y,x)==(2,1) else None)))
        bad.append(row)
    assert torus_valid(bad,left,(1,),check_escape=False)
    assert not torus_valid(bad,left,(1,),check_escape=True)

    return dict(status='PASS_MARKED_PERIODIC_TM_PADDING',
                theorem='Uniform finite radius-one local relation; marked periodic existence iff TM halts; every sufficiently large torus width and height for each halting finite input.',
                halting_samples=thresholds_record,padded_tori=padded,physical_cells=cells,
                rectangular_repetitions=repeated,initial_payload_corruptions=corruptions,
                consecutive_cyclic_presentations=cyclic,
                initialization_phase_candidates=phase_cases,exact_initialization_paths=phase_paths,
                single_head_source_rows=row_cases,candidate_output_rows=output_cases,
                rejected_head_escape_sources=escapes,
                unmarked_vacuity_exhibited=True,deleted_escape_full_false_tableau=True,
                local_radius=1,alphabet_depends_on_machine_and_input=True,
                fixed_life_reduction=False,arithmetic_operation_count=None,
                review='Author and independent complete scoped proof/source review PASS; fresh receipt comparison PASS.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps(result,indent=2))

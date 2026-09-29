"""Independent exhaustive short-tape audit; does not modify author artifacts."""
import sys
from itertools import product
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'verification'))
import explore_finite_state_raw_queue as q

cases = steps = growth_left = growth_right = 0
for written in range(3):
    for move in (-1, 0, 1):
        machine = q.Machine('audit', {('s', a): ('accept', written, move) for a in range(3)})
        _, table, _ = machine.compile()
        for width in range(1, 5):
            for tape in product(range(3), repeat=width):
                for head in range(width):
                    word = tuple(q.MARKED[a] if i == head else q.PLAIN[a]
                                 for i, a in enumerate(tape)) + (q.DELIM,)
                    state = machine.start('s')
                    for index in range(width+1):
                        state, word, event = q.one_queue_step(machine, state, word, table)
                        assert word
                        assert event == ('pass' if index == width else '')
                        steps += 1
                    expected = list(tape)
                    expected[head] = written
                    expected_head = head+move
                    if expected_head < 0:
                        expected.insert(0, q.BLANK)
                        expected_head = 0
                        growth_left += 1
                    elif expected_head == width:
                        expected.append(q.BLANK)
                        growth_right += 1
                    assert q.decode_tape(word) == (expected, expected_head)
                    assert state.kind == 'drain'
                    cases += 1
assert cases == 3834
print(dict(status='PASS_INDEPENDENT_SHORT_TAPE_QUEUE_AUDIT', cases=cases,
           exact_dequeues=steps, left_growths=growth_left, right_growths=growth_right))

#!/usr/bin/env python3
"""Independent dense-tape audit of the exact calibrated blank startup.

No imports from the runtime engine, builders, or sparse-tape checker.
The complete table is parsed independently.  A dynamically grown bytearray
represents a blank two-sided tape, and every literal transition is executed.
The final whole support is compared with an explicit register-frame formula.
"""
from pathlib import Path
import argparse
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_complete_table(path):
    data = path.read_bytes()
    rows = {}
    starts = []
    for number, line in enumerate(data.decode('ascii').splitlines(), 1):
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
            continue
        if not line or line.startswith('#'):
            continue
        fields = line.split()
        require(len(fields) == 5, 'Malformed transition at line ' + str(number))
        q, b, w, direction, target = fields
        q, b, w, target = int(q), int(b), int(w), int(target)
        require(q >= 0 and target >= 0 and b in (0, 1) and w in (0, 1)
                and direction in ('L', 'R'), 'Invalid transition field')
        require((q, b) not in rows, 'Duplicate transition')
        rows[q, b] = w, (-1 if direction == 'L' else 1), target
    states = {q for q, b in rows}
    require(starts == [0] and 0 in states, 'Expected unique initial state zero')
    require(set(rows) == {(q, b) for q in states for b in (0, 1)},
            'Missing binary transition row')
    terminals = {z for w, direction, z in rows.values()} - states
    require(len(terminals) == 1, 'Expected one terminal without transition rows')
    return rows, terminals.pop(), hashlib.sha256(data).hexdigest()


def explicit_expected_frame():
    logical = [3, 0, 0, 0, 3, 0, 0, 0, 0]
    physical_positions = [6, 2, 0, 4, 3, 7, 8, 5, 1]
    physical = [None] * 9
    for logical_register, physical_position in enumerate(physical_positions):
        physical[physical_position] = logical[logical_register]
    require(all(type(value) is int and value >= 0 for value in physical),
            'Malformed explicit physical register permutation')
    # The head is at -5. The left marker is -6, the IP is all zero,
    # and the register-file header is at 176. Each B(v) block is 0 1^(v+1).
    expected = {-6, 176}
    cursor = 177
    for value in physical + [1] * 167:
        cursor += 1                  # the zero at the start of B(v)
        expected.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    require(len(expected) == 351, 'Explicit frame must contain 351 one-cells')
    return sorted(expected), dict(head=-5, left_marker=-6, register_header=176,
                                  logical_registers=logical,
                                  logical_to_physical=physical_positions,
                                  spare_count=167, spare_value=1,
                                  block_encoding='0 followed by v+1 ones',
                                  all_other_cells=0)


def audit(table_path, steps, dispatcher):
    require(type(steps) is int and steps > 0, 'A positive fixed step count is required')
    rows, halt, table_hash = read_complete_table(table_path)
    require((dispatcher, 0) in rows, 'Dispatcher is not a working state')
    # Cell coordinate zero is at array index origin. Unrepresented cells
    # are zero; growing either side introduces exactly those blank cells.
    tape = bytearray(64)
    origin = 32
    state = 0
    head = 0
    growths = 0
    for tick in range(steps):
        require(state != halt, 'Startup halted before fixed endpoint at step ' + str(tick))
        index = origin + head
        if index < 0:
            added = len(tape)
            tape[:0] = bytes(added)
            origin += added
            index += added
            growths += 1
        elif index >= len(tape):
            tape.extend(bytes(len(tape)))
            growths += 1
        require(0 <= index < len(tape), 'Tape growth did not include head')
        write, direction, state = rows[state, tape[index]]
        tape[index] = write
        head += direction
    actual = [index - origin for index, bit in enumerate(tape) if bit]
    expected, recipe = explicit_expected_frame()
    require(state == dispatcher, 'Fixed endpoint is not the specified dispatcher')
    require(head == -5, 'Fixed endpoint head is not -5')
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        raise ValueError('Entire-tape frame mismatch: missing=' + repr(missing)
                         + ', extra=' + repr(extra))
    return dict(status='INDEPENDENT_DENSE_BLANK_FRAME_PASS',
                table_sha256=table_hash, working_states=len(rows) // 2,
                transition_rows=len(rows), start=0, blank=0, initial_head=0,
                exact_steps=steps, dispatcher=state, head=head,
                one_cells=actual, one_cell_count=len(actual),
                explicit_frame=recipe,
                dense_storage=dict(allocated_cells=len(tape), growth_events=growths,
                                   minimum_coordinate=-origin,
                                   maximum_coordinate=len(tape) - origin - 1),
                scope='Fixed literal blank execution with complete finite support. '
                      'Every represented or unrepresented cell outside the explicit '
                      '351-one-cell frame is zero. No runtime engine or builder imported.',
                checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--steps', type=int, required=True)
    parser.add_argument('--dispatcher', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.table, args.steps, args.dispatcher)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'one_cells'}, indent=2))


if __name__ == '__main__':
    main()

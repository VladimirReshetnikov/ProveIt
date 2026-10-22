#!/usr/bin/env python3
"""Independent, stdlib-only audit of a finite K215 -> TM0 adapter.

This script was written for this delivery. It reads the pinned transition table
as data; it never imports or executes repository scripts. It does not attempt
to decide whether K215 eventually halts.
"""
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
PATH = ROOT / 'k215.tm'
EXPECTED = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'

def read_table():
    data = PATH.read_bytes()
    assert sha256(data).hexdigest() == EXPECTED
    rows = {}
    for line in data.decode().splitlines():
        if line.startswith('#') or not line.strip():
            continue
        q, b, w, direction, p = line.split()
        q, b, w, p = map(int, (q, b, w, p))
        assert (q, b) not in rows
        assert 0 <= q < 215 and b in (0, 1) and w in (0, 1)
        assert direction in ('L', 'R') and 0 <= p <= 215
        rows[q, b] = w, direction, p
    assert set(rows) == set(product(range(215), range(2)))
    return rows

TABLE = read_table()
HELPERS = sorted({(p, direction) for (q, b), (w, direction, p) in TABLE.items()
                  if p != 215 and w != b})
assert len(HELPERS) == 25
HELPER_INDEX = {pair: 215 + i for i, pair in enumerate(HELPERS)}

def tm0(q, b):
    """None, or (next state, 'write'/'move', value/direction)."""
    if q < 215:
        w, direction, p = TABLE[q, b]
        if p == 215:
            return None
        if w == b:
            return p, 'move', direction
        return HELPER_INDEX[p, direction], 'write', w
    p, direction = HELPERS[q - 215]
    return p, 'move', direction

def put(tape, position, value):
    tape = dict(tape)
    if value:
        tape[position] = value
    else:
        tape.pop(position, None)
    return tape

def machine_step(config):
    q, head, tape = config
    w, direction, p = TABLE[q, tape.get(head, 0)]
    return p, head + (1 if direction == 'R' else -1), put(tape, head, w)

def tm0_step(config):
    q, head, tape = config
    action = tm0(q, tape.get(head, 0))
    if action is None:
        return None
    p, kind, value = action
    if kind == 'write':
        return p, head, put(tape, head, value)
    return p, head + (1 if value == 'R' else -1), tape

def macro_step(config):
    first = tm0_step(config)
    if first is None:
        return None, 0
    if first[0] < 215:
        return first, 1
    second = tm0_step(first)
    assert second is not None and second[0] < 215
    return second, 2

def main():
    local_cases = 0
    halt_cases = 0
    for q, b, left, right in product(range(215), range(2), range(2), range(2)):
        tape = {p: v for p, v in ((-1, left), (0, b), (1, right)) if v}
        config = q, 0, tape
        original = machine_step(config)
        adapted, count = macro_step(config)
        if original[0] == 215:
            assert adapted is None and count == 0
            halt_cases += 1
        else:
            assert adapted == original
            assert count in (1, 2)
        local_cases += 1
    original = (0, 0, {})
    simulated = (0, 0, {})
    tm0_steps = 0
    for index in range(10000):
        next_original = machine_step(original)
        next_simulated, count = macro_step(simulated)
        if next_original[0] == 215:
            assert next_simulated is None
            break
        assert next_original == next_simulated
        original, simulated = next_original, next_simulated
        tm0_steps += count
    else:
        index = 10000
    adapter_rows = [dict(state=q, read=b, action=tm0(q, b))
                    for q, b in product(range(240), range(2))]
    output = ROOT / 'k215_tm0_240.json'
    output.write_text(json.dumps(dict(
        source_sha256=EXPECTED, alphabet=[0, 1], blank=0,
        states=240, initial=0, input_encoder=[0, 0], prefix=[],
        helper_targets=HELPERS, transition_rows=adapter_rows), indent=2) + '\n')
    report = dict(
        status='PASS_FINITE_TM0_ADAPTER_AUDIT', source_sha256=EXPECTED,
        source_rows=len(TABLE), working_states=215,
        halting_rows=[dict(state=q, read=b, write=w, direction=d, target=p)
                      for (q, b), (w, d, p) in TABLE.items() if p == 215],
        write_changing_rows=sum(w != b for (q, b), (w, d, p) in TABLE.items()),
        helpers=len(HELPERS), tm0_states=240, tm0_rows=len(adapter_rows),
        exhaustive_local_cases=local_cases, terminal_local_cases=halt_cases,
        blank_prefix_original_steps=index, blank_prefix_tm0_steps=tm0_steps,
        adapter_json_sha256=sha256(output.read_bytes()).hexdigest(),
        caveat='Finite checks corroborate the local simulation lemma; they do not decide eventual halting or formally certify the full Diophantine composition.')
    (ROOT / 'k215_tm0_adapter_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()

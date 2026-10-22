#!/usr/bin/env python3
"""A literal, total, one-sided normalization of the released K215 table.

No supplied repository Python module is imported.  The only external data are
the 430 lines in k215.tm, authenticated below.  The construction is a finite
table transformation.  Its halting equivalence is proved in NORMALIZATION.md.
"""
from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
K215_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
START, ERASE, RETURN, TRAP, HALT = range(5)
ALPHABET = tuple(range(10))
STATES = tuple(range(435))
# In each pair (p,n), p holds original cell j and n holds original cell -j-1.
PAIR = {(0, 0): 0, (0, 1): 3, (1, 0): 4, (1, 1): 5}
ORIGIN_PAIR = {(p, n): 6 + 2*p + n for p in (0, 1) for n in (0, 1)}
DECODE = {code: (p, n, False) for (p, n), code in PAIR.items()}
DECODE.update({code: (p, n, True) for (p, n), code in ORIGIN_PAIR.items()})


def simulation_state(q: int, side: int) -> int:
    """side=0 for original nonnegative cells, side=1 for negative cells."""
    assert 0 <= q < 215 and side in (0, 1)
    return 5 + 2*q + side


def source_table() -> dict[tuple[int, int], tuple[int, int, int]]:
    raw = (ROOT / "k215.tm").read_bytes()
    if sha256(raw).hexdigest() != K215_SHA256:
        raise ValueError("The supplied K215 table does not have the reviewed hash")
    rows = {}
    for line in raw.decode("ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        q, read, written, direction, newq = line.split()
        key = int(q), int(read)
        assert key not in rows
        rows[key] = int(newq), int(written), {"L": -1, "R": 1}[direction]
    assert set(rows) == {(q, a) for q in range(215) for a in (0, 1)}
    assert all(0 <= q <= 215 and a in (0, 1) and d in (-1, 1)
               for q, a, d in rows.values())
    return rows


@dataclass(frozen=True)
class Machine:
    states: tuple[int, ...]
    alphabet: tuple[int, ...]
    transitions: dict[tuple[int, int], tuple[int, int, int]]
    start: int = START
    halt: int = HALT
    blank: int = 0

    def delta(self, q: int, a: int) -> tuple[int, int, int]:
        return self.transitions[q, a]


def normalized_machine() -> Machine:
    old = source_table()
    table = {(q, a): (TRAP, a, 0) for q in STATES for a in ALPHABET}
    for a in ALPHABET:
        table[TRAP, a] = TRAP, a, 0
        table[HALT, a] = HALT, a, 0
    # Initially the tape is 1 on [-t,0], blank elsewhere, and the head is at 0.
    # The first step is exactly the stationary flag required by the markers.
    table[START, 1] = ERASE, 2, 0
    table[ERASE, 2] = ERASE, 2, -1
    table[ERASE, 1] = ERASE, 0, -1
    table[ERASE, 0] = RETURN, 0, 1
    table[RETURN, 0] = RETURN, 0, 1
    table[RETURN, 2] = simulation_state(0, 0), ORIGIN_PAIR[0, 0], 0
    for q in range(215):
        for side in (0, 1):
            for symbol, (p, n, origin) in DECODE.items():
                newq, written, original_move = old[q, n if side else p]
                pair = (p, written) if side else (written, n)
                new_symbol = (ORIGIN_PAIR if origin else PAIR)[pair]
                # Motion away from the origin is always physical left.
                toward_origin = (side == 0 and original_move == -1) or (
                    side == 1 and original_move == 1)
                if toward_origin and origin:
                    new_side, physical_move = 1-side, 0
                else:
                    new_side = side
                    physical_move = 1 if toward_origin else -1
                target = HALT if newq == 215 else simulation_state(newq, new_side)
                table[simulation_state(q, side), symbol] = target, new_symbol, physical_move
    assert len(table) == 4350
    return Machine(STATES, ALPHABET, table)


def fold(head: int) -> tuple[int, int]:
    """Return physical position and side of an original two-way head."""
    return (-head, 0) if head >= 0 else (head+1, 1)


def check_normalization() -> dict:
    machine, old = normalized_machine(), source_table()
    loader_checks = 0
    for t in range(1, 65):
        tape = {j: 1 for j in range(-t, 1)}
        head, q = 0, START
        for _ in range(2*t+4):
            assert head <= 0
            q, written, move = machine.delta(q, tape.get(head, 0))
            tape[head] = written
            head += move
        assert (head, q) == (0, simulation_state(0, 0))
        assert tape[0] == ORIGIN_PAIR[0, 0]
        assert all(value == 0 for place, value in tape.items() if place != 0)
        loader_checks += 1
    step_checks = 0
    for q in range(215):
        for side in (0, 1):
            for symbol, (p, n, origin) in DECODE.items():
                original_head = (0 if side == 0 else -1) if origin else (
                    2 if side == 0 else -3)
                physical_head, actual_side = fold(original_head)
                assert actual_side == side
                newq, written, move = old[q, n if side else p]
                expected_position, expected_side = fold(original_head+move)
                q2, symbol2, move2 = machine.delta(simulation_state(q, side), symbol)
                assert physical_head+move2 == expected_position
                assert q2 == (HALT if newq == 215 else simulation_state(newq, expected_side))
                p2, n2, origin2 = DECODE[symbol2]
                assert origin2 == origin
                assert (p2, n2) == ((p, written) if side else (written, n))
                step_checks += 1
    # Only simulation rows and the absorbing halt can enter HALT.
    assert all(q >= 5 or q == HALT for (q, _), (r, _, _) in machine.transitions.items()
               if r == HALT)
    return {
        "status": "PASS",
        "source_sha256": K215_SHA256,
        "source_working_states": 215,
        "source_transitions": 430,
        "normalized_total_states_including_trap_and_absorbing_halt": 435,
        "normalized_alphabet_size": 10,
        "normalized_transitions": len(machine.transitions),
        "exhaustive_local_fold_transition_cases": step_checks,
        "loader_lengths_checked": loader_checks,
        "loader_steps_formula": "2*t+4 for t+1 initial ones",
        "scope": "Finite local checks support the induction proof; they do not decide K215 halting.",
    }


if __name__ == "__main__":
    result = check_normalization()
    (ROOT / "normalization_checks.json").write_text(json.dumps(result, indent=2)+"\n")
    machine = normalized_machine()
    data = {
        "states": list(machine.states), "alphabet": list(machine.alphabet),
        "start": machine.start, "halt": machine.halt, "blank": machine.blank,
        "transitions": [[q, a, *machine.delta(q, a)] for q in STATES for a in ALPHABET],
    }
    (ROOT / "normalized_machine.json").write_text(json.dumps(data, separators=(",", ":"))+"\n")
    print(json.dumps(result, indent=2))

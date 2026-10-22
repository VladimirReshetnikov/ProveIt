#!/usr/bin/env python3
"""Exact finite local predicate for blank-input K215 helical tableaux.

The alphabet has 439 symbols. Windows are row-major, with rows at time
offsets -1,0,+1. The origin marker S is the 3x3 window around the unique
initialized head. E passes the center predicate but cannot occur in a
globally valid configuration, since it breaks vertical propagation at
its prior-time cell. No global halting claim is inferred from tests.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from verify_k215 import parse_tm, require

ALPHABET_SIZE = 439
L, Q, R, V, H = 434, 435, 436, 437, 438
HALT = 215


def normal(symbol, state=None):
    return 2*(0 if state is None else state+1) + symbol


def decode(code):
    """Return (vertical bit,horizontal bit,payload,initial phase)."""
    if not isinstance(code, int) or not 0 <= code < ALPHABET_SIZE:
        raise ValueError("Invalid alphabet code")
    if code < L:
        k, symbol = divmod(code, 2)
        return 0, 0, (symbol, None if k == 0 else k-1), None
    if code in (L, Q, R):
        return 0, 0, (0, 0 if code == Q else None), code
    return (1, 0, None, None) if code == V else (0, 1, None, None)


DECODED = tuple(decode(code) for code in range(ALPHABET_SIZE))
PHASE_PAIRS = {(L, L), (L, Q), (Q, R), (R, R)}
S = (H, H, H, L, Q, R, normal(0), normal(1), normal(0, 93))
E = (normal(0), H, normal(0), normal(0), V, H, normal(0), V, normal(0))


def table_from_rows(rows):
    table = {(q, b): (target, w, d) for q, b, w, d, target in rows}
    table[HALT, 0] = HALT, 0, 0
    table[HALT, 1] = HALT, 1, 0
    require(len(table) == 432, "Unexpected completed table size")
    return table


def next_payload(left, center, right, table):
    symbol, state = center
    output_symbol = symbol if state is None else table[state, symbol][1]
    incoming = []
    for (old_symbol, old_state), required_move in ((left, 1), (center, 0), (right, -1)):
        if old_state is not None:
            next_state, _, move = table[old_state, old_symbol]
            if move == required_move:
                incoming.append(next_state)
    if len(incoming) > 1:
        return None
    return output_symbol, incoming[0] if incoming else None


def local_valid(window, table):
    if len(window) != 9 or any(type(code) is not int or not 0 <= code < ALPHABET_SIZE for code in window):
        return False
    tiles = [DECODED[code] for code in window]
    v, h, payload, phase = tiles[4]
    left, right, prior, following = tiles[3], tiles[5], tiles[1], tiles[7]
    if v != following[0] or (v and right[0]) or (h and following[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v or h:
        return True
    if prior[1]:
        if phase not in (L, Q, R):
            return False
        if (left[0] and phase != L) or (right[0] and phase != R):
            return False
        if not right[0] and (phase, right[3]) not in PHASE_PAIRS:
            return False
    elif phase is not None:
        return False
    symbol, state = payload
    if following[1] and state is not None and state != HALT:
        return False
    if state is not None:
        move = table[state, symbol][2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not following[1]:
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload((0, None) if left[0] else left[2], payload,
                                (0, None) if right[0] else right[2], table)
        if expected is None or following[2] != expected:
            return False
    return True


def overlap(center, right, following):
    return (all(center[3*y+x+1] == right[3*y+x] for y in range(3) for x in range(2))
            and all(center[3*(y+1)+x] == following[3*y+x] for y in range(2) for x in range(3)))


def simulate(table, limit):
    tape = {}
    head = state = 0
    history = []
    for _ in range(limit+1):
        history.append((dict(tape), head, state))
        if state == HALT:
            break
        state, write, move = table[state, tape.get(head, 0)]
        tape[head] = write
        head += move
    return history


def strip(history, width, height):
    left_margin = max(1, -min(head for _, head, _ in history))
    right_margin = max(1, max(head for _, head, _ in history))
    require(width >= left_margin+right_margin+2, "Strip too narrow")
    require(height >= len(history)+1, "Strip too short")
    head_column = left_margin+1
    grid = []
    for y in range(height):
        row = [V]
        if y == 0:
            row += [H]*(width-1)
        else:
            tape, head, state = history[min(y-1, len(history)-1)]
            for x in range(1, width):
                position = x-head_column
                if y == 1:
                    row.append(L if position < 0 else Q if position == 0 else R)
                else:
                    row.append(normal(tape.get(position, 0), state if position == head else None))
        grid.append(row)
    return grid, head_column


def cyclic(grid, head_column):
    height, width = len(grid), len(grid[0])
    result = [None]*(width*height)
    for y, row in enumerate(grid):
        for x, code in enumerate(row):
            index = (-(x-head_column)-width*(y-1)) % len(result)
            require(result[index] is None, "Cyclic coordinate collision")
            result[index] = code
    require(all(code is not None for code in result), "Cyclic coordinate gap")
    return result


def lift(word, stride):
    size = len(word)
    return [tuple(word[(i-dx-stride*dy) % size] for dy in (-1, 0, 1) for dx in (-1, 0, 1))
            for i in range(size)]


def verify(rows):
    table = table_from_rows(rows)
    require(table[0, 0] == (93, 1, 1), "The fixed start block has the wrong first transition")
    require(local_valid(S, table), "S is not in the lifted alphabet")
    require(local_valid(E, table), "E is not in the lifted alphabet")
    require(DECODED[E[1]][0] != DECODED[E[4]][0], "E does not violate predecessor vertical propagation")
    # Exhaust all three possible initial phases at small strip widths.
    from itertools import product
    initial_paths = 0
    for width in range(3, 9):
        accepted = {p for p in product((L, Q, R), repeat=width)
                    if p[0] == L and p[-1] == R and all((a,b) in PHASE_PAIRS for a,b in zip(p,p[1:]))}
        intended = {(L,)*a+(Q,)+(R,)*(width-a-1) for a in range(1, width-1)}
        require(accepted == intended, "Initial phase paths are not exactly L^a Q R^b")
        initial_paths += len(accepted)
    # Two halting control machines retain exactly K215's first transition.
    controls = []
    first = dict(table)
    first[93, 0] = HALT, 0, 0
    controls.append(first)
    second = dict(table)
    second[93, 0] = 2, 1, -1
    second[2, 1] = 3, 0, -1
    second[3, 0] = HALT, 1, 1
    controls.append(second)
    checked_windows = seam_windows = presentations = 0
    for control in controls:
        history = simulate(control, 20)
        require(history[-1][2] == HALT, "Positive control failed to halt")
        min_width = max(1, -min(h for _,h,_ in history)) + max(1, max(h for _,h,_ in history)) + 2
        for dw in range(4):
            for dh in range(4):
                grid, head_column = strip(history, min_width+dw, len(history)+1+dh)
                word = cyclic(grid, head_column)
                blocks = lift(word, len(grid[0]))
                require(all(local_valid(block, control) for block in blocks), "Helical seam or interior failed")
                require(all(overlap(blocks[i], blocks[(i-1)%len(word)], blocks[(i-len(grid[0]))%len(word)])
                            for i in range(len(word))), "Window-lift overlap failed")
                require(blocks[0] == S and blocks.count(S) == 1, "S is not unique at the origin")
                require(E not in blocks, "Impossible block E occurs in a valid presentation")
                checked_windows += len(blocks)
                seam_windows += sum(block[4] == V for block in blocks)
                presentations += 1
    # A finite K215 prefix whose final state is not halted is rejected.
    history = simulate(table, 20)
    require(history[-1][2] != HALT, "Unexpected early K215 halt")
    min_width = max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
    grid, head_column = strip(history, min_width, len(history)+1)
    blocks = lift(cyclic(grid, head_column), min_width)
    require(not all(local_valid(block, table) for block in blocks), "A nonhalting truncation was accepted")
    return {
        "schema": "proveit-k215-blank-helical-check-v1",
        "alphabet_size": ALPHABET_SIZE,
        "ordinary_interiors": 434,
        "initial_phases": {"L": L, "Q": Q, "R": R},
        "boundaries": {"V": V, "H": H},
        "S": S,
        "E": E,
        "S_and_E_center_predicates": True,
        "E_excluded_by_prior_vertical_propagation": True,
        "initial_phase_paths_checked": initial_paths,
        "halting_control_presentations": presentations,
        "local_windows_and_overlaps_checked": checked_windows,
        "vertical_seam_windows_checked": seam_windows,
        "actual_K215_nonhalting_prefix_rejected_steps": 20,
        "scope": "Finite implementation checks; the general soundness/completeness argument is mathematical, not inferred from these tests.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tm", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = verify(parse_tm(args.tm.read_bytes()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()


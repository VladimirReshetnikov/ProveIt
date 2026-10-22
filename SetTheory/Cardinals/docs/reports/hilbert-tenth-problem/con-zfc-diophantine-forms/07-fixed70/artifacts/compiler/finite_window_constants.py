#!/usr/bin/env python3
"""Exact finite helical atlas and a lazy specification of fixed coefficients.

The atlas predicate is a standalone transcription of ProveIt's reviewed
helical local clauses, with attribution and source pins in NORMALIZATION.md.
Only finite local tests and a compressed exact census are executed.  The
astronomical list of windows and giant coefficient integers are not allocated.
All sums used in the coefficient recipe have fixed, explicitly bounded ranges.
"""
from __future__ import annotations

from collections import Counter
from itertools import product
from pathlib import Path
import json

from k215_one_sided import Machine, normalized_machine, START, HALT

ROOT = Path(__file__).resolve().parent
PHASES = ("L", "I", "Q", "R")
PAIRS = {("L", "L"), ("L", "I"), ("I", "I"), ("I", "Q"),
         ("Q", "R"), ("R", "R")}


def tile(v, h, payload=None, phase=None):
    return v, h, payload, phase


V, H = tile(1, 0), tile(0, 1)


def phase_payload(phase, machine):
    return (0, None) if phase in ("L", "R") else (
        1, machine.start if phase == "Q" else None)


def alphabet(machine):
    ordinary = tuple(tile(0, 0, (s, q))
                     for s in machine.alphabet for q in (None,)+machine.states)
    initial = tuple(tile(0, 0, phase_payload(p, machine), p) for p in PHASES)
    result = (V, H)+ordinary+initial
    assert len(result) == len(set(result))
    return result


def next_payload(left, center, right, machine):
    symbol, state = center
    out_symbol = symbol if state is None else machine.delta(state, symbol)[1]
    incoming = []
    for old, required in ((left, 1), (center, 0), (right, -1)):
        a, q = old
        if q is not None:
            r, _, d = machine.delta(q, a)
            if d == required:
                incoming.append(r)
    return None if len(incoming) > 1 else (
        out_symbol, incoming[0] if incoming else None)


def local_valid(center, left, right, down, up, machine):
    v, h, payload, phase = center
    if v not in (0, 1) or h not in (0, 1):
        return False
    if v != up[0] or (v and right[0]) or (h and up[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v:
        return h == 0 and payload is None and phase is None
    if h:
        return payload is None and phase is None
    if payload is None or payload[0] not in machine.alphabet:
        return False
    if payload[1] is not None and payload[1] not in machine.states:
        return False
    if down[1]:
        if phase not in PHASES or (left[0] and phase != "L") or (
                right[0] and phase != "R"):
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
        if (not left[0] and left[2] is None) or (
                not right[0] and right[2] is None):
            return False
        blank = machine.blank, None
        expected = next_payload(blank if left[0] else left[2], payload,
                                blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def window_valid(window, machine):
    return local_valid(window[4], window[3], window[5], window[1], window[7], machine)


def fixed_markers(machine):
    q1, written, move = machine.delta(machine.start, 1)
    assert (written, move) == (2, 0) and q1 not in (machine.start, machine.halt)
    cell = lambda symbol, head=None, phase=None: tile(0, 0, (symbol, head), phase)
    start = (H, H, H, cell(1, phase="I"), cell(1, phase="I"),
             cell(1, machine.start, "Q"), cell(1), cell(1), cell(2, q1))
    end = (H, H, H, cell(0, phase="L"), cell(1, phase="I"),
           cell(1, phase="I"), cell(0), cell(1), cell(1))
    assert start != end and window_valid(start, machine) and window_valid(end, machine)
    return start, end


def allowed_windows(machine):
    """The exact finite sequence: Start, End, then all other windows in order.

    Intended as a mathematical definition/streaming reference, not the routine
    run by the census.  It terminates after at most a^9 predicate calls.
    """
    tiles = alphabet(machine)
    ids = {t: i for i, t in enumerate(tiles)}
    markers = tuple(tuple(ids[t] for t in w) for w in fixed_markers(machine))
    yield from markers
    for indices in product(range(len(tiles)), repeat=9):
        if indices not in markers and window_valid(tuple(tiles[j] for j in indices), machine):
            yield indices


def _incoming(cells, required, machine):
    """Counts by incoming state; None means no incoming head."""
    result = Counter()
    for cell in cells:
        if cell == V:
            result[None] += 1
        else:
            a, q = cell[2]
            if q is not None and machine.delta(q, a)[2] == required:
                result[machine.delta(q, a)[0]] += 1
            else:
                result[None] += 1
    return result


def count_crosses(machine):
    """Exact factorized sum of the five-cell predicate, with category counts.

    For nonboundary centers the left and right contributions are partitioned
    by whether they send a head toward the center.  At most one incoming head
    is allowed; matching up tiles are counted by their payload multiplicity.
    This is a finite partition of the literal predicate, not a statistical
    estimate.  Its implementation is exhaustively compared on a small fixture.
    """
    tiles = alphabet(machine)
    a = len(tiles)
    ordinary = [t for t in tiles if t[2] is not None and t[3] is None]
    initial = [t for t in tiles if t[3] is not None]
    non_h = [t for t in tiles if t != H]
    multiplicity = Counter(t[2] for t in tiles if t[2] is not None)
    summaries = {
        (required, no_v): _incoming([t for t in non_h if not (no_v and t == V)],
                                   required, machine)
        for required in (-1, 1) for no_v in (False, True)
    }

    def update_count(center, left, right):
        a0, q = center[2]
        r, written, move = machine.delta(q, a0) if q is not None else (None, a0, None)
        l0, r0 = left[None], right[None]
        if q is not None and move == 0:
            return l0*r0*multiplicity[written, r]
        answer = l0*r0*multiplicity[written, None]
        answer += r0*sum(count*multiplicity[written, state]
                         for state, count in left.items() if state is not None)
        answer += l0*sum(count*multiplicity[written, state]
                         for state, count in right.items() if state is not None)
        return answer

    ordinary_updates = ordinary_end = 0
    for center in ordinary:
        symbol, q = center[2]
        move = machine.delta(q, symbol)[2] if q is not None else None
        left = summaries[1, move == -1]
        right = summaries[-1, move == 1]
        ordinary_updates += (a-1)*update_count(center, left, right)
        if q is None or q == machine.halt:
            # In our normalizer halt is absorbing; the formula also respects
            # arbitrary final-step movements for a general fixture.
            lcount = a-int(move == -1)
            rcount = a-1-int(move == 1)
            ordinary_end += (a-1)*lcount*rcount
    initial_updates = initial_end = 0
    for center in initial:
        symbol, q = center[2]
        phase = center[3]
        move = machine.delta(q, symbol)[2] if q is not None else None
        left_cells = [t for t in non_h if not (t == V and (phase != "L" or move == -1))]
        right_cells = [t for t in tiles if (
            (t == V and phase == "R" and move != 1) or
            (t[3] is not None and (phase, t[3]) in PAIRS))]
        initial_updates += update_count(center, _incoming(left_cells, 1, machine),
                                        _incoming(right_cells, -1, machine))
        if q is None or q == machine.halt:
            lcount = a-int(phase != "L" or move == -1)
            initial_end += lcount*len(right_cells)
    categories = {
        "V_centers": a*a*(a-1),
        "H_centers": 2*a*a*(a-2),
        "ordinary_update_centers": ordinary_updates,
        "ordinary_final_centers": ordinary_end,
        "initial_update_centers": initial_updates,
        "initial_final_centers": initial_end,
    }
    return sum(categories.values()), categories


def small_fixture_check():
    """Directly sum every five-cell cross for two 18-tile fixtures.

    The second fixture exercises both motion directions, boundary exclusion,
    and competing incoming heads; the first agrees with the repository's
    independent rejecting-machine census.
    """
    states, symbols = (0, 1, 2), (0, 1, 2)
    transition = {(q, s): (2 if q == 2 else 1, s, 0)
                  for q in states for s in symbols}
    transition[0, 1] = 1, 2, 0
    machine = Machine(states, symbols, transition, start=0, halt=2, blank=0)
    mixed = dict(transition)
    mixed[0, 0], mixed[0, 2] = (1, 1, 1), (1, 0, -1)
    mixed[1, 0], mixed[1, 1], mixed[1, 2] = (1, 1, -1), (2, 0, 1), (1, 2, 0)
    machines = (machine, Machine(states, symbols, mixed, start=0, halt=2, blank=0))
    results = []
    for index, fixture in enumerate(machines):
        tiles = alphabet(fixture)
        direct = sum(local_valid(c, l, r, d, u, fixture)
                     for c, l, r, d, u in product(tiles, repeat=5))
        compressed, _ = count_crosses(fixture)
        assert direct == compressed
        if index == 0:
            assert direct == 121165
        results.append({"fixture": "stationary" if index == 0 else "mixed_motion",
            "tiles": len(tiles), "direct_five_crosses_checked": len(tiles)**5,
            "accepted_crosses": direct, "compressed_count_agrees": True})
    return results


def next_five_power(n):
    value = 1
    while value < n:
        value *= 5
    return value


def compact_layout(k, a):
    """Exact scalar layout of the existing modified75 window compiler.

    For this enormous alphabet the mask mu determines the radix bound.  The
    two explicit inequalities below prove this before b is chosen.  Powers
    whose exponents are enormous remain mathematical fixed numerals.
    """
    ell = max(2, (k+1).bit_length())
    h0 = 9*a+4
    m0 = 2*ell+30*a+8
    padding = max(0, (k+9*a+4-m0+1)//2)
    m = m0+2*padding
    dummy_count = m+1-k-9*a-4
    assert dummy_count >= 1
    e_star = k+12*a
    U = m+6*a-3
    Emax = 27*U
    Hshift = 51*U+3*a+1
    T1, T2 = 105*U+4*a+2, 159*U+4*a+3
    g = 186*U+4*a+4
    L = next_five_power(213*U+4*a+5)
    h_mu = h0+padding
    coefficient_mass_bits = ell*h0+(14*k+9*a+5).bit_length()
    raw_margin_bits = coefficient_mass_bits+(m+3).bit_length()+4
    assert ell*h_mu+1 > raw_margin_bits
    target_bit_length = ell*h_mu+2
    b = next_five_power(target_bit_length)
    d = b*L
    assert e_star+1 < Emax and g+Emax < L
    return {
        "window_count_k": k, "tile_count_a": a, "clause_base_log2_ell": ell,
        "initial_m": m0, "padding_clause_count": padding,
        "m": m, "native_position_count": m+1, "dummy_position_count": dummy_count,
        "extra_dummy_e_star": e_star, "anchor_unit_U": U,
        "maximum_position_Emax": Emax, "right_copy_shift_H": Hshift,
        "first_clause_band_T1": T1, "second_clause_band_T2": T2,
        "optional_high_degree_g": g, "radix_cell_length_L": L,
        "highest_mu_clause_exponent": h_mu,
        "coefficient_mass_strict_upper_log2": coefficient_mass_bits,
        "raw_margin_strict_upper_log2": raw_margin_bits,
        "radix_target_bit_length": target_bit_length,
        "inner_bits_b": b, "cell_bits_d": d,
        "endpoint_exponent_2d_plus_b": 2*d+b,
        "ordinary_input": 1, "helical_marker_distance": 2,
        "I_run_length": 3, "initial_unary_ones": 4,
        "all_huge_powers_are_fixed_numerals": True,
    }


def main():
    fixture = small_fixture_check()
    machine = normalized_machine()
    tiles = alphabet(machine)
    crosses, categories = count_crosses(machine)
    a = len(tiles)
    k = crosses*a**4
    ids = {t: i for i, t in enumerate(tiles)}
    markers = [list(ids[t] for t in w) for w in fixed_markers(machine)]
    result = {
        "status": "PASS_EXACT_COMPRESSED_CENSUS",
        "normalizer_total_states": len(machine.states),
        "normalizer_symbols": len(machine.alphabet),
        "atlas_tile_count": a,
        "accepted_five_cell_cross_count": crosses,
        "cross_categories": categories,
        "free_corner_count": a**4,
        "allowed_window_count": k,
        "start_window_tile_ids": markers[0], "end_window_tile_ids": markers[1],
        "ordering": "Start, End, then lexicographic tile-id 9-tuples passing local_valid, excluding these two.",
        "small_exhaustive_census_check": fixture,
        "layout": compact_layout(k, a),
        "scope": "Full K215 windows and giant integer constants are specified exactly but not materialized.",
    }
    (ROOT / "compiler_metadata.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact, compressed fixed-program coefficients for the K215 Diophantine slice.

Standard library only. This file supplies a literal folded machine, its exact
radius-one tableau predicate, an exact finite window enumeration, and six
integer coefficient recipes. The coefficients have astronomically many bits;
the default command emits their recipes and finite layout integers, never an
expanded numeral, computation history or purported Diophantine witness.

The generic arithmetic/compiler correctness theorem is an inherited theorem
of ProveIt, not established by the finite checks in this file. See COMPILER.md.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

PIN = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
TABLE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
PHASES = ('L', 'I', 'Q', 'R')
PHASE_PAIRS = {('L', 'L'), ('L', 'I'), ('I', 'I'), ('I', 'Q'), ('Q', 'R'), ('R', 'R')}
PAIRS = {0: (0, 0), 1: (0, 1), 4: (1, 0), 5: (1, 1)}
PAIR_CODES = {v: k for k, v in PAIRS.items()}


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Machine:
    states: tuple[str, ...]
    alphabet: tuple[int, ...]
    start: str
    halt: str
    blank: int
    transitions: dict[tuple[str, int], tuple[str, int, int]]

    def delta(self, state, symbol):
        return self.transitions[state, symbol]


def read_table(path):
    raw = Path(path).read_bytes()
    require(sha256(raw).hexdigest() == TABLE_SHA256, 'K215 table SHA-256 mismatch')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, a, b, direction, nextq = line.split()
        key = (int(q), int(a))
        require(key not in table, 'duplicate transition')
        table[key] = (int(nextq), int(b), -1 if direction == 'L' else 1)
        require(direction in ('L', 'R'), 'invalid direction')
    require(set(table) == set(product(range(215), (0, 1))), 'not the complete 430-row table')
    require(all(0 <= q <= 215 and a in (0, 1) and d in (-1, 1)
                for q, a, d in table.values()), 'invalid transition target')
    return table


def folded_machine(table):
    """Ignore the unary input, erase it, then simulate K215 on a folded tape.

    At physical position -n, n>0, a pair contains original cells +n and -n.
    Physical position 0 has symbol 2 or 3 encoding original bit 0 or 1.
    States pQ/mQ select the positive/negative track. At physical position 0
    either side state is admissible; the next original direction chooses it.
    """
    states = ('start', 'enter', 'erase', 'return', 'dead', 'halt') + tuple(
        f'{side}{q}' for side in ('p', 'm') for q in range(215))
    alphabet = tuple(range(6))
    transitions = {(q, a): ('dead', a, 0) for q, a in product(states, alphabet)}
    transitions['start', 1] = ('enter', 2, 0)
    transitions['enter', 2] = ('erase', 2, -1)
    transitions['erase', 1] = ('erase', 0, -1)
    transitions['erase', 0] = ('return', 0, 1)
    transitions['return', 0] = ('return', 0, 1)
    transitions['return', 2] = ('p0', 2, 0)
    for a in alphabet:
        transitions['dead', a] = ('dead', a, 0)
        transitions['halt', a] = ('halt', a, 0)
    for side, q in product(('p', 'm'), range(215)):
        state = f'{side}{q}'
        for symbol, pair in PAIRS.items():
            component = 0 if side == 'p' else 1
            nq, written, direction = table[q, pair[component]]
            newpair = list(pair)
            newpair[component] = written
            newstate = 'halt' if nq == 215 else f'{side}{nq}'
            move = -direction if side == 'p' else direction
            transitions[state, symbol] = (newstate, PAIR_CODES[tuple(newpair)], move)
        for origin_bit in (0, 1):
            nq, written, direction = table[q, origin_bit]
            newside = 'p' if direction == 1 else 'm'
            newstate = 'halt' if nq == 215 else f'{newside}{nq}'
            transitions[state, 2 + origin_bit] = (newstate, 2 + written, -1)
    return Machine(states, alphabet, 'start', 'halt', 0, transitions)


def phase_payload(phase, machine):
    return (0, None) if phase in ('L', 'R') else (1, machine.start if phase == 'Q' else None)


def tiles(machine):
    # Order is part of the fixed coefficient recipe.
    boundaries = ((1, 0, None, None), (0, 1, None, None))
    ordinary = tuple((0, 0, (a, q), None)
                     for a, q in product(machine.alphabet, (None,) + machine.states))
    initial = tuple((0, 0, phase_payload(p, machine), p) for p in PHASES)
    return boundaries + ordinary + initial


def next_payload(left, center, right, machine):
    symbol, state = center
    written = symbol if state is None else machine.delta(state, symbol)[1]
    incoming = []
    for (a, q), direction in ((left, 1), (center, 0), (right, -1)):
        if q is not None:
            nq, _, d = machine.delta(q, a)
            if d == direction:
                incoming.append(nq)
    return None if len(incoming) > 1 else (written, incoming[0] if incoming else None)


def local_valid(center, left, right, down, up, machine):
    """Exactly the helical radius-one rule from the pinned repository.

    The four corners of a 3x3 window do not occur in this predicate.
    """
    v, h, payload, phase = center
    if v != up[0] or (v and right[0]) or (h and up[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v:
        return h == 0 and payload is None and phase is None
    if h:
        return payload is None and phase is None
    if down[1]:
        if phase not in PHASES or (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase, right[3]) not in PHASE_PAIRS:
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
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        blank = (machine.blank, None)
        expected = next_payload(blank if left[0] else left[2], payload,
                                blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def markers(machine):
    q1, written, move = machine.delta(machine.start, 1)
    require(written == 2 and move == 0 and q1 not in (machine.start, machine.halt),
            'stationary marked first step required')
    H = (0, 1, None, None)
    cell = lambda a, q=None, phase=None: (0, 0, (a, q), phase)
    start = (H, H, H, cell(1, phase='I'), cell(1, phase='I'), cell(1, machine.start, 'Q'),
             cell(1), cell(1), cell(2, q1))
    end = (H, H, H, cell(0, phase='L'), cell(1, phase='I'), cell(1, phase='I'),
           cell(0), cell(1), cell(1))
    return start, end


def count_crosses(machine):
    """Exact count with no cross enumeration.

    A neighbor contributes either no arriving head or exactly its target
    state. A valid update has at most one arrival. Counters summarize all
    left/right choices; initial phases and boundaries are handled directly.
    This is a factorization of the finite sum of local_valid over a^5 tuples.
    """
    ts = tiles(machine)
    a = len(ts)
    payload_tiles = ts[2:]
    up_weights = Counter(t[2] for t in payload_tiles)

    def arrival(t, direction):
        if t[0] or t[2][1] is None:
            return None
        nq, _, move = machine.delta(t[2][1], t[2][0])
        return nq if move == direction else None

    common = (ts[0],) + payload_tiles
    base_left = Counter(arrival(t, 1) for t in common)
    base_right = Counter(arrival(t, -1) for t in common)
    counts = [(a - 1) * a * a, 2 * (a - 2) * a * a]
    for center in payload_tiles:
        _, _, (symbol, state), phase = center
        move = None if state is None else machine.delta(state, symbol)[2]
        written = symbol if state is None else machine.delta(state, symbol)[1]
        center_arrival = (machine.delta(state, symbol)[0]
                          if state is not None and move == 0 else None)
        exclude_left_v = (phase is not None and phase != 'L') or move == -1
        left = base_left.copy()
        left[None] -= int(exclude_left_v)
        if phase is None:
            right = base_right.copy()
            right[None] -= int(move == 1)
            right_count = a - 1 - int(move == 1)
            down_count = a - 1
        else:
            right_tiles = [t for t in payload_tiles if (phase, t[3]) in PHASE_PAIRS]
            if phase == 'R' and move != 1:
                right_tiles.append(ts[0])
            right = Counter(arrival(t, -1) for t in right_tiles)
            right_count = len(right_tiles)
            down_count = 1
        # Up=H: there is no update test; left=H is then permitted.
        halt_endings = ((a - int(exclude_left_v)) * right_count
                        if state in (None, machine.halt) else 0)
        # Up is an ordinary or initialization tile with the exact result payload.
        if center_arrival is not None:
            updates = left[None] * right[None] * up_weights[written, center_arrival]
        else:
            updates = left[None] * right[None] * up_weights[written, None]
            updates += right[None] * sum(n * up_weights[written, q]
                                        for q, n in left.items() if q is not None)
            updates += left[None] * sum(n * up_weights[written, q]
                                       for q, n in right.items() if q is not None)
        counts.append(down_count * (halt_endings + updates))
    require(len(counts) == a and min(counts) >= 0, 'cross-count shape')
    return sum(counts), counts


def crosses(machine):
    """The exact finite lexicographic enumeration used in coefficient sums.

    This deliberately simple definition is total and finite. Do not enumerate
    the K215 instance: the compressed metadata and formulas avoid that task.
    """
    ts = tiles(machine)
    for c, l, r, d, u in product(range(len(ts)), repeat=5):
        if local_valid(ts[c], ts[l], ts[r], ts[d], ts[u], machine):
            yield c, l, r, d, u


def windows(machine):
    """Start, End, then all other permitted windows in the fixed finite order."""
    ts = tiles(machine)
    ids = {t: i for i, t in enumerate(ts)}
    start, end = (tuple(ids[t] for t in w) for w in markers(machine))
    yield start
    yield end
    for c, l, r, d, u in crosses(machine):
        for nw, ne, sw, se in product(range(len(ts)), repeat=4):
            word = (nw, d, ne, l, c, r, sw, u, se)
            if word != start and word != end:
                yield word


def next_five_power(n):
    r = 1
    while r < n:
        r *= 5
    return r


def sum_inv_two_mod5(start, count):
    # 2^{-j} has period four and each full period sums to zero modulo five.
    return sum(pow(3, start + j, 5) for j in range(count % 4)) % 5


def layout(machine):
    a = len(tiles(machine))
    cross_count, by_center = count_crosses(machine)
    k = cross_count * a**4
    # Padding the clause radix is licensed by the A>k+1 condition. A=1 mod5
    # makes selector coefficient residues independent of the actual window.
    ell = 4 * ((max(2, (k + 1).bit_length()) + 3) // 4)
    h0 = 9 * a + 4
    m0 = 2 * ell + 30 * a + 8
    padding = max(0, (k + 9 * a + 4 - m0 + 1) // 2)
    h = h0 + padding
    m = m0 + 2 * padding
    dummy_count = m + 1 - k - 9 * a - 4
    dummy_first = k + 12 * a
    M = m + 6 * a - 3
    Emax = 27 * M
    H = 51 * M + 3 * a + 1
    T1 = 105 * M + 4 * a + 2
    T2 = 159 * M + 4 * a + 3
    high = 186 * M + 4 * a + 4
    L = next_five_power(213 * M + 4 * a + 5)
    # sum(c_e) <= (14k+9a+4) A^h0. This conservative power-of-five
    # rounding satisfies the exact modified75 no-carry bound without forming mu.
    mass_bits = ell * h0 + (4 * (m + 3) * (28 * k + 18 * a + 14) + 8).bit_length()
    mu_bits = ell * h + 2
    b = next_five_power(max(mass_bits, mu_bits, 4))
    d = b * L
    weighted = (4 * sum_inv_two_mod5(0, k)
                + sum_inv_two_mod5(k + 3 * a, 9 * a)
                + sum(pow(3, e, 5) for e in (M, 3 * M, 9 * M, 27 * M))) % 5
    DC0mod5 = (sum(pow(2, e, 5) for e in (3 * a, H + a, 8 * M, 24 * M))
               + (pow(2, T1, 5) + pow(2, T2, 5)) * weighted) % 5
    old_unit = (2 * DC0mod5 - pow(2, H, 5)) % 5
    correction = int(old_unit == 0)
    unit = (old_unit + correction * 2 * pow(2, high, 5)) % 5
    require(dummy_count >= 1, 'missing ignored dummy')
    require(high + Emax < L and dummy_first + 1 < Emax, 'layout separation')
    require(ell % 4 == 0 and (1 << ell) > k + 1 and unit != 0, 'clause or modular guard')
    return dict(tile_count=a, machine_states=len(machine.states), tape_symbols=len(machine.alphabet),
                valid_crosses=cross_count, windows=k, cross_counts_by_center=by_center,
                clause_radix_log2=ell, clause_radix=1 << ell, initial_clause_count=h0,
                zero_clause_padding=padding, final_clause_count=h, mask_popcount=m,
                native_positions=m + 1, dummy_positions=dummy_count, dummy_first=dummy_first,
                anchor_unit=M, Emax=Emax, H=H, T1=T1, T2=T2, high_degree=high,
                cell_radix_length=L, inner_bits=b, cell_bits=d, mu_bit_bound=mu_bits,
                raw_mass_bit_bound=mass_bits, original_unit_mod5=old_unit,
                high_correction=correction, corrected_unit_mod5=unit)


def coefficient_recipe(machine):
    data = layout(machine)
    ids = {t: i for i, t in enumerate(tiles(machine))}
    data.update(repository_commit=PIN, k215_table_sha256=TABLE_SHA256,
                start_window=[ids[t] for t in markers(machine)[0]],
                end_window=[ids[t] for t in markers(machine)[1]],
                window_order='Start, End, then lexicographic valid cross (c,l,r,d,u), '
                             'then lexicographic corners (nw,ne,sw,se), omitting the two markers',
                definitions={
                    'A': '2^ell, ell=clause_radix_log2',
                    'R': '2^b, b=inner_bits',
                    'B': '2^d, d=cell_bits=b*L',
                    'j(r,c,s)': '1+(3*r+c)*a+s, 0<=r,c<3, 0<=s<a',
                    'e(r,c,s)': 'k+3*a+(2-r)*3*a+(2-c)*a+s',
                    'selector_coefficient(i)': '1+sum_{r,c=0..2} A^j(r,c,window(i)[3*r+c])'
                                               '+sum_{j=9*a+1..9*a+4} A^j',
                    'copy_coefficient(e(r,c,s))': 'A^j(r,c,s)',
                    'anchor_coefficient(3^t*M)': 'A^(9*a+1+t), t=0,1,2,3',
                    'coefficient(dummy)': '0',
                    'E': '{0,...,k-1} union {k+3*a,...,k+12*a-1} '
                         'union {k+12*a,...,k+12*a+dummy_count-1} union {M,3*M,9*M,27*M}',
                    'mu': 'A-2+sum_{j=1..h} A^j, h=final_clause_count',
                    'DC': 'R^(3*a)+R^(H+a)+R^(8*M)+R^(24*M)'
                          '+sum_{e in E} c_e*(R^(T1-e)+R^(T2-e))+epsilon*R^g; '
                          'epsilon=high_correction, g=high_degree',
                    'DR': 'R^H',
                    'MC': 'B-1-sum_{e in E, e!=1} R^e-2*R^dummy_first',
                    'MF_native': 'mu*(R^T1+R^T2)'
                                 '+sum_{r=0..1,c=0..2,s=0..a-1} R^e(r,c,s)'
                                 '+sum_{r=0..2,c=0..1,s=0..a-1} R^(H+e(r,c,s))'
                                 '+R^(9*M)+R^(27*M)+4',
                },
                ports={'Bm1': 'B-1', 'Kconstant': 'DC+B*DR', 'twice_cell_bits': '2*d',
                       'inner_bits': 'b', 'MC': 'MC', 'MF': 'MF_native+B-1'},
                scope='Six unique fixed integers specified by finite sums with explicit bounds; '
                      'no hidden choice of an r.e. index, run length, or coefficient. '
                      'The numbers and the full window list are not materialized.')
    return data


def encode_tape(original):
    radius = max((abs(j) for j in original), default=0)
    encoded = {0: 2 + original.get(0, 0)}
    for n in range(1, radius + 1):
        encoded[-n] = PAIR_CODES[original.get(n, 0), original.get(-n, 0)]
    return encoded


def decode_tape(encoded):
    answer = {0: encoded.get(0, 2) - 2}
    for x, symbol in encoded.items():
        if x < 0:
            p, m = PAIRS[symbol]
            answer[-x], answer[x] = p, m
    return {j: v for j, v in answer.items() if v}


def verify_fold(table, machine):
    cases = 0
    for q, head, read, other in product(range(215), (-2, -1, 0, 1, 2), (0, 1), (0, 1)):
        tape = {head: read}
        if head:
            tape[-head] = other
        sides = ('p', 'm') if head == 0 else (('p',) if head > 0 else ('m',))
        for side in sides:
            encoded = encode_tape(tape)
            nq, written, direction = table[q, read]
            expected = dict(tape)
            expected[head] = written
            es, ew, em = machine.delta(f'{side}{q}', encoded.get(-abs(head), 0))
            encoded[-abs(head)] = ew
            eh = -abs(head) + em
            require(eh == -abs(head + direction), 'folded head mismatch')
            require(decode_tape(encoded) == {j: v for j, v in expected.items() if v},
                    'folded tape mismatch')
            if nq == 215:
                require(es == machine.halt, 'halting mismatch')
            else:
                require(es[1:] == str(nq), 'state mismatch')
                if head + direction:
                    require(es[0] == ('p' if head + direction > 0 else 'm'), 'side mismatch')
            cases += 1
    initialization = []
    for length in (1, 2, 3, 4, 7, 19, 64):
        tape = {-n: 1 for n in range(length)}
        state, head, steps = machine.start, 0, 0
        while state != 'p0':
            require(steps <= 2 * length + 6, 'initialization did not terminate')
            state, written, move = machine.delta(state, tape.get(head, 0))
            tape[head] = written
            head += move
            steps += 1
            require(head <= 0 and state != machine.halt, 'invalid initialization')
        require(head == 0 and decode_tape(tape) == {}, 'initial tape is not blank')
        initialization.append(dict(unary_length=length, steps=steps))
    return dict(local_fold_transition_checks=cases, initialization_checks=initialization)


def verify_counts():
    # Independent brute force matches the aggregated count on the repository's
    # 18-tile rejecting-machine fixture, including each center separately.
    states, alphabet = ('start', 'loop', 'halt'), (0, 1, 2)
    transitions = {(q, a): ('halt' if q == 'halt' else 'loop', a, 0)
                   for q, a in product(states, alphabet)}
    transitions['start', 1] = ('loop', 2, 0)
    machine = Machine(states, alphabet, 'start', 'halt', 0, transitions)
    ts = tiles(machine)
    expected_total, expected_counts = count_crosses(machine)
    actual = [0] * len(ts)
    for c, l, r, d, u in product(range(len(ts)), repeat=5):
        if local_valid(ts[c], ts[l], ts[r], ts[d], ts[u], machine):
            actual[c] += 1
    require(actual == expected_counts and sum(actual) == 121165 == expected_total,
            'aggregated cross count fails independent enumeration')
    return dict(bruteforce_crosses=len(ts)**5, valid_crosses=sum(actual),
                fixture_full_windows=sum(actual) * len(ts)**4)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=Path(__file__).with_name('k215.tm'))
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    table = read_table(args.table)
    machine = folded_machine(table)
    metadata = coefficient_recipe(machine)
    checks = verify_fold(table, machine)
    checks['cross_count_validation'] = verify_counts()
    ts = tiles(machine)
    checks['marker_validity'] = []
    for word in markers(machine):
        okay = local_valid(word[4], word[3], word[5], word[1], word[7], machine)
        require(okay, 'invalid fixed marker')
        checks['marker_validity'].append(okay)
    checks['status'] = 'PASS'
    checks['scope'] = 'Exact finite machine and layout checks; no new formal proof of compiler universality'
    args.out.mkdir(parents=True, exist_ok=True)
    transitions = [[q, a, *machine.delta(q, a)] for q, a in product(machine.states, machine.alphabet)]
    machine_json = dict(states=list(machine.states), alphabet=list(machine.alphabet),
                        start=machine.start, halt=machine.halt, blank=machine.blank, transitions=transitions)
    for name, content in [('folded_machine.json', machine_json), ('coefficient_recipe.json', metadata),
                          ('compiler_checks.json', checks)]:
        (args.out / name).write_text(json.dumps(content, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: metadata[k] for k in ('machine_states', 'tile_count', 'valid_crosses',
                                              'windows', 'clause_radix_log2', 'inner_bits',
                                              'cell_radix_length', 'cell_bits', 'high_correction')}, indent=2))
    print('PASS: folded machine, initialization, marker predicate and exact cross-count factorization')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Closed, effective numeral specification for the K215 Diophantine system.

The default writes only a finite manifest: it does NOT enumerate the enormous
window set or pretend that the astronomical coefficients have been evaluated.
--compile-sparse and --materialize are complete in-principle generators.

The compiler formulas are the exact complete76 layout with the complete75
half-binomial mask correction from ProveIt, pinned at
cdd582bec13f908df3711fa9e05d1ddac368a5db.  No package other than Python's
standard library is used.  Machine states are arbitrary distinct integers.
"""

from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import sys

COMMIT = "cdd582bec13f908df3711fa9e05d1ddac368a5db"
PHASE_PAIRS = {('L', 'L'), ('L', 'I'), ('I', 'I'),
               ('I', 'Q'), ('Q', 'R'), ('R', 'R')}


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass
class Machine:
    states: tuple
    alphabet: tuple
    start: int
    halt: int
    blank: int
    transitions: dict

    @classmethod
    def read(cls, path):
        data = json.loads(Path(path).read_text())
        table = {(q, a): (nq, w, move)
                 for q, a, nq, w, move in data['transitions']}
        obj = cls(tuple(data['states']), tuple(data['alphabet']),
                  data['start'], data['halt'], data['blank'], table)
        obj.validate()
        return obj

    def validate(self):
        require(len(set(self.states)) == len(self.states), 'duplicate state')
        require(len(set(self.alphabet)) == len(self.alphabet), 'duplicate symbol')
        require(self.blank == 0 and {0, 1, 2} <= set(self.alphabet), 'symbol convention')
        require(set(self.transitions) == set(product(self.states, self.alphabet)),
                'transition domain')
        for nq, w, move in self.transitions.values():
            require(nq in self.states and w in self.alphabet and move in (-1, 0, 1),
                    'transition codomain')
        first, written, move = self.transitions[self.start, 1]
        require(written == 2 and move == 0 and first not in (self.start, self.halt),
                'first transition must write 2, stay, and enter a new nonhalting state')
        require(all(self.transitions[self.halt, a] == (self.halt, a, 0)
                    for a in self.alphabet), 'halt must be absorbing')


def tile_alphabet(machine):
    """Exact ordered finite alphabet; tuples are (v, h, payload, phase)."""
    tiles = [(1, 0, None, None), (0, 1, None, None)]
    tiles += [(0, 0, (a, q), None)
              for a in machine.alphabet for q in (None,) + machine.states]
    tiles += [(0, 0, (0, None), 'L'), (0, 0, (1, None), 'I'),
              (0, 0, (1, machine.start), 'Q'), (0, 0, (0, None), 'R')]
    require(len(set(tiles)) == len(tiles), 'duplicate tile')
    return tuple(tiles)


def next_payload(left, center, right, machine):
    symbol, state = center
    written = symbol if state is None else machine.transitions[state, symbol][1]
    incoming = []
    for (a, q), required in ((left, 1), (center, 0), (right, -1)):
        if q is not None:
            nq, _, move = machine.transitions[q, a]
            if move == required:
                incoming.append(nq)
    return None if len(incoming) > 1 else (written, incoming[0] if incoming else None)


def local_valid(window, machine):
    """Literal helical radius-one rule; window order is bottom to top, left to right.

    Position 4 is the center. Positions 1,3,5,7 are down,left,right,up.
    This is the predicate used by the repository's complete75/76 compiler.
    Allowing a two-sided tape changes only padding in completeness, not this rule.
    """
    center, down, left, right, up = (window[j] for j in (4, 1, 3, 5, 7))
    v, h, payload, phase = center
    if v != up[0] or (v and right[0]) or (h and up[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v:
        return h == 0 and payload is None and phase is None
    if h:
        return payload is None and phase is None
    if payload is None:
        return False
    if down[1]:
        if phase not in ('L', 'I', 'Q', 'R'):
            return False
        if (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase, right[3]) not in PHASE_PAIRS:
            return False
        expected = ((0, None) if phase in ('L', 'R')
                    else (1, machine.start if phase == 'Q' else None))
        if payload != expected:
            return False
    elif phase is not None:
        return False
    symbol, state = payload
    if up[1] and state is not None and state != machine.halt:
        return False
    if state is not None:
        move = machine.transitions[state, symbol][2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        blank = (0, None)
        expected = next_payload(blank if left[0] else left[2], payload,
                                blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def markers(machine, tiles):
    lookup = {t: i for i, t in enumerate(tiles)}
    H = (0, 1, None, None)
    def cell(a, q=None, phase=None):
        return (0, 0, (a, q), phase)
    q1 = machine.transitions[machine.start, 1][0]
    start = (H, H, H, cell(1, phase='I'), cell(1, phase='I'),
             cell(1, machine.start, 'Q'), cell(1), cell(1), cell(2, q1))
    end = (H, H, H, cell(0, phase='L'), cell(1, phase='I'),
           cell(1, phase='I'), cell(0), cell(1), cell(1))
    require(local_valid(start, machine) and local_valid(end, machine), 'marker validity')
    return tuple(lookup[t] for t in start), tuple(lookup[t] for t in end)


def iter_windows(machine):
    """Exact finite enumeration: Start=0, End=1, then lexicographic remainder.

    Its run time is intentionally not hidden: a^9 tuples are inspected.
    This is an unambiguous definition of ordinary finite integer coefficients,
    not a claim that the astronomical enumeration has been executed here.
    """
    tiles = tile_alphabet(machine)
    start, end = markers(machine, tiles)
    yield start
    yield end
    for word in product(range(len(tiles)), repeat=9):
        if word != start and word != end and local_valid(tuple(tiles[i] for i in word), machine):
            yield word


def count_allowed_windows(machine):
    """Count the exact allowed windows without enumerating them.

    The four corners are free. The cross count factors the predecessor row
    according to H/non-H, and the left/right cells according to the new head
    they send into the center. Every multiplicity is an ordinary finite count.
    """
    tiles = tile_alphabet(machine)
    a = len(tiles)
    V = tiles[0]
    interior = tiles[2:]
    neighbor = (V,) + interior
    up_count = Counter(t[2] for t in interior)
    def incoming(group, direction):
        out = Counter()
        for tile in group:
            if tile[0] or tile[2][1] is None:
                out[None] += 1
            else:
                symbol, head = tile[2]
                nq, _, move = machine.transitions[head, symbol]
                out[nq if move == direction else None] += 1
        return out
    left_all, right_all = incoming(neighbor, 1), incoming(neighbor, -1)
    def update_count(payload, left, right):
        symbol, head = payload
        if head is None:
            written, own = symbol, None
        else:
            nq, written, move = machine.transitions[head, symbol]
            own = nq if move == 0 else None
        if own is not None:
            return left[None]*right[None]*up_count[written, own]
        total = left[None]*right[None]*up_count[written, None]
        total += right[None]*sum(count*up_count[written, q]
                                for q, count in left.items() if q is not None)
        total += left[None]*sum(count*up_count[written, q]
                               for q, count in right.items() if q is not None)
        return total
    # Boundary center cases. Down and left are unconstrained here.
    boundary = a*a*(a-1) + 2*a*a*(a-2)
    unphased, phased = 0, 0
    for center in interior:
        symbol, head = center[2]
        phase = center[3]
        move = 0 if head is None else machine.transitions[head, symbol][2]
        if phase is None:
            left, right = left_all.copy(), right_all.copy()
            if move == -1:
                left[None] -= 1  # forbidden escape across V
            if move == 1:
                right[None] -= 1
            local = update_count(center[2], left, right)
            if head in (None, machine.halt):
                local += a*(a-1)  # up is H: no next-payload constraint
            unphased += (a-1)*local  # down can be every tile except H
        else:
            # Down is exactly H. Right is the prescribed next phase, or V
            # when phase R. Left can be V only when phase L.
            right_group = tuple(t for t in neighbor
                                if (t[0] and phase == 'R') or
                                   (not t[0] and (phase, t[3]) in PHASE_PAIRS))
            left = left_all.copy()
            if phase != 'L':
                left[None] -= 1
            right = incoming(right_group, -1)
            local = update_count(center[2], left, right)
            if head in (None, machine.halt):
                local += (a if phase == 'L' else a-1)*len(right_group)
            phased += local
    cross = boundary+unphased+phased
    return dict(alphabet_size=a, boundary_crosses=boundary,
                unphased_crosses=unphased, phased_crosses=phased,
                allowed_crosses=cross, free_corner_factor=a**4,
                allowed_windows=cross*a**4)


def layout_scalars(machine):
    """Evaluate the enormous layout's small scalar description without its arrays.

    When padding is large, the exact radix bound is dominated by 2*mu+4.
    A rigorous upper bound on the other term proves this before returning b.
    The actual sparse-mask and center polynomials remain finite-sum definitions.
    """
    count = count_allowed_windows(machine)
    k, a = count['allowed_windows'], count['alphabet_size']
    return layout_scalars_for_counts(k, a)


def layout_scalars_for_counts(k, a):
    t = max(2, (k+1).bit_length())
    m0 = 2*t+30*a+8
    padding = max(0, (k+9*a+5-(m0+1)+1)//2)
    m = m0+2*padding
    dummy_count = m-k-9*a-3
    require(dummy_count >= 1, 'dummy scalar census')
    M0 = k+15*a+dummy_count
    H, T1, T2, g = 51*M0+3*a+1, 105*M0+4*a+2, 159*M0+4*a+3, 186*M0+4*a+4
    L = next_five_power(213*M0+4*a+5)
    J0, J = 9*a+4, 9*a+4+padding
    coefficient = 4*(m+3)*(2*k+10)+8
    mass_bit_upper = coefficient.bit_length()+t*(J0+1)
    dominates = t*J+1 >= mass_bit_upper
    result = dict(window_count=k, tile_alphabet=a, A_log2=t, zero_clause_padding=padding,
                  m=m, dummy_count=dummy_count, M0=M0, H=H, T1=T1, T2=T2, g=g,
                  L=L, mu_bit_length=t*J+1,
                  mass_target_bit_length_upper=mass_bit_upper,
                  mask_target_dominates=dominates)
    if dominates:
        b = next_five_power(t*J+2)
        result.update(b=b, d=b*L, B_log2=b*L, W0_log2=b+2*b*L,
                      exact_radix_rule='b=least power of 5 at least t*J+2')
    return result


def next_five_power(n):
    result = 1
    while result < n:
        result *= 5
    return result


def add_term(poly, exponent, coefficient):
    poly[exponent] = poly.get(exponent, 0) + coefficient


def compile_windows(windows, alphabet_size):
    """Exact sparse version of complete75_half_binomial_compiler.compile_windows.

    All integers except B,DC,DR,MC,MF remain represented as radix polynomials.
    The coefficient arrays are finite but can still be enormous.
    """
    windows = tuple(tuple(w) for w in windows)
    a, k = alphabet_size, len(windows)
    require(k >= 2 and len(set(windows)) == k, 'window enumeration')
    require(all(len(w) == 9 and all(0 <= t < a for t in w) for w in windows), 'window entries')
    A = 1 << max(2, (k + 1).bit_length())
    start = k + 3*a
    payload = {(r, c, s): start + (2-r)*3*a + (2-c)*a + s
               for r, c, s in product(range(3), range(3), range(a))}
    coeff, mu = {i: 1 for i in range(k)}, A-2
    for j, ((r, c, s), e) in enumerate(payload.items(), 1):
        power = A**j
        coeff[e] = power
        mu += power
        for i, w in enumerate(windows):
            if w[3*r+c] == s:
                coeff[i] += power
    anchor_coeff = []
    for j in range(1+9*a, 1+9*a+4):
        power = A**j
        anchor_coeff.append(power)
        mu += power
        for i in range(k):
            coeff[i] += power
    padding = 0
    m = 2*mu.bit_count() + 12*a + 2
    next_clause = 1+9*a+4
    while m+1 < k+9*a+5:
        mu += A**(next_clause+padding)
        padding += 1
        m += 2
    dummy = tuple(range(start+9*a, start+9*a+(m+1-k-9*a-4)))
    require(bool(dummy), 'missing dummy')
    old_positions = tuple(range(k)) + tuple(payload.values()) + dummy
    M0 = max(old_positions)+3*a+1
    anchors = tuple(v*M0 for v in (1, 3, 9, 27))
    positions = old_positions + anchors
    for e, value in zip(anchors, anchor_coeff):
        coeff[e] = value
    require(len(set(positions)) == len(positions) == m+1, 'position census')
    E = max(positions)
    H = E+24*M0+3*a+1
    T1 = H+2*E+a+1
    T2 = T1+2*E+1
    g = T2+E+1
    L = next_five_power(g+E+1)
    DC = {}
    for e in (3*a, H+a, 8*M0, 24*M0):
        add_term(DC, e, 1)
    for e, value in coeff.items():
        add_term(DC, T1-e, value)
        add_term(DC, T2-e, value)
    old_unit = (2*sum(c*pow(2, e, 5) for e, c in DC.items())-pow(2, H, 5)) % 5
    if old_unit == 0:
        add_term(DC, g, 1)
    unit = (2*sum(c*pow(2, e, 5) for e, c in DC.items())-pow(2, H, 5)) % 5
    require(unit != 0, 'five-adic unit')
    MF = {T1: mu, T2: mu}
    for r, c, s in product(range(2), range(3), range(a)):
        add_term(MF, payload[r, c, s], 1)
    for r, c, s in product(range(3), range(2), range(a)):
        add_term(MF, H+payload[r, c, s], 1)
    for e in anchors[2:]:
        add_term(MF, e, 1)
    require(sum(v.bit_count() for v in MF.values()) == m, 'mask census')
    # The complete75 modification uses the stronger bound, then changes MC and MF.
    mass = (len(positions)+2)*(2*sum(coeff.values())+6)
    target = max(4*mass+8, 2*mu+4, 16)
    b = next_five_power((target-1).bit_length())
    d = b*L
    extra_dummy = dummy[0]
    require(extra_dummy+1 < E, 'extra dummy separation')
    require(max(DC)+E < L and max(MF) < g, 'support separation')
    require(0 not in MF, 'low verification mask')
    MF[0] = 4
    return dict(alphabet_size=a, window_count=k, A=A, coeff=coeff, mu=mu,
                padding=padding, m=m, positions=positions, payload=payload,
                dummy=dummy, anchors=anchors, M0=M0, H=H, T1=T1, T2=T2,
                g=g, L=L, b=b, d=d, DCpoly=DC, MFpoly=MF,
                extra_dummy=extra_dummy, mass_bound=mass, unit_mod5=unit,
                high_correction=int(old_unit == 0), windows=windows)


def materialize(layout):
    """Actual finite integer constants; deliberately opt-in and potentially enormous."""
    b, d = layout['b'], layout['d']
    def evaluate(poly):
        return sum(v << (b*e) for e, v in poly.items())
    B = 1 << d
    DC, DR = evaluate(layout['DCpoly']), 1 << (b*layout['H'])
    MC = B-1-sum(1 << (b*e) for e in layout['positions'] if e != 1)
    MC -= 2 << (b*layout['extra_dummy'])
    native_MF = evaluate(layout['MFpoly'])
    return dict(B=B, Bm1=B-1, Kconstant=DC+B*DR, DC=DC, DR=DR,
                MC=MC, MF=native_MF+B-1, MF_native=native_MF,
                twice_cell_bits=2*d, inner_bits=b, W0=1 << (b+2*d),
                input_unit_constant=1-3*(1 << (b+2*d)))


def json_layout(layout):
    result = dict(layout)
    result['payload'] = [[list(k), v] for k, v in layout['payload'].items()]
    for name in ('coeff', 'DCpoly', 'MFpoly'):
        result[name] = [[e, v] for e, v in sorted(layout[name].items())]
    return result


def manifest(machine_path, machine):
    tiles = tile_alphabet(machine)
    start, end = markers(machine, tiles)
    return dict(format='closed-k215-coefficient-recipe-v1', source_commit=COMMIT,
                normalized_machine_sha256=hashlib.sha256(Path(machine_path).read_bytes()).hexdigest(),
                evaluated=dict(machine_states=len(machine.states), tape_symbols=len(machine.alphabet),
                               tile_alphabet_size=len(tiles), candidate_window_tuples=len(tiles)**9,
                               start_window=start, end_window=end),
                exact_window_count=count_allowed_windows(machine),
                exact_layout_scalars=layout_scalars(machine),
                not_evaluated=['allowed_window_list', 'sparse_compiler_arrays', 'astronomical_integer_coefficients'],
                definition=dict(windows='list(iter_windows(machine)); Start=0, End=1, remaining accepted tuples in lexicographic order',
                                layout='compile_windows(windows, len(tile_alphabet(machine)))',
                                constants='materialize(layout)',
                                fixed_input='x=1; endpoint distance y=2; W0=2^(b+2d)',
                                input_unit_constant='1-3*W0',
                                all_loops_finite=True),
                compiler_sources=['Papers/verification/explore_fixed_raw_universal_76.py',
                                  'Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py'],
                warning='This manifest defines exact finite integers; it does not claim the enormous window enumeration or coefficient expansion was executed.')


def toy_helical_test():
    # A stay-first machine that deliberately visits a positive coordinate before halting.
    states, alphabet, halt = tuple(range(5)), (0, 1, 2), 4
    table = {(q, a): (q, a, 0) for q in states for a in alphabet}
    table[0, 1] = 1, 2, 0
    table[1, 2] = 2, 2, 1
    table[2, 0] = 3, 1, -1
    table[3, 2] = 4, 0, 0
    machine = Machine(states, alphabet, 0, halt, 0, table)
    machine.validate()
    tiles = tile_alphabet(machine)
    S, E = markers(machine, tiles)
    lookup = {t: i for i, t in enumerate(tiles)}
    # Raw input y=2 has I-run u=3 and four initial ones including Q.
    u, left_margin, right_margin, height = 3, 4, 5, 9
    width = left_margin+u+right_margin+2
    Q = left_margin+u+1
    start_column = Q-1
    tape = {-j: 1 for j in range(u+1)}
    state, head, history = 0, 0, []
    for step in range(height-2):
        history.append((dict(tape), head, state))
        state, written, move = table[state, tape.get(head, 0)]
        tape[head] = written
        head += move
    grid = []
    for y in range(height):
        row = []
        for x in range(width):
            if x == 0:
                tile = (1, 0, None, None)
            elif y == 0:
                tile = (0, 1, None, None)
            else:
                tp, hp, qp = history[min(y-1, len(history)-1)]
                n = x-Q
                phase = None
                if y == 1:
                    phase = 'L' if n < -u else 'I' if n < 0 else 'Q' if n == 0 else 'R'
                tile = (0, 0, (tp.get(n, 0), qp if n == hp else None), phase)
            row.append(tile)
        grid.append(row)
    N, stride = width*height, width
    word = [None]*N
    for y, row in enumerate(grid):
        for x, tile in enumerate(row):
            idx = (-(x-start_column)-stride*(y-1)) % N
            require(word[idx] is None, 'cyclic assignment')
            word[idx] = tile
    lifted = [tuple(word[(i-dx-stride*dy) % N]
                    for dy in (-1, 0, 1) for dx in (-1, 0, 1)) for i in range(N)]
    require(all(local_valid(w, machine) for w in lifted), 'two-sided helical local rule')
    coded = [tuple(lookup[t] for t in w) for w in lifted]
    require(coded[0] == S and coded[2] == E and coded.count(S) == coded.count(E) == 1,
            'fixed marker displacement')
    # Both exact overlap relations, checked independently of local_valid.
    for i, w in enumerate(lifted):
        wr, wt = lifted[(i-1) % N], lifted[(i-stride) % N]
        require(all(w[3*r+c+1] == wr[3*r+c] for r in range(3) for c in range(2)), 'right overlap')
        require(all(w[3*(r+1)+c] == wt[3*r+c] for r in range(2) for c in range(3)), 'next overlap')
    return dict(cells=N, unique_start=1, unique_end=1, endpoint_distance=2,
                visits_positive_coordinate=True, all_local_rules=True, both_overlaps=True)


def window_count_test():
    states, alphabet = (0, 1, 2), (0, 1, 2)
    table = {(q, a): (q, a, 0) for q in states for a in alphabet}
    table.update({(0,1):(1,2,0), (1,2):(2,0,0), (1,0):(2,1,1),
                  (1,1):(0,2,-1), (0,0):(1,0,-1), (0,2):(2,1,1)})
    machine = Machine(states, alphabet, 0, 2, 0, table)
    machine.validate()
    tiles = tile_alphabet(machine)
    count = 0
    for center, left, right, up in product(tiles, repeat=4):
        for down, multiplicity in ((tiles[1], 1), (tiles[0], len(tiles)-1)):
            word = [tiles[0]]*9
            word[4], word[3], word[5], word[7], word[1] = center, left, right, up, down
            count += int(local_valid(word, machine))*multiplicity
    analytic = count_allowed_windows(machine)
    require(count == analytic['allowed_crosses'], 'cross-count formula')
    return dict(tile_alphabet=len(tiles), independent_cross_count=count,
                weighted_cross_assignments=2*len(tiles)**4, exact_formula_match=True)


def compiler_test():
    fixtures = [(((0,)*9, (1,)*9), 2),
                (((0,)*9, (0,1,0,1,0,1,0,1,0), (1,)*9), 2),
                (tuple(product(range(2), repeat=9))[:100], 2),
                (((0,)*9, (1,)*9, (2,)*9), 3),
                (tuple(product(range(2), repeat=9))[:3], 2)]
    records = []
    for windows, a in fixtures:
        cc = compile_windows(windows, a)
        scalars = layout_scalars_for_counts(len(windows), a)
        for name in ('m', 'M0', 'H', 'T1', 'T2', 'g', 'L'):
            require(scalars[name] == cc[name], 'scalar layout formula: '+name)
        require(scalars['dummy_count'] == len(cc['dummy']), 'dummy count formula')
        if scalars['mask_target_dominates']:
            require(scalars['b'] == cc['b'], 'exact dominant radix')
        # Materialize only these small compiler fixtures, never the K215 layout.
        c = materialize(cc)
        B, MC, MF = c['B'], c['MC'], c['MF_native']
        require(0 < MC < B-1 and 0 < MF < B-1, 'mask ranges')
        require(MC % 4 == 2 and MF % 8 == 4, 'low mask bits')
        require(MC.bit_count()+MF.bit_count() == cc['d'], 'mask population')
        require((2*c['DC']-c['DR']) % 5 != 0, 'numerical unit')
        records.append(dict(windows=len(windows), alphabet=a, b=cc['b'], L=cc['L'], d=cc['d'],
                            high_correction=cc['high_correction'], mask_population=cc['d'],
                            B_bit_length=B.bit_length(), materialized_fixture_only=True))
    require({r['high_correction'] for r in records} == {0, 1}, 'both compiler correction branches')
    return records


def main():
    if hasattr(sys, 'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machine', nargs='?', default=str(Path(__file__).resolve().parents[1]/'data/normalized_k215.json'))
    parser.add_argument('--output', type=Path)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--compile-sparse', type=Path,
                        help='enumerates the entire finite window set; astronomically expensive for K215')
    parser.add_argument('--materialize', type=Path,
                        help='also expands all astronomical integer coefficients; not used for delivered tests')
    args = parser.parse_args()
    machine = Machine.read(args.machine)
    data = manifest(args.machine, machine)
    if args.self_test:
        data['self_tests'] = dict(helical=toy_helical_test(), compiler=compiler_test(),
                                 window_count=window_count_test())
    if args.compile_sparse or args.materialize:
        layout = compile_windows(iter_windows(machine), len(tile_alphabet(machine)))
        if args.compile_sparse:
            args.compile_sparse.write_text(json.dumps(json_layout(layout), indent=2)+'\n')
        if args.materialize:
            # Hex avoids Python's configurable decimal-printing limit.
            args.materialize.write_text(json.dumps({k:hex(v) for k,v in materialize(layout).items()}, indent=2)+'\n')
        data['evaluated']['allowed_window_count'] = layout['window_count']
    text = json.dumps(data, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')


if __name__ == '__main__':
    main()

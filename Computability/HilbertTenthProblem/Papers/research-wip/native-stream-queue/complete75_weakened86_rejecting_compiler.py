"""An actual rejecting helical compiler slice for the86 collapse theorem.

The complete window alphabet and fixed numerals have finite exact recipes.
Only the five-cell crosses are enumerated: billions of full windows and the
astronomical compiler numerals are not materialized.
"""
import argparse
from functools import lru_cache
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import sys

VERIFY = Path(__file__).resolve().parents[2]/'verification'
sys.path.insert(0, str(VERIFY))
import explore_fixed_raw_universal_81 as semantics
import complete75_half_binomial_compiler as compiler


def rejecting_machine():
    states, alphabet = ('start', 'loop', 'halt'), (0, 1, 2)
    transitions = {(q, a): ('halt' if q == 'halt' else 'loop', a, 0)
                   for q, a in product(states, alphabet)}
    transitions['start', 1] = ('loop', 2, 0)
    return semantics.unary.old.Machine(states, alphabet, 'start', 'halt', 0, transitions)


def tiles(machine):
    tile = semantics.tile
    boundary = (tile(1, 0), tile(0, 1))
    ordinary = tuple(tile(0, 0, (s, q)) for s, q in product(machine.alphabet, (None,)+machine.states))
    initial = tuple(tile(0, 0, semantics.unary.phase_payload(phase, machine), phase)
                    for phase in semantics.unary.PHASES)
    answer = boundary+ordinary+initial
    assert len(answer) == len(set(answer)) == 18
    return answer


class WindowAlphabet:
    """Exact random access to every permitted window, with Start0 and End1."""
    def __init__(self):
        self.machine = rejecting_machine()
        self.tiles = tiles(self.machine)
        self.a = len(self.tiles)
        self.ids = {tile: i for i, tile in enumerate(self.tiles)}
        self.crosses = []
        for center, left, right, down, up in product(range(self.a), repeat=5):
            at = {(-1, 0): self.tiles[left], (1, 0): self.tiles[right],
                  (0, -1): self.tiles[down], (0, 1): self.tiles[up]}
            if semantics.helical.local_valid(self.tiles[center], lambda x, y: at[x, y], self.machine):
                self.crosses.append((center, left, right, down, up))
        self.cross_lookup = {cross: i for i, cross in enumerate(self.crosses)}
        self.corner_count = self.a**4
        self.k = len(self.crosses)*self.corner_count
        self.start, self.end = (tuple(self.ids[t] for t in word)
                               for word in semantics.fixed_markers(self.machine))
        self.marker_raw = (self.raw_rank(self.start), self.raw_rank(self.end))
        assert len(set(self.marker_raw)) == 2
        self.excluded = sorted(self.marker_raw)
        assert len(self.crosses) == 121165 and self.k == 12719417040

    def raw_window(self, index):
        assert 0 <= index < self.k
        cross_index, corner_index = divmod(index, self.corner_count)
        center, left, right, down, up = self.crosses[cross_index]
        corners = [0]*4
        for i in range(3, -1, -1):
            corner_index, corners[i] = divmod(corner_index, self.a)
        assert corner_index == 0
        return (corners[0], down, corners[1], left, center, right, corners[2], up, corners[3])

    def raw_rank(self, window):
        assert len(window) == 9 and all(0 <= t < self.a for t in window)
        c = self.cross_lookup[(window[4], window[3], window[5], window[1], window[7])]
        corners = 0
        for position in (0, 2, 6, 8):
            corners = self.a*corners+window[position]
        return c*self.corner_count+corners

    def window(self, index):
        assert 0 <= index < self.k
        if index < 2:
            return self.start if index == 0 else self.end
        raw = index-2
        for excluded in self.excluded:
            if raw >= excluded:
                raw += 1
        return self.raw_window(raw)

    def rank(self, window):
        raw = self.raw_rank(window)
        if raw == self.marker_raw[0]:
            return 0
        if raw == self.marker_raw[1]:
            return 1
        return 2+raw-sum(excluded < raw for excluded in self.excluded)


@lru_cache(maxsize=1)
def alphabet():
    return WindowAlphabet()


def machine_audit(atlas):
    machine = atlas.machine
    assert set(machine.transitions) == set(product(machine.states, machine.alphabet))
    assert machine.delta('start', 1) == ('loop', 2, 0)
    assert all(machine.delta('loop', a) == ('loop', a, 0) for a in machine.alphabet)
    assert all(machine.delta('start', a)[0] == 'loop' for a in machine.alphabet)
    assert all(machine.delta('halt', a) == ('halt', a, 0) for a in machine.alphabet)
    traces = 0
    for x in range(1, 65):
        # The doubled raw distance2x uses an I-run of length2x+1 and its Q head.
        history = semantics.unary.history_for(machine, 2*x+1, limit=5)
        assert [state for _, _, state in history] == ['start']+['loop']*5
        assert all(head == 0 for _, head, _ in history)
        assert history[1][0] == history[-1][0] and history[-1][2] != machine.halt
        traces += 1
    pred = semantics.helical.predicate(machine)
    start, end = semantics.fixed_markers(machine)
    assert pred(start) and pred(end)
    assert atlas.window(0) == atlas.start and atlas.window(1) == atlas.end
    return dict(states=list(machine.states), tape_alphabet=list(machine.alphabet),
        transitions=[[q, a, *machine.delta(q, a)] for q, a in product(machine.states, machine.alphabet)],
        exact_loop_invariant=True, semantic_input_traces=traces,
        first_transition_is_stationary_origin_mark=True, fixed_start_and_end_are_valid=True,
        ordinary_language='empty set', false_ordinary_input=1,
        theorem_basis='Every start transition enters loop, and every loop transition preserves the tape/head/state. '
                     'The unreachable halt is retained as the tableau acceptance state.')


def window_audit(atlas):
    rng = random.Random(861999)
    pred = semantics.helical.predicate(atlas.machine)
    indices = sorted({0, 1, 2, atlas.k-1, *atlas.marker_raw,
                      *[rng.randrange(atlas.k) for _ in range(1024)]})
    for i in indices:
        word = atlas.window(i)
        assert atlas.rank(word) == i and atlas.window(atlas.rank(word)) == word
        assert pred(tuple(atlas.tiles[t] for t in word))
    # Actual predicate ignores exactly the four corners in the counted decomposition.
    corner_cases = 0
    for _ in range(256):
        word = list(atlas.window(rng.randrange(atlas.k)))
        for position in (0, 2, 6, 8):
            word[position] = rng.randrange(atlas.a)
        word = tuple(word)
        assert pred(tuple(atlas.tiles[t] for t in word))
        assert atlas.window(atlas.rank(word)) == word
        corner_cases += 1
    return dict(tile_alphabet=atlas.tiles, tile_count=atlas.a,
        exhaustive_five_cell_crosses_tested=atlas.a**5, valid_five_cell_crosses=len(atlas.crosses),
        free_corner_choices=atlas.corner_count, exact_full_window_count=atlas.k,
        full_window_list_materialized=False, marker_raw_indices=list(atlas.marker_raw),
        start_window=atlas.start, end_window=atlas.end,
        cross_table_sha256=hashlib.sha256(json.dumps(atlas.crosses).encode()).hexdigest(),
        random_access_round_trips=len(indices), independent_corner_variations=corner_cases)


def layout_metadata(k, a):
    """Exact compressed quantities of the frozen compiler, without numerals."""
    clause_bits = max(2, (k+1).bit_length())
    h0 = 9*a+4
    initial_m = 2*clause_bits+30*a+8
    padding = max(0, (k+9*a+4-initial_m+1)//2)
    m = initial_m+2*padding
    dummy = m+1-k-9*a-4
    assert dummy >= 1
    extra_dummy = k+12*a
    U = m+6*a-3
    Emax, H = 27*U, 51*U+3*a+1
    T1, T2 = 105*U+4*a+2, 159*U+4*a+3
    high_degree = 186*U+4*a+4
    L = compiler.baseline.next_five_power(213*U+4*a+5)
    mu_highest = h0+padding
    # The source coefficients before dummy padding occur only through A^h0.
    # sum(coeff)<(14k+9a+5)*A^h0, with A=2^clause_bits.
    coefficient_mass_bits = clause_bits*h0+(14*k+9*a+5).bit_length()
    raw_margin_bits = coefficient_mass_bits+(m+3).bit_length()+4
    assert clause_bits*mu_highest+1 > raw_margin_bits
    # Thus 2mu+4 strictly dominates the other radix target.  Its exact
    # (target-1) bit length follows from mu=A-2+sum_(1<=j<=h) A^j.
    radix_target_bits = clause_bits*mu_highest+2
    b = compiler.baseline.next_five_power(radix_target_bits)
    d = b*L
    assert compiler.baseline.is_five_power(b) and compiler.baseline.is_five_power(L)
    assert compiler.baseline.is_five_power(d) and d % 2 and d % 3 and b % 2
    assert high_degree+Emax < L and extra_dummy+1 < Emax
    assert m%2 == 0
    return dict(window_count=k, tile_count=a, clause_radix_log2=clause_bits,
        initial_m=initial_m, zero_clause_padding=padding, m=m,
        native_positions=m+1, dummy_positions=dummy, extra_dummy=extra_dummy,
        anchor_unit=U, Emax=Emax, spatial_copy_shift=H, T1=T1, T2=T2,
        optional_high_degree=high_degree, cell_radix_length=L,
        mu_highest_clause_exponent=mu_highest,
        coefficient_sum_strict_upper_power2=coefficient_mass_bits,
        raw_radix_margin_strict_upper_power2=raw_margin_bits,
        exact_radix_target_bit_length=radix_target_bits,
        inner_bits=b, cell_bits=d, MC_even=True,
        native_MC_population=d-m-1, native_MF_population=m+1,
        total_mask_population=d,
        fixed_numerals_materialized=False,
        original_export='new_constants(compile_windows([window(i) for i in range(k)],18))',
        scope='The export is an exact finite mathematical recipe, not an executed billions-window list.')


def compiler_audit(atlas):
    # Check the closed combinatorial formulas against literal parent construction
    # on modest alphabets, using enough selectors for mu to dominate its margin.
    small = []
    for k in (1000, 1200, 1500):
        windows = list(__import__('itertools').islice(product(range(3), repeat=9), k))
        cc = compiler.compile_windows(windows, 3)
        md = layout_metadata(k, 3)
        assert (cc.m, len(cc.dummy), cc.extra_dummy, cc.anchor_unit, max(cc.positions),
                cc.H, cc.T1, cc.T2, cc.high_degree, cc.L, cc.radix_bits, cc.d) == (
                md['m'], md['dummy_positions'], md['extra_dummy'], md['anchor_unit'], md['Emax'],
                md['spatial_copy_shift'], md['T1'], md['T2'], md['optional_high_degree'],
                md['cell_radix_length'], md['inner_bits'], md['cell_bits'])
        small.append(dict(windows=k, tile_count=3, b=cc.radix_bits, L=cc.L, d=cc.d))
    actual = layout_metadata(atlas.k, atlas.a)
    assert actual['inner_bits'] == 5**17 and actual['cell_radix_length'] == 5**18
    assert actual['cell_bits'] == 5**35
    assert actual['cell_bits'] == 2910383045673370361328125
    return dict(actual_rejecting_layout=actual, literal_small_layout_matches=small,
        required_frozen_export='complete75_half_binomial_compiler.new_constants',
        new_masks=['MC=B-1-sum_(e in positions,e!=1)2^(b*e)-2^(b*extra_dummy+1)',
                   'MF=sum_e MFpoly[e]*2^(b*e)+4'],
        toy_width4_is_not_an_actual_layout=True,
        actual_program_semantics='Both markers precede the remaining allowed windows; the ordinary language is empty.')


def verify():
    import complete75_weakened86_all_input_collapse as collapse
    atlas = alphabet()
    contract = collapse.theorem_contract()
    return dict(status='PASS_ACTUAL_REJECTING_COMPILER_86_COUNTEREXAMPLE',
        arithmetic_theorem_contract=contract, machine=machine_audit(atlas),
        window_alphabet=window_audit(atlas), compiler=compiler_audit(atlas),
        conclusion='The fixed actual modified helical compiler of this rejecting machine represents the empty '
                   'ordinary-input language, but its unchanged weakened86 polynomial has full positive19-coordinate '
                   'zeros for x1 and for every positive x by the all-input-collapse theorem.',
        scope='An actual program/input counterexample by an exact finite compiler recipe and an existence theorem. '
              'No giant compiler numerals, full window list, Dirichlet prime or full witness integers are materialized. '
              'The sound75 certificate and87 polynomial are unchanged.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['conclusion'])
    print(result['scope'])

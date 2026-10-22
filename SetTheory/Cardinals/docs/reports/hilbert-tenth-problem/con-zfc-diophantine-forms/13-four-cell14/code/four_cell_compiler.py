#!/usr/bin/env python3
"""Four-cell compression of the pinned blank-K215 native compiler.

This defines finite integer recipes, not their infeasible binary expansions.
The semantic alphabet comprises (left, center, right, following) tuples.
The predecessor initialization condition is shifted forward one time step.
By default verify the vendored machine and compare the stored certificate.
Use --write to regenerate the certificate. Only finite diagnostics execute.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re

ALPHABET = 439
TILE_COUNT = 71356645
TM_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
L, Q, R, V, H = 434, 435, 436, 437, 438
HALT = 215
START = (L, Q, R, 1)
EXCLUDED = (V, V, 0, V)
SLOTS = ((1, 0), (1, 1), (1, 2), (2, 1))
VERTICAL_TARGETS = ((1, 1),)
HORIZONTAL_TARGETS = ((1, 0), (1, 1))
PHASE_PAIRS = {(L, L), (L, Q), (Q, R), (R, R)}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse_dense_table(data):
    require(hashlib.sha256(data).hexdigest() == TM_SHA256, "The exact dense K215 table hash differs")
    lines = data.decode('ascii').splitlines()
    require(lines[0] == '#! start 0', "Wrong K215 starting state")
    actions = {}
    for line in lines[1:]:
        match = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
        require(match is not None, "Malformed dense transition")
        q, read, write, direction, target = match.groups()
        q, read, write, target = map(int,(q,read,write,target))
        require(0 <= q < 215 and 0 <= target <= 215, "Dense transition out of range")
        require((q,read) not in actions, "Duplicate dense transition")
        actions[q,read] = [q,read,write,1 if direction == 'R' else -1,target]
    require(set(actions) == {(q,r) for q in range(215) for r in (0,1)}, "Incomplete dense table")
    return [actions[q,r] for q in range(215) for r in (0,1)]


def normal(symbol, state=None):
    return 2 * (0 if state is None else state + 1) + symbol


def decode(code):
    if not isinstance(code, int) or not 0 <= code < ALPHABET:
        raise ValueError("Invalid tile")
    if code < L:
        k, symbol = divmod(code, 2)
        return 0, 0, (symbol, None if k == 0 else k - 1), None
    if code in (L, Q, R):
        return 0, 0, (0, 0 if code == Q else None), code
    return (1, 0, None, None) if code == V else (0, 1, None, None)


DECODED = tuple(decode(code) for code in range(ALPHABET))


def table_from_rows(rows):
    table = {(q, b): (target, w, direction) for q, b, w, direction, target in rows}
    table[HALT, 0] = HALT, 0, 0
    table[HALT, 1] = HALT, 1, 0
    require(len(table) == 432, "Expected the completed K215 table")
    return table


def next_payload(left, center, right, table):
    symbol, state = center
    written = symbol if state is None else table[state, symbol][1]
    incoming = []
    for (old_symbol, old_state), move in ((left, 1), (center, 0), (right, -1)):
        if old_state is not None:
            target, _, direction = table[old_state, old_symbol]
            if direction == move:
                incoming.append(target)
    if len(incoming) > 1:
        return None
    return written, incoming[0] if incoming else None


def local_valid(tile, table):
    if len(tile) != 4 or any(type(c) is not int or not 0 <= c < ALPHABET for c in tile):
        return False
    left, center, right, following = (DECODED[c] for c in tile)
    v, h, payload, phase = center
    if v != following[0] or (v and right[0]) or (h and following[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v:
        return True
    if h:
        # Shift the old next-center predecessor-H condition one step earlier.
        return following[3] in (L, Q, R)
    if phase is not None:
        if (left[0] and phase != L) or (right[0] and phase != R):
            return False
        if not right[0] and (phase, right[3]) not in PHASE_PAIRS:
            return False
    symbol, state = payload
    if following[1] and state is not None and state != HALT:
        return False
    if state is not None:
        direction = table[state, symbol][2]
        if (direction == -1 and left[0]) or (direction == 1 and right[0]):
            return False
    if not following[1]:
        # The old predicate at the following center forbids an initial phase.
        if following[3] is not None:
            return False
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload((0, None) if left[0] else left[2], payload,
                                (0, None) if right[0] else right[2], table)
        if expected is None or following[2] != expected:
            return False
    return True


def overlap(center, right, following):
    return (center[2] == right[1] and center[1] == right[0]
            and center[3] == following[1])


def direct_center_count(center, table):
    v, h, payload, _ = DECODED[center]
    total = 0
    for left, right in itertools.product(range(ALPHABET), repeat=2):
        lt, rt = DECODED[left], DECODED[right]
        candidates = [V] if v else [L, Q, R] if h else [H]
        if not v and not h and (lt[0] or lt[2] is not None) and (rt[0] or rt[2] is not None):
            expected = next_payload((0, None) if lt[0] else lt[2], payload,
                                    (0, None) if rt[0] else rt[2], table)
            if expected is not None:
                candidates.append(normal(*expected))
        for following in candidates:
            total += local_valid((left, center, right, following), table)
    return total


def count_tiles(rows, direct=True):
    table = table_from_rows(rows)
    li = sum(d == 1 for _, _, _, d, _ in rows) + 1
    ri = sum(d == -1 for _, _, _, d, _ in rows)
    ln, rn = 438 - li, 438 - ri
    categories = []

    def add(name, center, multiplicity, count):
        observed = direct_center_count(center, table) if direct else None
        require(not direct or observed == count, f"Wrong count for {name}: {observed}, {count}")
        categories.append(dict(name=name, center=center, multiplicity=multiplicity,
                               per_center=count, direct_count=observed,
                               total=multiplicity * count))

    add("V", V, 1, 438 * 439)
    add("H", H, 1, 2 * 439 * 3)
    for symbol in (0, 1):
        add(f"headless-{symbol}", normal(symbol), 1,
            439 * 438 + ln * rn + li * rn + ri * ln)
        add(f"halt-{symbol}", normal(symbol, HALT), 1, 439 * 438 + ln * rn)
    for write, direction in itertools.product((0, 1), (-1, 1)):
        matching = [row for row in rows if row[2] == write and row[3] == direction]
        require(matching, "Missing transition class")
        l, r = ln - (direction == -1), rn - (direction == 1)
        q, symbol, *_ = matching[0]
        add(f"working-write{write}-move{direction}", normal(symbol, q), len(matching),
            l * r + li * r + ri * l)
    add("initial-L", L, 1, 2 * 439 + 2 * (ln + li))
    add("initial-Q", Q, 1, 437)
    add("initial-R", R, 1, 2 * 438 + 2 * (ln - 1 + li))
    require(sum(c['multiplicity'] for c in categories) == ALPHABET, "Incomplete center partition")
    count = sum(c['total'] for c in categories)
    require(count == TILE_COUNT, "Unexpected four-cell alphabet cardinality")
    return dict(tile_count=count, categories=categories, independent_direct_count=direct,
                incoming_from_left=li, incoming_from_right=ri,
                nonincoming_from_left=ln, nonincoming_from_right=rn)


def five_power_at_least(n):
    p, e = 1, 0
    while p < n:
        p *= 5
        e += 1
    return p, e


def layout(alphabet=ALPHABET, tiles=TILE_COUNT):
    a, k = alphabet, tiles
    ell = max(2, (k + 1).bit_length())
    padding = max(0, (k - 2 * ell - 7 * a - 4 + 1) // 2)
    mu_top = 4 * a + 4 + padding
    m = 2 * ell + 11 * a + 8 + 2 * padding
    count = m + 1
    dummy_count = count - k - 4 * a - 4
    require(dummy_count >= 1, "No ignored dummy")
    dummy_start = k + 12 * a
    anchor = k + 15 * a + dummy_count
    emax = 27 * anchor
    shift = emax + 24 * anchor + 3 * a + 1
    band1 = shift + 2 * emax + a + 1
    band2 = band1 + 4 * emax + 2
    cell_length, cell_exp = five_power_at_least(band2 + 2 * emax + 2)
    # Conservative inherited coefficient bound; 14 also exceeds 1+4+4.
    prefactor = 4 * (count + 2) * (28 * (k + 4 * a + 4) + 6) + 8
    threshold = max(ell * (mu_top + 1) + 3,
                    ell * (4 * a + 4) + prefactor.bit_length() + 1, 4)
    radix_bits, radix_exp = five_power_at_least(threshold)
    cell_bits = radix_bits * cell_length
    require(band2 - band1 > 2 * emax, "Clause bands overlap")
    require(cell_length - (band2 - band1) > emax, "Wrapped clause bands overlap")
    require(band2 + emax < cell_length, "Field support wraps")
    require(dummy_start + dummy_count < anchor, "Dummy reaches first anchor")
    require(cell_bits == 5 ** (radix_exp + cell_exp), "Bad power-of-five factorization")
    return dict(alphabet=a, tiles=k, ell=ell, padding=padding, mu_top=mu_top,
                m=m, native_positions=count, dummy_count=dummy_count,
                dummy_start=dummy_start, anchor_unit=anchor, emax=emax,
                shift_H=shift, T1=band1, T2=band2,
                cell_length=cell_length, cell_length_power_five=cell_exp,
                radix_bits=radix_bits, radix_bits_power_five=radix_exp,
                cell_bits=cell_bits, cell_bits_power_five=radix_exp+cell_exp,
                radix_threshold=threshold,
                mask_population_MC=cell_bits-m-1, mask_population_MF=m+1,
                bit_length_K=radix_bits*(cell_length+shift)+1)


def payload(a, k, r, c, symbol):
    return k + 3 * a + (2 - r) * 3 * a + (2 - c) * a + symbol


def toy_compiler(tiles, a):
    """Exact finite support/mask audit for nontrivial small tile alphabets."""
    g = layout(a, len(tiles))
    k, A = len(tiles), 1 << g['ell']
    coefficients = {j: 1 for j in range(k)}
    mu = A - 2
    for slot, (r, c) in enumerate(SLOTS):
        for symbol in range(a):
            power = A ** (1 + slot * a + symbol)
            e = payload(a, k, r, c, symbol)
            coefficients[e] = power
            mu += power
            for i, tile in enumerate(tiles):
                if tile[slot] == symbol:
                    coefficients[i] += power
    anchors = [g['anchor_unit'] * x for x in (1, 3, 9, 27)]
    for j, e in enumerate(anchors, 4 * a + 1):
        power = A ** j
        coefficients[e] = power
        mu += power
        for i in range(k):
            coefficients[i] += power
    for j in range(4 * a + 5, g['mu_top'] + 1):
        mu += A ** j
    dummy = list(range(g['dummy_start'], g['dummy_start'] + g['dummy_count']))
    positions = list(range(k)) + [payload(a, k, r, c, s) for (r, c), s in
                                  itertools.product(SLOTS, range(a))] + dummy + anchors
    require(len(set(positions)) == g['native_positions'], "Wrong native support census")
    require(2 * mu.bit_count() + 3 * a + 2 == g['m'], "Wrong mask population formula")
    DC, MF = {}, {}

    def add(d, e, coefficient=1):
        d[e] = d.get(e, 0) + coefficient

    for e in (3*a, g['shift_H']+a, 8*g['anchor_unit'], 24*g['anchor_unit']):
        add(DC, e)
    for e, coefficient in coefficients.items():
        add(DC, g['T1']-e, coefficient)
        add(DC, g['T2']-e, coefficient)
    for target in (g['T1'], g['T2']):
        add(MF, target, mu)
    for (r, c), s in itertools.product(VERTICAL_TARGETS, range(a)):
        add(MF, payload(a, k, r, c, s))
    for (r, c), s in itertools.product(HORIZONTAL_TARGETS, range(a)):
        add(MF, g['shift_H']+payload(a, k, r, c, s))
    for e in anchors[2:]:
        add(MF, e)
    require(sum(v.bit_count() for v in MF.values()) == g['m'], "Wrong high-mask population")
    bound = max(4*(g['native_positions']+2)*(2*sum(coefficients.values())+6)+8, 2*mu+4, 16)
    require(g['radix_bits'] >= (bound-1).bit_length(), "Radix too small")
    tests = []
    for t in (g['T1'], g['T2']):
        tests.append((t, lambda site, e: coefficients.get(e, 0) if site == 0 else 0))
    for (r, c), s in itertools.product(VERTICAL_TARGETS, range(a)):
        t, e0 = payload(a, k, r, c, s), payload(a, k, r+1, c, s)
        tests.append((t, lambda site, e, t=t, e0=e0: int(site == 0 and e == e0 or site == 2 and e == t)))
    for (r, c), s in itertools.product(HORIZONTAL_TARGETS, range(a)):
        t = g['shift_H'] + payload(a, k, r, c, s)
        e0, e1 = payload(a, k, r, c+1, s), payload(a, k, r, c, s)
        tests.append((t, lambda site, e, e0=e0, e1=e1: int(site == 0 and e == e0 or site == 1 and e == e1)))
    for t, e0 in zip(anchors[2:], anchors[:2]):
        tests.append((t, lambda site, e, t=t, e0=e0: int(site == 0 and e == e0 or site == 2 and e == t)))
    basis_checks = 0
    for site, e, (t, expected) in itertools.product(range(3), positions, tests):
        actual = DC.get(t-e, 0) if site == 0 else int(t-e == g['shift_H']) if site == 1 else int(t == e)
        require(actual == expected(site, e), "A convolution support does not match its prescribed clause")
        basis_checks += 1
    support, length = set(positions), g['cell_length']
    expanded = support | {dummy[0] + 1}
    require(not ({(g['T1']-e)%length for e in expanded} & {(g['T2']-e)%length for e in expanded}), "No uniformly clean band")
    alignments = {(anchors[2]-e)%length for e in support} & {(anchors[3]-e)%length for e in support}
    require(alignments == {0}, "Anchors permit a non-cell shift")
    unit = (2*sum(v*pow(2,e,5) for e,v in DC.items()) - pow(2,g['shift_H'],5))%5
    if a % 4 == 3:
        require(unit == 3, "Wrong uniform five-adic unit")
    return dict(alphabet=a, tiles=k, basis_checks=basis_checks, unit_mod5=unit,
                all_rotation_support_checks=True, geometry=g)


def simulate(table, limit):
    tape, head, state, history = {}, 0, 0, []
    for _ in range(limit+1):
        history.append((dict(tape), head, state))
        if state == HALT:
            break
        state, write, move = table[state, tape.get(head, 0)]
        tape[head] = write
        head += move
    return history


def cyclic_tiles(history, width, height):
    head_column = max(1, -min(h for _,h,_ in history)) + 1
    word = [None] * (width * height)
    for time in range(height):
        tape, head, state = history[min(max(0,time-1),len(history)-1)]
        for x in range(width):
            if x == 0:
                code = V
            elif time == 0:
                code = H
            elif time == 1:
                code = L if x < head_column else Q if x == head_column else R
            else:
                position = x-head_column
                code = normal(tape.get(position,0), state if position == head else None)
            index = (-(x-head_column)-width*(time-1))%len(word)
            require(word[index] is None, "Cyclic presentation collision")
            word[index] = code
    return [(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)])
            for i in range(len(word))]


def semantic_checks(rows):
    table = table_from_rows(rows)
    require(table[0,0] == (93,1,1), "Wrong literal K215 first transition")
    require(local_valid(START,table), "Start is not a legal four-cell tile")
    require(local_valid(EXCLUDED,table), "Excluded tile is not locally legal")
    require(EXCLUDED[0] == V and EXCLUDED[1] == V, "Excluded tile has no adjacent-V obstruction")
    controls = []
    one = dict(table); one[93,0] = HALT,0,0; controls.append(one)
    two = dict(table); two[93,0] = 2,1,-1; two[2,1] = 3,0,-1; two[3,0] = HALT,1,1; controls.append(two)
    presentations = windows = 0
    for control in controls:
        history = simulate(control,20)
        require(history[-1][2] == HALT, "Control did not halt")
        width = max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
        for dw,dh in itertools.product(range(4),repeat=2):
            tiles = cyclic_tiles(history,width+dw,len(history)+1+dh)
            require(all(local_valid(tile,control) for tile in tiles), "A genuine helical tableau was rejected")
            require(all(overlap(tiles[i],tiles[(i-1)%len(tiles)],tiles[(i-width-dw)%len(tiles)]) for i in range(len(tiles))), "Four-cell overlap failed")
            require(tiles[0] == START and tiles.count(START) == 1, "Canonical Start changed")
            require(EXCLUDED not in tiles, "Impossible tile in genuine tableau")
            presentations += 1; windows += len(tiles)
    history = simulate(table,20)
    require(history[-1][2] != HALT, "K215 unexpectedly halts in 20 steps")
    width = max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
    tiles = cyclic_tiles(history,width,len(history)+1)
    require(not all(local_valid(tile,table) for tile in tiles), "Nonhalting truncation accepted")
    return dict(canonical_presentations=presentations, local_and_overlap_checks=windows,
                nonhalting_truncation_rejected=True, start=START, excluded=EXCLUDED)


def specification():
    return dict(schema="proveit-k215-four-cell-constants-v1", free_parameters=[],
        machine_sha256=TM_SHA256, alphabet_size=ALPHABET, tile_count=TILE_COUNT,
        tile_order=dict(first=START, second=EXCLUDED,
            rest="lexicographic four-tuples (left,center,right,following) in range(439)^4 satisfying local_valid, excluding first and second"),
        layout=layout(),
        definitions={
            "slots":"(1,0),(1,1),(1,2),(2,1) in this order; slot index j=0,1,2,3",
            "A":"2^ell", "r":"2^radix_bits", "B":"r^cell_length=2^cell_bits",
            "e(r0,c,s)":"k+3*a+(2-r0)*3*a+(2-c)*a+s",
            "mu":"A-2+sum(A^j,j=1..mu_top)",
            "c_selector(i)":"1+sum(A^(1+j*a+tile_i[j]),j=0..3)+sum(A^(4*a+t),t=1..4)",
            "c_payload(j,s)":"A^(1+j*a+s)", "c_anchor(t)":"A^(4*a+t)", "c_dummy":"0",
            "positions":"0..k-1; payload e for four slots and s=0..a-1; dummy_start..dummy_start+dummy_count-1; M,3M,9M,27M",
            "DC":"r^(3*a)+r^(H+a)+r^(8*M)+r^(24*M)+sum(c_e*(r^(T1-e)+r^(T2-e)),e in positions)",
            "DR":"r^H",
            "MF0":"mu*(r^T1+r^T2)+sum(r^e(1,1,s),s=0..a-1)+sum(r^(H+e(r0,c,s)),(r0,c)=(1,0),(1,1),s=0..a-1)+r^(9*M)+r^(27*M)",
            "MC":"B-1-sum(r^e,e in positions except1)-2*r^dummy_start",
            "MF_native":"MF0+4", "Bm1":"B-1", "Kconstant":"DC+B*DR", "MF":"MF_native+B-1"},
        polynomial_ports=["Bm1","Kconstant","MC","MF"],
        key_certificates=dict(unit_2DC_minus_DR_mod5=3, MC_mod4=2, MF_native_mod8=4,
                              population_sum="cell_bits", bit_length_Bm1="cell_bits"),
        expansions_materialized=False)


def main():
    package = Path(__file__).resolve().parent.parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transitions',type=Path,default=package/'vendor'/'k215_transitions.json')
    parser.add_argument('--tm',type=Path,default=package/'vendor'/'k215.tm')
    parser.add_argument('--output',type=Path,default=package/'data'/'four_cell_constants.json')
    parser.add_argument('--write',action='store_true',help='Regenerate the saved certificate; default is comparison only')
    args=parser.parse_args()
    source=json.loads(args.transitions.read_text())
    require(source['source_sha256']['tm'] == TM_SHA256, "Unrecognized machine data")
    rows=parse_dense_table(args.tm.read_bytes())
    require(rows == source['transitions'], "Transition export differs from the exact dense table")
    result=dict(constants=specification(),
        machine_binding=dict(sha256=TM_SHA256,transition_count=len(rows),export_matches_dense_table=True),
        cardinality=count_tiles(rows,True),
        semantics=semantic_checks(rows),
        toy_compilers=[toy_compiler([(0,)*4,(1,)*4],3),
                       toy_compiler([(0,1,2,0),(2,0,1,2),(1,2,0,1)],3),
                       toy_compiler([(0,1,2,3),(3,2,1,0),(2,1,0,3),(1,3,2,0)],7)],
        status="PASS",
        scope="Finite data, support and semantic diagnostics supplement the parametric proofs; no giant coefficient or K215 halting witness is materialized.")
    # JSON normalization changes tuple values to their saved list representation.
    serialized=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.write:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(serialized)
    else:
        require(json.loads(args.output.read_text()) == json.loads(serialized), "Saved four-cell certificate differs")
    print(json.dumps(dict(status=result['status'],geometry=result['constants']['layout'],
                         direct_cardinality=True,mode='write' if args.write else 'compare',
                         semantics=result['semantics']),sort_keys=True))


if __name__=='__main__':
    main()

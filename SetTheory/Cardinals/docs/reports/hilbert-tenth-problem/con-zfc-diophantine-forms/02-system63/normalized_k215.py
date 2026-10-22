#!/usr/bin/env python3
"""Explicit normalized K215 machine and exact helical window alphabet.

This module is a finite specification, not a claim that the astronomical
full window list has been materialized.  Only standard-library Python is used.
Tape positions are integers.  All reachable positions are nonpositive.
delta returns (new_state, written_symbol, movement), where movement is -1/0/+1.
"""
from __future__ import annotations

from hashlib import sha256
from itertools import product
from pathlib import Path
from collections import Counter
import json

if not __debug__:
    raise RuntimeError('normalized_k215 requires assertions enabled; do not run Python with -O.')

TABLE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
SOURCE_COMMIT = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
START, AFTER, ERASE, RETURN, SINK, HALT = range(6)
STATE_COUNT = 436
SYMBOL_COUNT = 8
ALPHABET_SIZE = 3502

# (positive-side bit, negative-side bit, is_origin).
# Unary-input symbol 1 doubles as an ordinary paired-tape symbol, but is
# erased before any simulation begins.  Symbol 2 is the cleared origin.
DECODE = ((0, 0, False), (1, 0, False), (0, 0, True),
          (0, 1, False), (1, 1, False), (0, 1, True),
          (1, 0, True), (1, 1, True))
ENCODE = {t: i for i, t in enumerate(DECODE)}


def load_table(path: Path | None = None):
    path = path or Path(__file__).with_name('k215.tm')
    raw = path.read_bytes()
    if sha256(raw).hexdigest() != TABLE_SHA256:
        raise ValueError('The K215 transition table does not match its pinned SHA-256.')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#'):
            continue
        q, read, write, move, target = line.split()
        key = (int(q), int(read))
        assert key not in table
        table[key] = (int(target), int(write), -1 if move == 'L' else 1)
    assert set(table) == set(product(range(215), range(2)))
    assert [(q, b) for (q, b), (t, _, _) in table.items() if t == 215] == [(68, 1)]
    return table


def sim_state(q: int, side: int):
    assert 0 <= q < 215 and side in (0, 1)
    return 6 + 2*q + side


class NormalizedK215:
    alphabet = tuple(range(SYMBOL_COUNT))
    states = tuple(range(STATE_COUNT))
    start = START
    after = AFTER
    halt = HALT
    blank = 0

    def __init__(self, table=None):
        self.table = table if table is not None else load_table()

    def delta(self, q: int, symbol: int):
        assert q in self.states and symbol in self.alphabet
        if q == START:
            return (AFTER, 2, 0) if symbol == 1 else (SINK, symbol, 0)
        if q == AFTER:
            return (ERASE, 2, -1) if symbol == 2 else (SINK, symbol, 0)
        if q == ERASE:
            if symbol == 1:
                return ERASE, 0, -1
            return (RETURN, 0, 1) if symbol == 0 else (SINK, symbol, 0)
        if q == RETURN:
            if symbol == 0:
                return RETURN, 0, 1
            return (sim_state(0, 0), 2, 0) if symbol == 2 else (SINK, symbol, 0)
        if q in (SINK, HALT):
            return q, symbol, 0
        original, side = divmod(q - 6, 2)
        posbit, negbit, origin = DECODE[symbol]
        target, written, virtual_move = self.table[original, (posbit, negbit)[side]]
        pair = (written, negbit) if side == 0 else (posbit, written)
        new_symbol = ENCODE[pair + (origin,)]
        # Positive virtual coordinate j is stored at physical -j.
        # Negative virtual coordinate -j-1 is stored at physical -j.
        toward_origin = (virtual_move == (-1 if side == 0 else 1))
        if toward_origin and origin:
            new_side, physical_move = 1 - side, 0
        else:
            new_side = side
            physical_move = (virtual_move if side else -virtual_move)
        new_state = HALT if target == 215 else sim_state(target, new_side)
        return new_state, new_symbol, physical_move


def tile(v=0, h=0, payload=None, phase=None):
    return v, h, payload, phase


V = tile(1, 0)
H = tile(0, 1)
PHASES = ('L', 'I', 'Q', 'R')
PAIRS = {('L','L'), ('L','I'), ('I','I'), ('I','Q'), ('Q','R'), ('R','R')}


def phase_payload(phase, machine):
    return {'L': (0,None), 'I': (1,None), 'Q': (1,machine.start), 'R': (0,None)}[phase]


def all_tiles(machine):
    """Canonical IDs: V,H, then (symbol,head), then L,I,Q,R phase tiles."""
    result = [V, H]
    for symbol in machine.alphabet:
        for head in (None,) + machine.states:
            result.append(tile(0, 0, (symbol, head)))
    result.extend(tile(0,0,phase_payload(p,machine),p) for p in PHASES)
    expected = 2 + len(machine.alphabet)*(len(machine.states)+1) + 4
    assert len(result) == expected and len(set(result)) == expected
    return tuple(result)


def next_payload(left, center, right, machine):
    """The ordinary radius-one local rule; multiple arriving heads reject."""
    arriving = []
    written = center[0]
    for offset, (symbol, state) in zip((-1,0,1), (left,center,right)):
        if state is None:
            continue
        target, new_symbol, move = machine.delta(state, symbol)
        if offset == 0:
            written = new_symbol
        if offset + move == 0:
            arriving.append(target)
    if len(arriving) > 1:
        return None
    return written, (arriving[0] if arriving else None)


def local_valid(center, at, machine):
    """Exact retained helical clause, with the same y orientation as its source."""
    v, h, payload, phase = center
    left, right, down, up = at(-1,0), at(1,0), at(0,-1), at(0,1)
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
        if phase not in PHASES or (left[0] and phase != 'L') or (right[0] and phase != 'R'):
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
        blank = (machine.blank,None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload(blank if left[0] else left[2], payload,
                                blank if right[0] else right[2], machine)
        if expected is None or up[2] != expected:
            return False
    return True


def valid_window(window, machine):
    assert len(window) == 9
    return local_valid(window[4], lambda dx,dy: window[(dy+1)*3+dx+1], machine)


def fixed_markers(machine):
    L = tile(0,0,(0,None),'L')
    I = tile(0,0,(1,None),'I')
    Q = tile(0,0,(1,machine.start),'Q')
    plain0 = tile(0,0,(0,None))
    plain1 = tile(0,0,(1,None))
    after = tile(0,0,(2,machine.after))
    start = (H,H,H, I,I,Q, plain1,plain1,after)
    end = (H,H,H, L,I,I, plain0,plain1,plain1)
    assert valid_window(start,machine) and valid_window(end,machine)
    return start, end


def iter_allowed_windows(machine=None):
    """Complete finite definition, intentionally not invoked by validation.

    Start is selector 0, End selector 1, remaining admissible 9-tuples occur
    in lexicographic order of canonical tile IDs.  This enumerates a fixed
    subset of {0,...,3501}^9 and consults no halting or consistency oracle.
    """
    machine = machine or NormalizedK215()
    tiles = all_tiles(machine)
    ids = {t: i for i,t in enumerate(tiles)}
    start, end = (tuple(ids[t] for t in w) for w in fixed_markers(machine))
    yield start
    yield end
    for window in product(range(len(tiles)), repeat=9):
        if window in (start,end):
            continue
        if valid_window(tuple(tiles[i] for i in window), machine):
            yield window


def count_allowed_windows(machine=None):
    """Exact count by factoring the four unconstrained corner coordinates.

    No transition may target the initialization state; hence every headed output
    has exactly one no-phase/phase tile representation.  An unheaded output
    has three representations at symbol0, two at symbol1, one otherwise.
    See normalization.md for the count derivation.
    """
    machine = machine or NormalizedK215()
    a = len(all_tiles(machine))
    N = a-1
    actions = [machine.delta(q,s) for q,s in product(machine.states,machine.alphabet)]
    assert all(target != machine.start for target,_,_ in actions)
    assert machine.delta(machine.start,1) == (machine.after,2,0)
    assert all(machine.delta(machine.halt,s) == (machine.halt,s,0) for s in machine.alphabet)
    moves = Counter(move for _,_,move in actions)
    left_arrivals, right_arrivals = moves[1], moves[-1]
    left_none, right_none = N-left_arrivals, N-right_arrivals
    plain = 0
    for symbol in machine.alphabet:
        for state in (None,) + machine.states:
            if state is None:
                target, written, move = None, symbol, None
            else:
                target, written, move = machine.delta(state,symbol)
            l = left_none - int(move == -1)
            r = right_none - int(move == 1)
            if state is not None and move == 0:
                ways = l*r
            else:
                multiplicity = 3 if written == 0 else 2 if written == 1 else 1
                ways = l*r*multiplicity + left_arrivals*r + l*right_arrivals
            plain += ways
    parts = dict(vertical=a*a*N, horizontal=2*a*a*(a-2),
                 terminal=2*len(machine.alphabet)*a*N*N+6*a-4,
                 successor=plain*N+17*left_none+6*left_arrivals-11)
    crosses = sum(parts.values())
    windows = crosses*a**4
    return dict(movement_counts={str(k):moves[k] for k in (-1,0,1)},
                left_noarrival=left_none,right_noarrival=right_none,
                cross_parts=parts,valid_crosses=crosses,allowed_windows=windows,
                selector_radix_bits=max(2,(windows+1).bit_length()))


def verify_count_fixtures():
    """Independent exhaustive five-coordinate enumeration on two small machines."""
    class SmallMachine:
        alphabet = (0,1,2)
        states = (0,1,2)
        start, after, halt, blank = 0,1,2,0
        def __init__(self,mixed):
            self.mixed = mixed
        def delta(self,q,s):
            if q == 0:
                return (1,2,0) if s == 1 else (1,s,0)
            if q == 2:
                return 2,s,0
            if self.mixed and s < 2:
                return 1,s,(-1 if s == 0 else 1)
            return 2,s,0
    records = []
    for mixed in (False,True):
        machine = SmallMachine(mixed)
        tiles = all_tiles(machine)
        counts = dict(vertical=0,horizontal=0,terminal=0,successor=0)
        for center,left,right,down,up in product(tiles,repeat=5):
            neighbors = {(-1,0):left,(1,0):right,(0,-1):down,(0,1):up}
            if local_valid(center,lambda dx,dy:neighbors[dx,dy],machine):
                part = 'vertical' if center[0] else 'horizontal' if center[1] else 'terminal' if up[1] else 'successor'
                counts[part] += 1
        formula = count_allowed_windows(machine)
        assert counts == formula['cross_parts'], (mixed,counts,formula)
        records.append(dict(mixed=mixed,alphabet_size=len(tiles),
                            brute_cross_candidates=len(tiles)**5,counts=counts))
    return records


def sparse_write(tape, position, symbol):
    if symbol:
        tape[position] = symbol
    else:
        tape.pop(position, None)


def simulate_prefix(machine, unary_length, steps):
    """Check an arbitrary finite prefix against the original exact machine."""
    tape = {j: 1 for j in range(1-unary_length, 1)}
    head, state, init_steps = 0, START, 0
    while state != sim_state(0,0):
        state, symbol, move = machine.delta(state,tape.get(head,0))
        sparse_write(tape,head,symbol)
        head += move
        init_steps += 1
        assert head <= 0 and init_steps <= 2*unary_length + 5
    assert head == 0 and tape == {0:2}
    original, ohead, ostate = {}, 0, 0
    for step in range(steps):
        assert head == (-ohead if ohead >= 0 else ohead + 1)
        assert state == sim_state(ostate, int(ohead < 0))
        target, written, omove = machine.table[ostate,original.get(ohead,0)]
        sparse_write(original,ohead,written)
        ohead += omove
        ostate = target
        state, symbol, move = machine.delta(state,tape.get(head,0))
        sparse_write(tape,head,symbol)
        head += move
        assert head <= 0
        restored = {}
        for position, code in tape.items():
            pbit,nbit,is_origin = DECODE[code]
            assert is_origin == (position == 0)
            if pbit:
                restored[-position] = pbit
            if nbit:
                restored[position-1] = nbit
        assert restored == original
        if target == 215:
            assert state == HALT
            return {'initialization_steps':init_steps, 'simulation_steps':step+1, 'halted':True}
    return {'initialization_steps':init_steps, 'simulation_steps':steps, 'halted':False}


def validate():
    machine = NormalizedK215()
    table_count = 0
    for q,s in product(machine.states,machine.alphabet):
        target,written,move = machine.delta(q,s)
        assert target in machine.states and written in machine.alphabet and move in (-1,0,1)
        table_count += 1
    tiles = all_tiles(machine)
    start,end = fixed_markers(machine)
    ids = {t:i for i,t in enumerate(tiles)}
    # Arbitrary local tape contents, all working states, both fold sides,
    # and both boundary/interior locations exercise every simulation clause.
    local_checks = 0
    for q,side,k,pbit,nbit in product(range(215),range(2),(0,1,7),range(2),range(2)):
        code = ENCODE[pbit,nbit,k==0]
        target,written,move = machine.delta(sim_state(q,side),code)
        oq,ow,om = machine.table[q,(pbit,nbit)[side]]
        virtual = k if side == 0 else -k-1
        new_virtual = virtual + om
        new_physical = -new_virtual if new_virtual >= 0 else new_virtual+1
        assert -k + move == new_physical
        assert target == (HALT if oq == 215 else sim_state(oq,int(new_virtual<0)))
        expected_pair = (ow,nbit) if side==0 else (pbit,ow)
        assert DECODE[written] == expected_pair + (k==0,)
        local_checks += 1
    prefixes = [simulate_prefix(machine,n,1000) for n in (3,4,5,12)]
    long_prefix = simulate_prefix(machine,4,95714)
    return dict(status='PASS_FINITE_NORMALIZATION_CHECKS', source_commit=SOURCE_COMMIT,
                k215_sha256=TABLE_SHA256, normalized_states=STATE_COUNT,
                tape_symbols=SYMBOL_COUNT, transition_rows=table_count,
                original_tile_alphabet=ALPHABET_SIZE,
                exact_window_count=count_allowed_windows(machine),
                start_window=[ids[t] for t in start], end_window=[ids[t] for t in end],
                exhaustive_folded_transition_checks=local_checks,
                initializations=prefixes, long_prefix=long_prefix,
                full_window_enumeration_performed=False,
                scope='Finite implementation checks; general simulation proof is in the report; no ZFC consistency or nonhalting claim.')


if __name__ == '__main__':
    print(json.dumps(validate(),indent=2))

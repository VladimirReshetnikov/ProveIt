#!/usr/bin/env python3
"""Finite definition of the K215 native-window specialization.

This file does NOT enumerate the astronomical complete window alphabet by default.
Its machine table, local predicate, and finite enumeration order fix that alphabet
unambiguously. The native coefficient formulas are in construction_review.txt.
No claim is made that the full coefficients or an accepting Pell witness were run.
"""
from itertools import product
from pathlib import Path
import hashlib
import json

TM_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
Q0, Q1, E0, E1, RETURN, LOOP, HALT = range(7)
STATES = tuple(range(437))
ALPHABET = tuple(range(8))
SIM0 = 7


def encode(a, b, origin):
    raw = a + 2*b + 4*origin
    return {2:4, 4:2}.get(raw, raw)


def decode(symbol):
    raw = {2:4, 4:2}.get(symbol, symbol)
    return raw & 1, (raw >> 1) & 1, (raw >> 2) & 1


def read_k215(path):
    raw = Path(path).read_bytes()
    if hashlib.sha256(raw).hexdigest() != TM_SHA256:
        raise ValueError('K215 transition file digest mismatch')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if not line or line.startswith('#'):
            continue
        q, a, written, move, target = line.split()
        key = (int(q), int(a))
        if key in table:
            raise ValueError('Duplicate transition')
        table[key] = (int(target), int(written), {'L':-1, 'R':1}[move])
    if set(table) != set(product(range(215), range(2))):
        raise ValueError('Incomplete K215 transition domain')
    if any(not (0 <= q <= 215 and a in (0, 1) and d in (-1, 1))
           for q, a, d in table.values()):
        raise ValueError('Invalid K215 transition')
    return table


class Normalized:
    states, alphabet, start, halt, blank = STATES, ALPHABET, Q0, HALT, 0

    def __init__(self, original):
        self.original = original

    def delta(self, state, symbol):
        if state == HALT:
            return HALT, symbol, 0
        if state == Q0 and symbol == 1:
            return Q1, 2, 0
        if state == Q1 and symbol == 2:
            return E0, 2, -1
        if state in (E0, E1) and symbol == 1:
            return E1 if state == E0 else E0, 0, -1
        if state == E1 and symbol == 0:
            return RETURN, 0, 1
        if state == RETURN and symbol == 0:
            return RETURN, 0, 1
        if state == RETURN and symbol == 2:
            return SIM0, 2, 0
        if state < SIM0:
            return LOOP, symbol, 0
        q, side = divmod(state-SIM0, 2)
        upper, lower, origin = decode(symbol)
        nq, written, move = self.original[q, lower if side else upper]
        new_upper, new_lower = (upper, written) if side else (written, lower)
        if (side == 0 and move == 1) or (side == 1 and move == -1):
            physical_move, next_side = -1, side
        elif origin:
            physical_move, next_side = 0, 1-side
        else:
            physical_move, next_side = 1, side
        next_state = HALT if nq == 215 else SIM0+2*nq+next_side
        return next_state, encode(new_upper, new_lower, origin), physical_move


def tile(v, h, payload=None, phase=None):
    return (v, h, payload, phase)


def tile_alphabet():
    # This order, not an ambient Python tuple comparison involving None, fixes IDs.
    return ((tile(1,0), tile(0,1))
            + tuple(tile(0,0,(a,q)) for a in ALPHABET for q in (None,)+STATES)
            + (tile(0,0,(0,None),'L'), tile(0,0,(1,None),'I'),
               tile(0,0,(1,Q0),'Q'), tile(0,0,(0,None),'R')))


PAIRS = {('L','L'), ('L','I'), ('I','I'), ('I','Q'), ('Q','R'), ('R','R')}


def next_payload(left, center, right, machine):
    symbol, state = center
    output = symbol if state is None else machine.delta(state,symbol)[1]
    incoming = []
    for (a,q), direction in ((left,1),(center,0),(right,-1)):
        if q is not None:
            nq, _, move = machine.delta(q,a)
            if move == direction:
                incoming.append(nq)
    return None if len(incoming)>1 else (output, incoming[0] if incoming else None)


def allowed_window(window, machine):
    """The repository's helical radius-one predicate, stated independently."""
    v,h,payload,phase = window[4]
    left,right,down,up = window[3],window[5],window[1],window[7]
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
        if phase not in ('L','I','Q','R'):
            return False
        if (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase,right[3]) not in PAIRS:
            return False
        expected = ((0,None) if phase in ('L','R') else
                    (1,Q0 if phase == 'Q' else None))
        if payload != expected:
            return False
    elif phase is not None:
        return False
    symbol,state = payload
    if up[1] and state is not None and state != HALT:
        return False
    if state is not None:
        move = machine.delta(state,symbol)[2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        blank = (0,None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload(blank if left[0] else left[2],payload,
                                blank if right[0] else right[2],machine)
        if expected is None or up[2] != expected:
            return False
    return True


def markers():
    H = tile(0,1)
    cell = lambda a,q=None,p=None: tile(0,0,(a,q),p)
    start = (H,H,H,cell(1,p='I'),cell(1,p='I'),cell(1,Q0,'Q'),
             cell(1),cell(1),cell(2,Q1))
    end = (H,H,H,cell(0,p='L'),cell(1,p='I'),cell(1,p='I'),
           cell(0),cell(1),cell(1))
    return start,end


def full_window_ids(machine):
    """Exact finite specification; infeasible to exhaust for K215 in practice."""
    alphabet = tile_alphabet()
    ids = {t:i for i,t in enumerate(alphabet)}
    start,end = (tuple(ids[t] for t in w) for w in markers())
    yield start
    yield end
    for indices in product(range(len(alphabet)),repeat=9):
        if indices not in (start,end):
            w = tuple(alphabet[i] for i in indices)
            if allowed_window(w,machine):
                yield indices


def raw_step(table,tape,head,state):
    nq,a,d = table[state,tape.get(head,0)]
    tape[head] = a
    return head+d,nq


def normalized_step(machine,tape,head,state):
    nq,a,d = machine.delta(state,tape.get(head,0))
    tape[head] = a
    return head+d,nq


def finite_checks(path):
    original = read_k215(path)
    machine = Normalized(original)
    alphabet = tile_alphabet()
    if len(alphabet) != len(set(alphabet)) or len(alphabet) != 3510:
        raise ValueError('Tile alphabet error')
    for state,symbol in product(STATES,ALPHABET):
        q,a,d = machine.delta(state,symbol)
        if q not in STATES or a not in ALPHABET or d not in (-1,0,1):
            raise ValueError('Nontotal normalized transition table')
    if any(not allowed_window(w,machine) for w in markers()):
        raise ValueError('Marker not locally valid')
    checks = 0
    for y in range(1,13):
        tape = {-j:1 for j in range(y+2)}
        head,state = 0,Q0
        for _ in range(4*y+20):
            if state >= SIM0 or state == LOOP:
                break
            head,state = normalized_step(machine,tape,head,state)
            if head > 0:
                raise ValueError('Escaped during preprocessing')
        if y % 2:
            if state != LOOP:
                raise ValueError('Odd input accepted into simulation')
            continue
        if state != SIM0 or head != 0 or any(a != (2 if p==0 else 0) for p,a in tape.items()):
            raise ValueError('Preprocessing did not produce the blank simulation')
        raw,raw_head,raw_state = {},0,0
        for _ in range(2000):
            if raw_state == 215:
                if state != HALT:
                    raise ValueError('Halting mismatch')
                break
            raw_head,raw_state = raw_step(original,raw,raw_head,raw_state)
            head,state = normalized_step(machine,tape,head,state)
            if head > 0:
                raise ValueError('Escaped folded half-line')
            if raw_state != 215:
                q,side = divmod(state-SIM0,2)
                represented_head = -head if side==0 else head-1
                if (q,represented_head) != (raw_state,raw_head):
                    raise ValueError('Control/head simulation mismatch')
            for p in set(tape) | {-abs(t) for t in raw} | {t+1 for t in raw if t<0}:
                if p>0:
                    continue
                upper,lower,origin = decode(tape.get(p,0))
                if (upper,lower,origin) != (raw.get(-p,0),raw.get(p-1,0),int(p==0)):
                    raise ValueError('Tape simulation mismatch')
            checks += 1
    return {'status':'PASS_FINITE_DEFINITION_CHECKS',
            'k215_sha256':TM_SHA256, 'normalized_states':len(STATES),
            'normalized_symbols':len(ALPHABET), 'tiles':len(alphabet),
            'total_transitions':len(STATES)*len(ALPHABET),
            'simulation_steps_compared':checks,
            'unary_test_inputs':list(range(1,13)), 'markers_locally_valid':2,
            'full_window_enumeration_run':False,
            'complete_coefficients_materialized':False,
            'scope':'Finite regression tests only. General simulation and compiler semantics require their mathematical proofs.'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def least_power_of_five_at_least(n):
    value = 1
    while value < n:
        value *= 5
    return value


def add_term(poly, exponent, coefficient):
    poly[exponent] = poly.get(exponent, 0) + coefficient


def compile_native_layout(windows, alphabet_size):
    """Independent transcription of the pinned 76 geometry + 75 radix recipe.

    Input is the COMPLETE finite window list, with Start first and End second.
    The return value specifies six constants by sparse finite sums. Neither B
    nor any full mask is allocated here. The K215 input is enormous; this
    function is exercised only on explicitly labeled small interface fixtures.
    """
    windows = tuple(tuple(w) for w in windows)
    k, a = len(windows), alphabet_size
    require(k >= 2 and len(set(windows)) == k, 'Invalid window list')
    require(all(len(w)==9 and all(0 <= t < a for t in w) for w in windows),
            'Invalid window entry')
    A = 1 << max(2, (k+1).bit_length())
    start = k + 3*a
    payload = {(r,c,t): start+(2-r)*3*a+(2-c)*a+t
               for r,c,t in product(range(3),range(3),range(a))}
    coeff = {i:1 for i in range(k)}
    mu = A-2
    for j, ((r,c,t), exponent) in enumerate(payload.items(), 1):
        coefficient = A**j
        coeff[exponent] = coefficient
        mu += coefficient
        for i, window in enumerate(windows):
            if window[3*r+c] == t:
                coeff[i] += coefficient
    anchor_coefficients = []
    for j in range(1+9*a, 1+9*a+4):
        coefficient = A**j
        anchor_coefficients.append(coefficient)
        mu += coefficient
        for i in range(k):
            coeff[i] += coefficient
    padding = 0
    m = 2*mu.bit_count()+12*a+2
    next_clause = 1+9*a+4
    while m+1 < k+9*a+5:
        mu += A**(next_clause+padding)
        padding += 1
        m += 2
    dummy = tuple(range(start+9*a, start+9*a+(m+1-k-9*a-4)))
    require(bool(dummy), 'No dummy position')
    old_positions = tuple(range(k))+tuple(payload.values())+dummy
    M = max(old_positions)+3*a+1
    anchors = tuple(t*M for t in (1,3,9,27))
    positions = old_positions+anchors
    for exponent, coefficient in zip(anchors,anchor_coefficients):
        coeff[exponent] = coefficient
    require(len(set(positions)) == len(positions) == m+1, 'Position collision')
    E = max(positions)
    H = E+24*M+3*a+1
    T1 = H+2*E+a+1
    T2 = T1+2*E+1
    g = T2+E+1
    L = least_power_of_five_at_least(g+E+1)
    DCpoly = {}
    for exponent in (3*a,H+a,8*M,24*M):
        add_term(DCpoly,exponent,1)
    for exponent, coefficient in coeff.items():
        add_term(DCpoly,T1-exponent,coefficient)
        add_term(DCpoly,T2-exponent,coefficient)
    unit = (2*sum(c*pow(2,e,5) for e,c in DCpoly.items())-pow(2,H,5)) % 5
    correction = int(unit == 0)
    if correction:
        add_term(DCpoly,g,1)
    MFpoly = {T1:mu,T2:mu}
    for r,c,t in product(range(2),range(3),range(a)):
        add_term(MFpoly,payload[r,c,t],1)
    for r,c,t in product(range(3),range(2),range(a)):
        add_term(MFpoly,H+payload[r,c,t],1)
    for exponent in anchors[2:]:
        add_term(MFpoly,exponent,1)
    # This is the MODIFIED 75 radix, not the preceding 76 radix.
    mass = (len(positions)+2)*(2*sum(coeff.values())+6)
    target = max(4*mass+8,2*mu+4,16)
    b = least_power_of_five_at_least((target-1).bit_length())
    d = b*L
    require(sum(c.bit_count() for c in MFpoly.values()) == m, 'Mask population')
    require(max(DCpoly)+E < L and max(MFpoly) < g, 'Band separation')
    require((2*sum(c*pow(2,e,5) for e,c in DCpoly.items())-pow(2,H,5)) % 5 != 0,
            'Missing five-adic correction')
    return dict(window_count=k, tile_count=a, clause_base=A, clause_mask=mu,
                zero_clause_padding=padding, positions=positions, dummy=dummy,
                center_coefficients=coeff, anchors=anchors, H=H,T1=T1,T2=T2,
                high_degree=g, high_correction=correction, L=L,b=b,d=d,
                DCpoly=DCpoly,MF_old_poly=MFpoly, extra_dummy=dummy[0],
                radix_target=target, unshifted_mass_bound=mass)


def materialize_native_coefficients(layout):
    """Exact integer evaluation, potentially much too large for real hardware.

    All powers here have FIXED integer exponents. None is a variable power in
    the final Diophantine polynomial. MF in the returned tuple is source MF,
    namely native MF plus B minus 1, not the native mask alone.
    """
    b,L,d = layout['b'],layout['L'],layout['d']
    R = 1 << b
    B = 1 << d
    DC = sum(c << (b*e) for e,c in layout['DCpoly'].items())
    DR = 1 << (b*layout['H'])
    MC_old = B-1-sum(1 << (b*e) for e in layout['positions'] if e != 1)
    MC = MC_old-(2 << (b*layout['extra_dummy']))
    MF_native = sum(c << (b*e) for e,c in layout['MF_old_poly'].items())+4
    require(0 < MC < B-1 and 0 < MF_native < B-1, 'Native mask ranges')
    require(MC % 4 == 2 and MF_native % 8 == 4, 'Native mask residues')
    require(MC.bit_count()+MF_native.bit_count() == d, 'Native mask mass')
    return {'Bm1':B-1, 'Kconstant':DC+B*DR, 'fixed_2d':2*d,
            'fixed_2d_plus_b':2*d+b, 'MC':MC, 'MF':MF_native+B-1}


def k215_coefficients(path):
    """The six completely specified integers of the 82-operation equation.

    This finite recipe uniquely specifies the six integers. In the idealized
    unbounded-memory integer model every enumeration is over a fixed finite set.
    Full evaluation is NOT claimed practical and is not part of default tests.
    """
    machine = Normalized(read_k215(path))
    layout = compile_native_layout(full_window_ids(machine),len(tile_alphabet()))
    return materialize_native_coefficients(layout)


if __name__ == '__main__':
    print(json.dumps(finite_checks(Path(__file__).with_name('k215.tm')),indent=2))

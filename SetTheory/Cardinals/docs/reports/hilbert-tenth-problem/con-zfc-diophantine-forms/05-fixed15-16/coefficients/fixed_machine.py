"""A completely specified one-sided, stay-first-step version of literal K215.

Standard library only. This module also specifies its finite radius-one window
alphabet and acceptance predicate. Neither construction runs K215 to completion.
"""
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

PIN = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
NATIVE_SHA256 = '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
DENSE_SHA256 = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
CANONICALIZATION_SHA256 = 'c24abea425721f9b2d5cb7bbb1a2e9b164b4f3837e362c7ca4c3a88da6ac885a'
HERE = Path(__file__).resolve().parent
Q0, Q1, ERASE, RETURN, HALT, TRAP = range(6)
PHASES = ('L', 'I', 'Q', 'R')
PAIRS = {('L','L'), ('L','I'), ('I','I'), ('I','Q'), ('Q','R'), ('R','R')}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_native(path=HERE / 'k215.native.tm'):
    raw = Path(path).read_bytes()
    require(sha256(raw).hexdigest() == NATIVE_SHA256, 'literal native SHA-256 mismatch')
    table = {}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#') or not line.strip():
            continue
        q, a, b, move, p = line.split()
        q, a, b, p = map(int, (q,a,b,p))
        require((q,a) not in table, 'duplicate native row')
        require(a in (0,1) and b in (0,1) and move in ('L','R'), 'native row type')
        table[q,a] = (p,b,-1 if move == 'L' else 1)
    states = tuple(sorted({q for q,a in table}))
    require(len(states) == 215 and len(table) == 430, 'literal table cardinality')
    require(set(table) == set(product(states,(0,1))), 'total native table')
    require({p for p,b,m in table.values()} <= set(states) | {254}, 'native target')
    require(0 in states and 254 not in states, 'native start and halt')
    return states, table, sha256(raw).hexdigest()


def verify_dense_isomorphism():
    states,native,native_hash = read_native()
    certificate_bytes = (HERE/'canonicalization.json').read_bytes()
    require(sha256(certificate_bytes).hexdigest() == CANONICALIZATION_SHA256, 'canonicalization SHA-256 mismatch')
    cert = json.loads(certificate_bytes)
    rename = {int(q):p for q,p in cert['native_to_canonical'].items()}
    inverse = {int(q):p for q,p in cert['canonical_to_native'].items()}
    require(set(rename) == set(states)|{254}, 'renaming domain')
    require(set(rename.values()) == set(range(216)), 'renaming codomain')
    require(all(inverse[p] == q for q,p in rename.items()), 'inverse state map')
    require(rename[0] == 0 and rename[254] == 215, 'start and halt renaming')
    raw = (HERE/'k215.tm').read_bytes()
    require(sha256(raw).hexdigest() == DENSE_SHA256, 'literal dense SHA-256 mismatch')
    dense = {}
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#') or not line.strip():
            continue
        q,a,b,move,p = line.split()
        q,a,b,p = map(int,(q,a,b,p))
        require((q,a) not in dense, 'duplicate dense row')
        require(a in (0,1) and b in (0,1) and move in ('L','R'), 'dense row type')
        dense[q,a] = (p,b,-1 if move == 'L' else 1)
    renamed = {(rename[q],a):(rename[p],b,d) for (q,a),(p,b,d) in native.items()}
    require(dense == renamed and len(dense) == 430, 'all transition rows must agree')
    dense_hash = sha256(raw).hexdigest()
    require(native_hash == cert['native_sha256'] and dense_hash == cert['canonical_sha256'], 'byte pins')
    return dict(native_sha256=native_hash,dense_sha256=dense_hash,
                canonicalization_sha256=sha256((HERE/'canonicalization.json').read_bytes()).hexdigest(),
                checked_rows=430,start_native=0,start_dense=0,halt_native=254,halt_dense=215,
                status='EXACT_TABLE_ISOMORPHISM_CHECKED')


# Ordinary cell symbol -> (nonnegative-track bit, negative-track bit).
PLAIN = {0:(0,0), 3:(0,1), 4:(1,0), 5:(1,1)}
ORIGIN = {6:(0,0), 7:(0,1), 8:(1,0), 9:(1,1)}
PAIRED = dict(PLAIN, **{})
PAIRED.update(ORIGIN)
ENCODE_PLAIN = {v:k for k,v in PLAIN.items()}
ENCODE_ORIGIN = {v:k for k,v in ORIGIN.items()}


class Machine:
    def __init__(self, source=None):
        self.source_states, self.native, self.native_sha256 = read_native() if source is None else source
        self.source_index = {q:i for i,q in enumerate(self.source_states)}
        self.states = tuple(range(6+2*len(self.source_states)))
        self.alphabet = tuple(range(10))
        self.start, self.halt, self.blank = Q0, HALT, 0
        self.transitions = {(q,a):(TRAP,a,0) for q in self.states for a in self.alphabet}
        for a in self.alphabet:
            self.transitions[HALT,a] = (HALT,a,0)
            self.transitions[TRAP,a] = (TRAP,a,0)
        self.transitions[Q0,1] = (Q1,2,0)
        self.transitions[Q1,2] = (ERASE,2,-1)
        self.transitions[ERASE,1] = (ERASE,0,-1)
        self.transitions[ERASE,0] = (RETURN,0,1)
        self.transitions[RETURN,0] = (RETURN,0,1)
        self.transitions[RETURN,2] = (self.sim(0,0),6,0)
        for q, side, symbol in product(self.source_states, (0,1), PAIRED):
            bits = PAIRED[symbol]
            target, written, move = self.native[q,bits[side]]
            out = list(bits)
            out[side] = written
            marked = symbol in ORIGIN
            write = (ENCODE_ORIGIN if marked else ENCODE_PLAIN)[tuple(out)]
            if marked and ((side == 0 and move == -1) or (side == 1 and move == 1)):
                physical_move, next_side = 0, 1-side
            else:
                physical_move, next_side = (-move if side == 0 else move), side
            next_state = HALT if target == 254 else self.sim(target,next_side)
            self.transitions[self.sim(q,side),symbol] = (next_state,write,physical_move)

    def sim(self, q, side):
        return 6 + 2*self.source_index[q] + side

    def delta(self, q, a):
        return self.transitions[q,a]


def tile(v, h, payload=None, phase=None):
    return (v,h,payload,phase)


def tile_alphabet(machine):
    # This explicit order is used by the window and coefficient definitions.
    boundary = (tile(1,0), tile(0,1))
    ordinary = tuple(tile(0,0,(s,q)) for s in machine.alphabet for q in (None,)+machine.states)
    phases = tuple(tile(0,0,phase_payload(p,machine),p) for p in PHASES)
    return boundary + ordinary + phases


def phase_payload(phase, machine):
    if phase in ('L','R'):
        return (0,None)
    return (1, machine.start if phase == 'Q' else None)


def next_payload(left, center, right, machine):
    symbol, state = center
    written = symbol if state is None else machine.delta(state,symbol)[1]
    incoming = []
    for (a,q), required in ((left,1),(center,0),(right,-1)):
        if q is not None:
            p, _, move = machine.delta(q,a)
            if move == required:
                incoming.append(p)
    return None if len(incoming)>1 else (written, incoming[0] if incoming else None)


def local_valid(window, machine):
    """Row-major order: y=-1,0,1 and x=-1,0,1; only the cross is tested.

    Every window entry must belong to tile_alphabet(machine). Membership is
    part of allowed_windows, rather than retested at each predicate call.
    """
    down, left, center, right, up = (window[i] for i in (1,3,4,5,7))
    v,h,payload,phase = center
    if v != up[0] or (v and right[0]) or (h and up[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    if v or h:
        return payload is None and phase is None
    if down[1]:
        if phase not in PHASES or (left[0] and phase != 'L') or (right[0] and phase != 'R'):
            return False
        if not right[0] and (phase,right[3]) not in PAIRS:
            return False
        if payload != phase_payload(phase,machine):
            return False
    elif phase is not None:
        return False
    symbol,state = payload
    if up[1] and state is not None and state != machine.halt:
        return False
    if state is not None:
        move = machine.delta(state,symbol)[2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not up[1]:
        blank = (machine.blank,None)
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected = next_payload(blank if left[0] else left[2],payload,
                                blank if right[0] else right[2],machine)
        if expected is None or up[2] != expected:
            return False
    return True


def markers(machine):
    H = tile(0,1)
    c = lambda s,q=None,p=None: tile(0,0,(s,q),p)
    S = (H,H,H,c(1,p='I'),c(1,p='I'),c(1,Q0,'Q'),c(1),c(1),c(2,Q1))
    E = (H,H,H,c(0,p='L'),c(1,p='I'),c(1,p='I'),c(0),c(1),c(1))
    return S,E


def allowed_windows(machine):
    """An exact, finite, generally infeasible enumeration; no halting oracle.

    Start is selector 0; End is selector 1; all other locally valid windows
    follow lexicographically in the explicit tile alphabet. All loop bounds
    are finite constants determined by the literal transition table.
    """
    alphabet = tile_alphabet(machine)
    index = {cell:i for i,cell in enumerate(alphabet)}
    S,E = markers(machine)
    specials = {tuple(map(index.__getitem__, S)),tuple(map(index.__getitem__, E))}
    require(local_valid(S,machine) and local_valid(E,machine), 'marker admissibility')
    yield tuple(map(index.__getitem__, S))
    yield tuple(map(index.__getitem__, E))
    for ids in product(range(len(alphabet)),repeat=9):
        if ids not in specials and local_valid(tuple(alphabet[i] for i in ids),machine):
            yield ids


def count_windows(machine):
    """Exact count by the five-cell cross; four unused corners are free.

    Incoming-head histograms factor the left/right sum. This evaluates the
    finite alphabet size without enumerating the astronomical window set.
    """
    alphabet = tile_alphabet(machine)
    a = len(alphabet)
    up_counts = Counter(cell[2] for cell in alphabet if not cell[0] and not cell[1])

    @lru_cache(None)
    def neighbor(side, phase, move, last_row):
        choices = []
        for cell in alphabet:
            v,h,payload,p = cell
            if side == 'R' and not v and h:
                continue
            if phase is not None:
                if v and phase != ('L' if side == 'L' else 'R'):
                    continue
                if side == 'R' and not v and (phase,p) not in PAIRS:
                    continue
            if v and move == (-1 if side == 'L' else 1):
                continue
            if not last_row and not v and payload is None:
                continue
            choices.append(cell)
        hist = Counter()
        if not last_row:
            for v,h,payload,p in choices:
                s,q = (machine.blank,None) if v else payload
                target = None
                if q is not None:
                    newq,_,direction = machine.delta(q,s)
                    if direction == (1 if side == 'L' else -1):
                        target = newq
                hist[target] += 1
        return len(choices),hist

    crosses = a*a*(a-1) + 2*a*a*(a-2)  # center V or H
    for center in alphabet[2:]:
        _,_,(symbol,state),phase = center
        down_count = a-1 if phase is None else 1
        target,written,move = (None,symbol,0) if state is None else machine.delta(state,symbol)
        if state is None or state == machine.halt:
            nL,_ = neighbor('L',phase,move,True)
            nR,_ = neighbor('R',phase,move,True)
            crosses += down_count*nL*nR
        _,L = neighbor('L',phase,move,False)
        _,R = neighbor('R',phase,move,False)
        if state is not None and move == 0:
            ways = L[None]*R[None]*up_counts[written,target]
        else:
            ways = L[None]*R[None]*up_counts[written,None]
            for incoming in (set(L)|set(R))-{None}:
                ways += (L[incoming]*R[None]+L[None]*R[incoming])*up_counts[written,incoming]
        crosses += down_count*ways
    return crosses*a**4, crosses


def verify():
    m = Machine()
    isomorphism = verify_dense_isomorphism()
    one_step = 0
    for q,side,symbol in product(m.source_states,(0,1),PAIRED):
        bits = PAIRED[symbol]
        n = 0 if symbol in ORIGIN else -1
        original_head = -n if side == 0 else n-1
        target,write,direction = m.native[q,bits[side]]
        p,new_symbol,physical = m.delta(m.sim(q,side),symbol)
        next_n = n+physical
        require(next_n <= 0, 'folded right-boundary escape')
        new_side = 1-side if physical == 0 else side
        decoded_head = -next_n if new_side == 0 else next_n-1
        require(decoded_head == original_head+direction, 'folded head transition')
        require(PAIRED[new_symbol][side] == write and PAIRED[new_symbol][1-side] == bits[1-side], 'folded write')
        require((symbol in ORIGIN) == (new_symbol in ORIGIN), 'origin marker persistence')
        require(p == (HALT if target == 254 else m.sim(target,new_side)), 'folded target')
        one_step += 1
    preprocess = []
    for length in range(1,33):
        tape = {-i:1 for i in range(length)}
        q,n = Q0,0
        for step in range(2*length+2):
            q,b,move = m.delta(q,tape.get(n,0))
            tape[n] = b
            n += move
            require(n <= 0, 'prelude right escape')
        require(q == m.sim(0,0) and n == 0, 'prelude endpoint')
        require(tape[0] == 6 and all(v == 0 for i,v in tape.items() if i != 0), 'prelude blank tape')
        preprocess.append({'unary_length':length,'steps':2*length+2})
    S,E = markers(m)
    require(local_valid(S,m) and local_valid(E,m) and S != E, 'distinct valid markers')
    k,crosses = count_windows(m)
    a = len(tile_alphabet(m))
    require(k > 2 and k <= a**9, 'window count range')
    return dict(source_commit=PIN,native_sha256=m.native_sha256,
                dense_table_isomorphism=isomorphism,
                native_nonhalting_states=len(m.source_states),normalized_states=len(m.states),
                normalized_symbols=len(m.alphabet),normalized_rows=len(m.transitions),
                tiles=a,admissible_crosses=crosses,admissible_windows=k,
                checked_folded_instruction_cases=one_step,prelude_cases=preprocess,
                window_materialized=False,coefficients_materialized=False,
                scope='Finite table normalization and exact window count, not a kernel proof of the final Diophantine equivalence')


def write_outputs():
    m = Machine()
    receipt = verify()
    (HERE/'machine_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    table = dict(states=list(m.states),alphabet=list(m.alphabet),start=Q0,halt=HALT,blank=0,
                 original_state_order=list(m.source_states),
                 transitions=[[q,a,*m.delta(q,a)] for q in m.states for a in m.alphabet],
                 row_format=['state','read','next_state','write','move'])
    (HERE/'normalized_machine.json').write_text(json.dumps(table,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'prelude_cases'},indent=2))


if __name__ == '__main__':
    write_outputs()

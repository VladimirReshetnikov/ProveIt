"""Concrete proof-carrying PA196 command updates over standard naturals.

This is an executable construction, not a PA theorem or a literal-TM binding.
"""
from __future__ import annotations
import importlib.util
from math import isqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pa196_checker_controls',
                                             HERE.parent / 'imported-checker' / 'replay.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
C = checker
TRUTH = 739


def require(ok, message):
    if not ok:
        raise ValueError(message)


def fold_stack(values, tail):
    for item in reversed(values):
        tail = C.pair(item, tail)
    return tail


def decode_atom(atom):
    """Decode every numeric atom, including noncanonical unused payloads."""
    tag, fields = C.decode(atom)
    if tag == 0:
        return ('shift',)
    first, rest = C.decode(fields)
    if tag == 1:
        return ('mp', first)
    second, _ = C.decode(rest)
    return ('ax', tag-2, second, first)


def atom_of(cmd):
    tag, *args = cmd
    if tag == 'shift':
        require(not args, 'shift arity')
        return 0
    if tag == 'mp':
        require(len(args) == 1, 'mp arity')
        return C.pair(1,C.pair(args[0],0))
    if tag == 'ax':
        require(len(args) == 3, 'ax arity')
        a,x,y = args
        return C.pair(a+2,C.pair(y,C.pair(x,0)))
    raise ValueError('unknown command')


def hfs_cons(head, tail):
    """Foundation HFS list adjoin, using its square pair, not the stack pair."""
    return (tail*tail+head if head < tail else head*head+head+tail)+1


def hfs_uncons(value):
    """Decode one nonzero HFS list cell."""
    require(value > 0, 'empty HFS list')
    n = value-1
    side = isqrt(n)
    delta = n-side*side
    return (delta,side) if delta < side else (side,delta-side)


def hfs_word(atoms):
    value = 0
    for atom in reversed(atoms):
        value = hfs_cons(atom,value)
    return value


def numeric_step(store, cmd):
    """Independent transcription of Store.step; None denotes Shift halt."""
    t, w, d, h = store
    tag, *args = cmd
    if tag == 'shift':
        require(not args, 'shift arity')
        if t+h == 1:
            return None
        head, tail = C.decode(w)
        return h, tail, d, head
    if tag == 'mp':
        require(len(args) == 1, 'mp arity')
        (x,) = args
        y = d+x
        return (y, C.pair(0,w), y, 0) if C.I(t,y) == h else (0,w,y,0)
    if tag == 'ax':
        require(len(args) == 3, 'ax arity')
        a,x,y = args
        D,H = d+x,h+y
        gate = 0 if a == H or a == D else C.bundle(H,D,a)
        return gate, fold_stack(C.ax_heads(D,H,a,d,h) + [t], w), 0, 0
    raise ValueError('unknown command')


def proof_step(store, proofs, cmd):
    """Return (certificate for halted formula 1, or next certificate triple).

    The caller must maintain the invariant; successful construction does not
    itself assert a valid certificate. Numeric step uses separate code above.
    """
    t,w,d,h = store
    pt,pw,ph = proofs
    tag,*args = cmd
    if tag == 'shift':
        require(not args, 'shift arity')
        if t+h == 1:
            return ('halt',pt if t == 1 else ph)
        if w == 0:
            return ('live',(ph,pw,TRUTH))
        phead, ptail = C.decode(pw)
        return ('live',(ph,ptail,phead))
    if tag == 'mp':
        require(len(args) == 1, 'mp arity')
        (x,) = args
        y = d+x
        if C.I(t,y) == h:
            return ('live',(C.mp(y,pt,ph), C.pair(TRUTH,pw), TRUTH))
        return ('live',(TRUTH,pw,TRUTH))
    if tag == 'ax':
        require(len(args) == 3, 'ax arity')
        a,x,y = args
        D,H = d+x,h+y
        pgate = TRUTH if a == H or a == D else C.leaf(9,H,D,a)
        stack = fold_stack(C.ax_proofs(D,H,a,d,ph) + [pt], pw)
        return ('live',(pgate,stack,TRUTH))
    raise ValueError('unknown command')


def invariant(store, proofs):
    """Check the numeric-stack prefix; certificates beyond zero are ghosts."""
    t,w,d,h = store
    pt,pw,ph = proofs
    if C.verify(pt) != t+1 or C.verify(ph) != h+1:
        return False
    while w:
        f,nextw = C.decode(w)
        p,nextp = C.decode(pw)
        if C.verify(p) != f+1 or nextw >= w:
            return False
        w,pw = nextw,nextp
    return True


def run_word(commands, store=(0,0,0,0), proofs=(TRUTH,0,TRUTH)):
    require(invariant(store,proofs), 'initial invariant failed')
    for i, cmd in enumerate(commands):
        nxt = numeric_step(store,cmd)
        kind,out = proof_step(store,proofs,cmd)
        if nxt is None:
            require(kind == 'halt' and C.verify(out) == 2, 'halt certificate failed')
            return {'kind':'halt','index':i,'certificate':out}
        require(kind == 'live' and invariant(nxt,out), f'invariant failed after {i}')
        store,proofs = nxt,out
    return {'kind':'live','store':store,'proofs':proofs}


def run_atoms(atoms, store=(0,0,0,0), proofs=(TRUTH,0,TRUTH)):
    return run_word((decode_atom(a) for a in atoms), store, proofs)


def extract_hfs_word(word):
    """Return the native checker proof at first halt, or 0 if word finishes.

    This is the unverified computational extractor. Its proof obligations are
    separate; it deliberately does not call the standard-Nat verifier.
    """
    store = (0,0,0,0)
    proofs = (TRUTH,0,TRUTH)
    while word:
        atom, word = hfs_uncons(word)
        cmd = decode_atom(atom)
        nxt = numeric_step(store,cmd)
        kind,out = proof_step(store,proofs,cmd)
        if nxt is None:
            require(kind == 'halt', 'inconsistent halt branch')
            return out
        require(kind == 'live', 'inconsistent live branch')
        store,proofs = nxt,out
    return 0

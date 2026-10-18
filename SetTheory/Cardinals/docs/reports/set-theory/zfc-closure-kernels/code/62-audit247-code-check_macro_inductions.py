#!/usr/bin/env python3
"""Check explicit induction templates for all four register operations.

This is a small, auditable mathematical symbolic checker, not Lean/Rocq.
Unknown unary lengths are quantified natural numbers. A power step is justified
by induction on the number of repetitions of one literal self-loop transition.
Four one-block theorems are checked with arbitrary left/right contexts, then
lifted by structural induction to every finite list of blocks. The complete
increment/decrement contracts are obtained by composing those derived lemmas
and literal transitions. No bounded examples are used as universal premises.
"""
from __future__ import annotations
from dataclasses import dataclass
import json
from pathlib import Path
from build_machine import ROOT, build, OLD_FINAL_SHA256

@dataclass(frozen=True)
class E:
    """Integer affine expression; run lengths are separately checked nonnegative."""
    c: int = 0
    terms: tuple = ()

    @staticmethod
    def var(name):
        return E(0, ((name, 1),))

    def __add__(self, other):
        if isinstance(other, int):
            other = E(other)
        d = dict(self.terms)
        for k, v in other.terms:
            d[k] = d.get(k, 0) + v
        return E(self.c + other.c, tuple(sorted((k, v) for k, v in d.items() if v)))

    __radd__ = __add__

    def __mul__(self, k):
        return E(k * self.c, tuple((n, k * v) for n, v in self.terms if k * v))

    __rmul__ = __mul__

    def nonnegative(self):
        return self.c >= 0 and all(v >= 0 for n, v in self.terms)

    def __str__(self):
        parts = ([str(self.c)] if self.c else []) + [f"{v}*{n}" for n, v in self.terms]
        return "+".join(parts) or "0"

@dataclass(frozen=True)
class Run:
    bit: int
    length: E

@dataclass(frozen=True)
class Blocks:
    family: str                 # B = 0 1^(v+1); C = 1 0 1^v
    name: str                   # a universally quantified finite list of naturals
    rev: bool = False           # reverse the entire encoded word

@dataclass(frozen=True)
class Context:
    name: str                   # opaque arbitrary context, never inspected

@dataclass(frozen=True)
class Blank:
    pass                       # infinite right blank exterior

def bit(b):
    return Run(b, E(1))

def ones(n):
    return Run(1, n if isinstance(n, E) else E(n))

def B(n):
    return [bit(0), ones(n + 1)]

def C(n):
    return [bit(1), bit(0), ones(n)]

def reverse(word):
    return [Blocks(x.family, x.name, not x.rev) if isinstance(x, Blocks) else x
            for x in reversed(word)]

WORD_IDENTITY_PROVED = False

def norm(word, rewrite=False):
    """Free-word normalization and, once proved, C(A)1 = 1B(A)."""
    global WORD_IDENTITY_PROVED
    out = []
    for atom in word:
        if isinstance(atom, Run):
            assert atom.bit in (0, 1) and atom.length.nonnegative()
            if atom.length == E():
                continue
            if out and isinstance(out[-1], Run) and out[-1].bit == atom.bit:
                atom = Run(atom.bit, out.pop().length + atom.length)
        out.append(atom)
    if len(out) >= 2 and isinstance(out[-1], Blank) and isinstance(out[-2], Run) and out[-2].bit == 0:
        out.pop(-2)
    if WORD_IDENTITY_PROVED and rewrite:
        for i in range(len(out) - 1):
            a, b = out[i:i+2]
            if (isinstance(a, Blocks) and a.family == "C" and not a.rev and
                    isinstance(b, Run) and b.bit == 1 and b.length.c >= 1):
                return norm(out[:i] + [bit(1), Blocks("B", a.name),
                    Run(1, b.length + -1)] + out[i+2:], True)
            if (isinstance(a, Run) and a.bit == 1 and a.length.c >= 1 and
                    isinstance(b, Blocks) and b.family == "C" and b.rev):
                return norm(out[:i] + [Run(1, a.length + -1),
                    Blocks("B", b.name, True), bit(1)] + out[i+2:], True)
    return out

@dataclass
class Conf:
    state: int
    side: str                   # R: head is first right cell; L: first left cell
    left: list                  # nearest cell first
    right: list                 # nearest cell first

    def key(self):
        return self.state, self.side, norm(self.left, self.state == 48 and self.side == "L"), norm(self.right)

    def copy(self):
        return Conf(self.state, self.side, self.left.copy(), self.right.copy())

TABLE = build()
DERIVED = {}

def literal_or_power(conf, cost, motion, trace):
    """Sound local symbolic rules: literal table transition or unary induction."""
    conf.left, conf.right = norm(conf.left, conf.state == 48 and conf.side == "L"), norm(conf.right)
    source = conf.right if conf.side == "R" else conf.left
    target = conf.left if conf.side == "R" else conf.right
    assert source, "missing finite word context"
    atom = source[0]
    if isinstance(atom, Blank):
        assert conf.side == "R"
        source.insert(0, bit(0))
        atom = source[0]
    assert isinstance(atom, Run), (conf.state, conf.side, atom, "opaque context was reached")
    write, direction, successor = TABLE[conf.state, atom.bit]
    same = direction == conf.side and successor == conf.state
    old_state = conf.state
    if same:
        # Base 0: no step, same configuration. Inductive step: one table row,
        # then the same theorem for the remaining length, with updated context.
        length = atom.length
        source.pop(0)
        target.insert(0, Run(write, length))
        cost += length
        motion += length * (1 if direction == "R" else -1)
        trace.append(dict(rule="unary-induction", state=old_state, read=atom.bit,
            row=[write, direction, successor], repetitions=str(length)))
    else:
        assert atom.length.c >= 1, (conf.state, atom, "unjustified unknown-length branch")
        source[0] = Run(atom.bit, atom.length + -1)
        if direction == conf.side:
            target.insert(0, bit(write))
        else:
            source.insert(0, bit(write))
            conf.side = direction
        conf.state = successor
        cost += 1
        motion += 1 if direction == "R" else -1
        trace.append(dict(rule="literal", state=old_state, read=atom.bit,
            row=[write, direction, successor]))
    conf.left, conf.right = norm(conf.left, conf.state == 48 and conf.side == "L"), norm(conf.right)
    return cost, motion

def apply_list_induction(conf, cost, motion, trace):
    """Structural induction on a finite list, from a previously checked block."""
    source = conf.right if conf.side == "R" else conf.left
    if not source or not isinstance(source[0], Blocks):
        return None
    a = source[0]
    key = conf.state, conf.side, a.family, a.rev
    if key not in DERIVED:
        return None
    theorem, destination = DERIVED[key]
    assert theorem in BLOCK_PROOFS
    # The checked block theorem preserves state/orientation, has arbitrary
    # untouched contexts, and crosses exactly one whole block. Thus the empty
    # list is reflexive and the cons case is theorem followed by the IH.
    source.pop(0)
    out = Blocks(destination, a.name, not a.rev)
    (conf.left if conf.side == "R" else conf.right).insert(0, out)
    width = E.var("width_" + a.name)
    cost += width
    motion += width * (1 if conf.side == "R" else -1)
    trace.append(dict(rule="finite-list-induction", theorem=theorem,
        list=a.name, repetitions="all finite list lengths", steps=str(width)))
    return cost, motion

def prove(name, start, finish, wantcost, wantmotion, allow_lists=False):
    c = start.copy()
    cost, motion, trace = E(), E(), []
    for _ in range(1000):
        c.left, c.right = norm(c.left, c.state == 48 and c.side == "L"), norm(c.right)
        if c.key() == finish.key():
            assert cost == wantcost, (name, "steps", cost, wantcost)
            assert motion == wantmotion, (name, "head motion", motion, wantmotion)
            return dict(name=name, status="PASS", universal=True, steps=str(cost),
                head_motion=str(motion), proof_rule_count=len(trace), trace=trace)
        answer = apply_list_induction(c, cost, motion, trace) if allow_lists else None
        if answer is None:
            cost, motion = literal_or_power(c, cost, motion, trace)
        else:
            cost, motion = answer
    raise AssertionError((name, "symbolic proof did not close"))

BLOCK_PROOFS = {}

def prove_blocks():
    x = E.var("v")
    l, r = Context("arbitrary_left"), Context("arbitrary_right")
    data = [
        ("seek73_block", 73, "R", "B", "B"),
        ("carry95_block", 95, "R", "B", "C"),
        ("return48_block", 48, "L", "B", "B"),
        ("rollback112_block", 112, "L", "C", "B"),
    ]
    for name, q, side, source_family, target_family in data:
        before = {"B": B, "C": C}[source_family](x)
        after = {"B": B, "C": C}[target_family](x)
        if side == "R":
            begin = Conf(q, "R", [l], before + [r])
            end = Conf(q, "R", reverse(after) + [l], [r])
            drift = x + 2
        else:
            begin = Conf(q, "L", reverse(before) + [l], [r])
            end = Conf(q, "L", [l], after + [r])
            drift = (x + 2) * -1
        BLOCK_PROOFS[name] = prove(name, begin, end, x + 2, drift)
        # Construct the list rule from the signature that was actually checked.
        # Its same-state/same-orientation endpoint is explicit above.
        DERIVED[(q, side, source_family, side == "L")] = (name, target_family)

def prove_word_identity():
    global WORD_IDENTITY_PROVED
    x = E.var("v")
    assert not WORD_IDENTITY_PROVED
    assert norm([] + [bit(1)]) == norm([bit(1)] + [])
    assert norm(C(x) + [bit(1)]) == norm([bit(1)] + B(x))
    # Cons: C(v) C(A) 1 = C(v) 1 B(A) by IH = 1 B(v) B(A).
    # This uses the definitions of concatenation and encodings, with no tape
    # execution premise. Reversing this equation gives 1 rev(C(A))=rev(B(A)) 1.
    WORD_IDENTITY_PROVED = True
    return dict(status="PASS", induction="finite lists of arbitrary natural numbers",
        base="C([])1 = 1B([])",
        cons="C(v)C(A)1 = C(v)1B(A) = 1B(v)B(A)",
        identity="C(A)1 = 1B(A)", reverse_identity="1rev(C(A)) = rev(B(A))1")

def prove_macros():
    p, s = E.var("width_pre"), E.var("width_suf")
    x, y = E.var("x"), E.var("y")
    a, b = Blocks("B", "pre"), Blocks("B", "suf")
    l, z = Context("arbitrary_left"), Blank()
    out = []
    # x+1 is an arbitrary positive selected register.
    out.append(prove("positive_decrement", Conf(95, "R", [l], [a, bit(0), bit(0), ones(x+1), b, z]),
        Conf(48, "L", [bit(1), l], [a] + B(x) + [b, z]),
        2*p + 4, E(), allow_lists=True))
    # Expose the following block 01^(y+1): this is the precise nonempty-spare premise.
    suffix = B(y) + [b, z]
    out.append(prove("zero_decrement", Conf(95, "R", [l], [a, bit(0), bit(0)] + suffix),
        Conf(112, "L", [l], [a] + B(E()) + suffix),
        2*p + 7, E(-1), allow_lists=True))
    out.append(prove("increment", Conf(73, "R", [l], [a, bit(0), bit(0), ones(x), b, z]),
        Conf(48, "L", [l], [a] + B(x+1) + [b] + B(E(1)) + [z]),
        2*(p+x+s+2) + 7, E(-1), allow_lists=True))
    return out

def prove_marks():
    skip = (60, 44, 31, 56, 38, 40, 28, 64, 69)
    values = [E.var("r" + str(i)) for i in range(9)]
    l = Context("arbitrary_left")
    suffix = [Blocks("B", "spare"), Blank()]
    file = [atom for v in values for atom in B(v)] + suffix
    results = []
    for r, q in enumerate(skip):
        wanted = [atom for v in values[:r] for atom in B(v)] + [bit(0), bit(0), ones(values[r])]
        wanted += [atom for v in values[r+1:] for atom in B(v)] + suffix
        # Mark visits the prefix and the first selected unary cell, then returns.
        # Let the symbolic checker derive the exact number for this finite
        # selector case, while its unary quantities remain universally quantified.
        c = Conf(q, "R", [l], file.copy())
        finish = Conf(2 if r == 0 else 6, "L", [l], wanted)
        cost, motion, trace = E(), E(), []
        for _ in range(1000):
            if c.key() == finish.key():
                assert motion == E(-1)
                results.append(dict(name=f"mark_{r}", status="PASS", universal=True,
                    steps=str(cost), head_motion=str(motion), proof_rule_count=len(trace), trace=trace))
                break
            cost, motion = literal_or_power(c, cost, motion, trace)
        else:
            raise AssertionError((r, "mark did not close"))
    return results

def main():
    if not __debug__:
        raise SystemExit("Assertions are required; do not use -O.")
    prove_blocks()
    word = prove_word_identity()
    macros = prove_macros()
    marks = prove_marks()
    out = dict(status="PASS", exact_table_sha256=OLD_FINAL_SHA256,
        proof_scope="All finite register lists with a selected primary followed by a block; arbitrary register values and left context.",
        kernel_status="Mathematical induction checker; not a proof-assistant kernel endpoint.",
        block_theorems=list(BLOCK_PROOFS.values()), word_identity=word,
        macro_theorems=macros, mark_theorems=marks,
        sound_rules=["literal table row", "unary self-loop induction", "structural finite-block-list induction", "concatenation and reversal identities"])
    (ROOT / "results/macro-inductions.json").write_text(json.dumps(out, indent=2)+"\n", encoding="ascii")
    print(json.dumps({k:v for k,v in out.items() if k not in ("block_theorems", "macro_theorems", "mark_theorems")}, indent=2))
    for row in list(BLOCK_PROOFS.values()) + macros + marks:
        print(row["name"], row["status"], "steps=" + row["steps"], "head=" + row["head_motion"])

if __name__ == "__main__":
    main()

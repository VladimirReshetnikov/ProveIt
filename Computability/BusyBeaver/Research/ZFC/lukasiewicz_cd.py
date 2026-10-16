#!/usr/bin/env python3
"""Condensed-detachment search from Lukasiewicz's single implicational axiom.

Every ZFC-machine calculus in this project keeps the row

    rho8 = ((c -> u) -> a) -> ((a -> c) -> (b -> c)),

which is Lukasiewicz's 1948 single axiom CCCpqrCCrpCsp for the classical
implicational calculus.  This script searches condensed-detachment (CD)
derivations of K, S and Peirce from that axiom alone, replays proof listings
produced by the faster C++ helper `lukasiewicz_search.cpp` (re-deriving and
checking every step with its own unifier), and can emit a stand-alone Lean
module over an arbitrary formula type.  It is an untrusted generator: the
Lean kernel is the correctness boundary.

Regeneration result (16 October 2026): the C++ helper, run as

    lukasiewicz_search.exe 19 5 100000000 K=CpCqp P=CCCpqpp S=CCpCqrCCpqCpr

finds a 107-step chain (`results/lukasiewicz-proof.txt`).  `--compare-lean`
shows that its 107 canonical formulas are exactly those of the attributed
port of Jeff's `CD254.v` certificates in `BusyBeaver/ZFC/Lukasiewicz.lean`.
The certificate is thus what a smallest-first given-clause search produces,
independently reproducible from the axiom alone.

Usage (from this directory):
    py -I lukasiewicz_cd.py --from-proof results/lukasiewicz-proof.txt
        --compare-lean ../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean
    py -I lukasiewicz_cd.py --from-proof results/lukasiewicz-proof.txt
        --emit OUTSIDE/Standalone.lean

Emitting writes a stand-alone module in the `LSystem` namespace; do not emit
over the committed `Lukasiewicz.lean`, whose interface differs.
"""

from __future__ import annotations

import argparse
import heapq
import itertools
import sys
from functools import lru_cache

# A formula is either an int (propositional variable) or a pair (A, B) for A -> B.


@lru_cache(maxsize=None)
def size(f):
    if isinstance(f, int):
        return 1
    return 1 + size(f[0]) + size(f[1])


def variables(f, acc=None):
    if acc is None:
        acc = []
    if isinstance(f, int):
        if f not in acc:
            acc.append(f)
    else:
        variables(f[0], acc)
        variables(f[1], acc)
    return acc


def canon(f):
    """Rename variables to 0,1,2,... in order of first occurrence."""
    m = {v: i for i, v in enumerate(variables(f))}
    return subst(f, m), m


def subst(f, s):
    if isinstance(f, int):
        return s.get(f, f)
    return (subst(f[0], s), subst(f[1], s))


def walk(t, s):
    while isinstance(t, int) and t in s:
        t = s[t]
    return t


def occurs(v, t, s):
    t = walk(t, s)
    if isinstance(t, int):
        return t == v
    return occurs(v, t[0], s) or occurs(v, t[1], s)


def unify(a, b, s):
    a = walk(a, s)
    b = walk(b, s)
    if isinstance(a, int) and isinstance(b, int) and a == b:
        return s
    if isinstance(a, int):
        if occurs(a, b, s):
            return None
        s = dict(s)
        s[a] = b
        return s
    if isinstance(b, int):
        return unify(b, a, s)
    s = unify(a[0], b[0], s)
    if s is None:
        return None
    return unify(a[1], b[1], s)


def resolve(t, s):
    t = walk(t, s)
    if isinstance(t, int):
        return t
    return (resolve(t[0], s), resolve(t[1], s))


def shift(f, k):
    if isinstance(f, int):
        return f + k
    return (shift(f[0], k), shift(f[1], k))


def match(pattern, inst, s):
    """One-sided matching: find s with subst(pattern, s) == inst."""
    if isinstance(pattern, int):
        if pattern in s:
            return s if s[pattern] == inst else None
        s = dict(s)
        s[pattern] = inst
        return s
    if isinstance(inst, int):
        return None
    s = match(pattern[0], inst[0], s)
    if s is None:
        return None
    return match(pattern[1], inst[1], s)


def subsumes(general, specific):
    if size(general) > size(specific):
        return False
    return match(general, specific, {}) is not None


def show(f, names="pqrstuvwxyzabcdefghijklmno"):
    if isinstance(f, int):
        return names[f] if f < len(names) else f"v{f}"
    return "C" + show(f[0], names) + show(f[1], names)


def parse(text):
    """Parse Polish notation with C and lowercase variables."""
    pos = 0
    names = {}

    def go():
        nonlocal pos
        ch = text[pos]
        pos += 1
        if ch == "C":
            a = go()
            b = go()
            return (a, b)
        if ch not in names:
            names[ch] = len(names)
        return names[ch]

    f = go()
    if pos != len(text):
        raise ValueError(text)
    return canon(f)[0]


L_AXIOM = parse("CCCpqrCCrpCsp")


class Theorem:
    __slots__ = ("idx", "f", "major", "minor", "smaj", "smin", "nvars")

    def __init__(self, idx, f, major=None, minor=None, smaj=None, smin=None):
        self.idx = idx
        self.f = f
        self.major = major
        self.minor = minor
        self.smaj = smaj  # substitution for the major's canonical variables
        self.smin = smin  # substitution for the minor's canonical variables
        self.nvars = len(variables(f))


def cd(major: Theorem, minor: Theorem):
    """Condensed detachment: major = A -> B, minor unifies with A."""
    if isinstance(major.f, int):
        return None
    k = major.nvars
    a, b = major.f
    n = shift(minor.f, k)
    s = unify(a, n, {})
    if s is None:
        return None
    result = resolve(b, s)
    cres, ren = canon(result)
    # Substitutions expressed in the result's canonical variables; variables
    # not occurring in the result are left as "free" markers (-1 - var).
    def express(var):
        t = resolve(var, s)
        return rename_or_mark(t, ren)

    smaj = {v: express(v) for v in range(k)}
    smin = {v: express(v + k) for v in range(minor.nvars)}
    return cres, smaj, smin


def rename_or_mark(t, ren):
    if isinstance(t, int):
        return ren[t] if t in ren else ("free", t)
    return (rename_or_mark(t[0], ren), rename_or_mark(t[1], ren))


def search(targets, max_size=27, max_given=4000, verbose=False, seeds=None, ratio=0):
    """Given-clause search.  `seeds` is a list of already-derived Theorem
    objects (with their provenance) used as additional starting points."""
    thms = [Theorem(0, L_AXIOM)]
    if seeds:
        for t in seeds:
            thms.append(t)
    usable: list[Theorem] = []
    queue = [(size(t.f), t.idx) for t in thms]
    heapq.heapify(queue)
    found = {}
    counter = itertools.count(len(thms))
    kept = [t.f for t in thms]

    def check_targets(t):
        for name, tf in targets.items():
            if name not in found and subsumes(t.f, tf):
                found[name] = t.idx

    for t in thms:
        check_targets(t)
    given = 0
    age = [t.idx for t in thms]
    heapq.heapify(age)
    done = set()
    while queue and len(found) < len(targets) and given < max_given:
        # Otter-style pick-given ratio: mostly lightest, sometimes oldest.
        if ratio and given % ratio == ratio - 1 and age:
            idx = heapq.heappop(age)
        else:
            _, idx = heapq.heappop(queue)
        if idx in done:
            continue
        done.add(idx)
        g = thms[idx]
        if any(subsumes(u.f, g.f) for u in usable):
            continue
        usable.append(g)
        given += 1
        new = []
        for u in usable:
            for maj, mino in ((g, u), (u, g)):
                r = cd(maj, mino)
                if r is None:
                    continue
                f, smaj, smin = r
                if size(f) > max_size:
                    continue
                new.append((f, maj.idx, mino.idx, smaj, smin))
        for f, mj, mn, smaj, smin in new:
            if any(subsumes(k, f) for k in kept):
                continue
            t = Theorem(next(counter), f, mj, mn, smaj, smin)
            assert t.idx == len(thms)
            thms.append(t)
            kept.append(f)
            heapq.heappush(queue, (size(f), t.idx))
            heapq.heappush(age, t.idx)
            check_targets(t)
        if verbose and given % 25 == 0:
            print(f"given {given}, kept {len(kept)}, found {sorted(found)}", file=sys.stderr)
    return thms, found


def needed(thms, roots):
    seen = set()
    order = []

    def visit(i):
        if i in seen:
            return
        seen.add(i)
        t = thms[i]
        if t.major is not None:
            visit(t.major)
            visit(t.minor)
        order.append(i)

    for r in roots:
        visit(r)
    return order


# ---------------------------------------------------------------- Lean output


def lean_term(t, default):
    if isinstance(t, tuple) and len(t) == 2 and t[0] == "free":
        return default
    if isinstance(t, int):
        return f"v{t}"
    return f"(imp {lean_term(t[0], default)} {lean_term(t[1], default)})"


def lean_formula(f):
    if isinstance(f, int):
        return f"v{f}"
    return f"(imp {lean_formula(f[0])} {lean_formula(f[1])})"


def emit_lean(thms, found, targets, path):
    order = needed(thms, [found[n] for n in targets])
    name = {i: f"cd{n}" for n, i in enumerate(order)}
    lines = []
    w = lines.append
    w("/-!")
    w("Lukasiewicz's single axiom `CCCpqrCCrpCsp` derives K, S and Peirce.")
    w("")
    w("Every ZFC-machine proof calculus in this project keeps the row")
    w("`rho8 = ((c → u) → a) → ((a → c) → (b → c))` as its only propositional axiom.")
    w("This module proves, for an *arbitrary* formula type with a binary implication")
    w("constructor and an arbitrary predicate closed under modus ponens and that")
    w("axiom, every instance of K, S and Peirce's law, and hence the full classical")
    w("implicational calculus is available to any such machine calculus.")
    w("")
    w("The condensed-detachment steps were found by the independent search")
    w("`Computability/BusyBeaver/Research/ZFC/lukasiewicz_cd.py`, which also")
    w("generated this file; the Lean kernel checks every step.  No equality of")
    w("formulas, injectivity of `imp`, or decoding is assumed: a code calculus whose")
    w("`imp` collapses some codes (such as the runtime truth alias `0 = imp 0 0`)")
    w("satisfies the same hypotheses.")
    w("-/")
    w("")
    w("namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz")
    w("")
    w("universe u")
    w("variable {α : Type u} {imp : α → α → α} {T : α → Prop}")
    w("")
    w("/-- A theorem predicate containing the Lukasiewicz axiom and closed under MP. -/")
    w("structure LSystem (imp : α → α → α) (T : α → Prop) : Prop where")
    w("  mp : ∀ {a b : α}, T (imp a b) → T a → T b")
    w("  ax : ∀ p q r s : α, T (imp (imp (imp p q) r) (imp (imp r p) (imp s p)))")
    w("")
    w("namespace LSystem")
    w("")
    w("variable (h : LSystem imp T)")
    w("include h")
    w("")
    for i in order:
        t = thms[i]
        nv = t.nvars
        binders = " ".join(f"v{k}" for k in range(nv))
        stmt = f"T {lean_formula(t.f)}"
        quant = f"∀ {binders} : α, " if nv else ""
        w(f"theorem {name[i]} : {quant}{stmt} := by")
        if nv:
            w(f"  intro {binders}")
        default = "v0" if nv else None
        if t.major is None:
            # The axiom itself, in canonical variable order p q r s.
            w("  exact h.ax v0 v1 v2 v3")
        else:
            maj = thms[t.major]
            mn = thms[t.minor]
            margs = " ".join(lean_term(t.smaj[k], default) for k in range(maj.nvars))
            nargs = " ".join(lean_term(t.smin[k], default) for k in range(mn.nvars))
            w(f"  exact h.mp ({name[t.major]} h {margs}) ({name[t.minor]} h {nargs})")
        w("")
    for tname, tf in targets.items():
        i = found[tname]
        t = thms[i]
        nv = len(variables(tf))
        binders = " ".join(f"v{k}" for k in range(nv))
        s = match(t.f, tf, {})
        args = " ".join(lean_term(s.get(k, 0) if k in s else 0, "v0") for k in range(t.nvars))
        w(f"/-- `{show(tf)}` -/")
        w(f"theorem {tname} : ∀ {binders} : α, T {lean_formula(tf)} := by")
        w(f"  intro {binders}")
        w(f"  exact {name[i]} h {args}")
        w("")
    w("end LSystem")
    w("")
    w("end SetTheory.BusyBeaver.ZFC.Lukasiewicz")
    w("")
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(lines))
    return order


TARGETS = {
    "imp_K": parse("CpCqp"),
    "imp_S": parse("CCpCqrCCpqCpr"),
    "peirce": parse("CCCpqpp"),
}


def parse_letters(text):
    """Parse the C++ helper's output: 'C' and lowercase letters a, b, ..."""
    pos = 0

    def go():
        nonlocal pos
        ch = text[pos]
        pos += 1
        if ch == "C":
            a = go()
            b = go()
            return (a, b)
        return ord(ch) - ord("a")

    f = go()
    if pos != len(text):
        raise ValueError(text)
    return f


def replay(lines):
    """Re-derive a proof listing 'id major minor formula' with this module's
    own condensed detachment, checking every step against the listing.
    Returns a theorem list in proof order and a map from listing ids."""
    thms = [Theorem(0, L_AXIOM)]
    index = {}
    for line in lines:
        parts = line.split()
        if not parts or parts[0] == "TARGET":
            continue
        ident, major, minor, text = int(parts[0]), int(parts[1]), int(parts[2]), parts[3]
        claimed = canon(parse_letters(text))[0]
        if major < 0:
            if claimed != L_AXIOM:
                raise ValueError("unexpected axiom line")
            index[ident] = 0
            continue
        mj, mn = thms[index[major]], thms[index[minor]]
        r = cd(mj, mn)
        if r is None:
            raise ValueError(f"step {ident} does not detach")
        f, smaj, smin = r
        if f != claimed:
            raise ValueError(f"step {ident}: {show(f)} != {show(claimed)}")
        t = Theorem(len(thms), f, mj.idx, mn.idx, smaj, smin)
        thms.append(t)
        index[ident] = t.idx
    return thms, index


def lean_statements(path):
    """Canonical formulas of the `T (imp ...)` statements in a Lean file."""
    import re

    text = open(path, encoding="utf-8").read()
    out = []
    for mt in re.finditer(r"T \((imp .*?)\) :=", text, re.S):
        toks = re.findall(r"\(|\)|imp|v\d+", mt.group(1))
        toks = ["("] + toks + [")"]
        pos = 0

        def go():
            nonlocal pos
            t = toks[pos]
            pos += 1
            if t == "(":
                assert toks[pos] == "imp"
                pos += 1
                a = go()
                b = go()
                assert toks[pos] == ")"
                pos += 1
                return (a, b)
            return int(t[1:])

        # Only certificate statements over v0, v1, ... are compared; wrapper
        # theorems stated over other names are skipped.
        try:
            f = go()
        except (AssertionError, IndexError, ValueError):
            continue
        if pos == len(toks):
            out.append(canon(f)[0])
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit")
    ap.add_argument("--max-size", type=int, default=27)
    ap.add_argument("--max-given", type=int, default=4000)
    ap.add_argument("-v", "--verbose", action="store_true")
    ap.add_argument("--from-proof", help="replay a proof listing from the C++ helper")
    ap.add_argument("--compare-lean", help="compare replayed formulas with a Lean certificate file")
    args = ap.parse_args(argv)
    if args.from_proof:
        lines = open(args.from_proof, encoding="utf-8").read().splitlines()
        thms, _ = replay(lines)
        found = {}
        for name, tf in TARGETS.items():
            for t in thms:
                if subsumes(t.f, tf):
                    found[name] = t.idx
                    break
        missing = [n for n in TARGETS if n not in found]
        if missing:
            print("missing after replay:", missing)
            return 1
        print(f"replayed {len(thms)} steps; all targets found")
        if args.compare_lean:
            mine = {t.f for t in thms}
            theirs = set(lean_statements(args.compare_lean))
            print(f"compared with {args.compare_lean}: {len(theirs)} certificate formulas, "
                  f"{len(mine & theirs)} common, {len(theirs - mine)} only there, "
                  f"{len(mine - theirs)} only here")
        if args.emit:
            order = emit_lean(thms, found, TARGETS, args.emit)
            print(f"wrote {args.emit} with {len(order)} derivation steps")
        return 0
    thms, found = search(TARGETS, args.max_size, args.max_given, args.verbose)
    missing = [n for n in TARGETS if n not in found]
    for n in TARGETS:
        if n in found:
            print(f"{n}: {show(TARGETS[n])} via #{found[n]} = {show(thms[found[n]].f)}")
    if missing:
        print("missing:", missing)
        return 1
    order = needed(thms, [found[n] for n in TARGETS])
    print(f"derivation uses {len(order)} theorems (including the axiom)")
    if args.emit:
        emit_lean(thms, found, TARGETS, args.emit)
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Render DomRho8 (Lean and Rocq) from a condensed-detachment derivation.

  python generate_domrho8_cd.py [--derivation derivation.txt] [--lean OUT.lean] [--rocq OUT.v]
  python generate_domrho8_cd.py --derivation derivation_core.txt --core DominatedImplication.lean
  python generate_domrho8_cd.py --derivation derivation_luk.txt --luk Lukasiewicz.lean
  python generate_domrho8_cd.py --derivation derivation_luk.txt --rocq-cd CD222.v

The derivation (found by the untrusted search in search/) lists formulas over
implication `>`, the code `Z` = 0 (with Z > Z = Z) and variables a, b, ...  Line
`i j k F [C]` says that F follows by modus ponens from major j and minor k, under
side conditions C (`x<=y`).  Leaf -1 is truth `Z`; leaf -2 is the dominated row
((a>b)>c)>((c>a)>(d>a)) [b<=c], i.e. `rho8 c d a b` with `b <= c`.  Lines
`#GOAL i F` name the lemma proving each public statement (by default the last line,
which must then generalize that row with no side condition).

--core renders a derivation without truth (no leaf -1 and no Z) as the
representation-independent DominatedImplication module: an arbitrary binary
connective with a reflexive `below` relation closed under insertion into either
operand.  Its goals are the row, composition ((a>b)>((b>c)>(a>c))) and
prefixing ((a>b)>((c>a)>(c>b))), and, when the derivation has them, K, Peirce
and S (exported as k, peirce, s for the unrestricted Lukasiewicz adapter).

--luk renders a derivation from the unrestricted row (no side conditions, no
truth) as the Lukasiewicz namespace of Lukasiewicz.lean: K, Peirce, S and, when
the derivation has that goal, composition.  The rest of the file (the Tarski
bridge after the namespace) is kept verbatim.  --rocq-cd renders the same
derivation as the Rocq lane's CD222.v (thm_K, thm_P, thm_B, thm_S over thm222).

Each step becomes one lemma.  The renderer recomputes the most general unifier,
so the premises' instances are explicit and every `u <= a` is proved from
`le_l`/`le_r` (u a literal subterm of a), `0 <= a`, or a hypothesis of the lemma.
The kernels check every step; nothing here is trusted.
"""
import argparse
from pathlib import Path

HERE = Path(__file__).resolve().parent
Z = -1


# ---------- formulas: int >= 0 variable, Z, or (antecedent, consequent) ----------

def parse(s):
    pos = 0

    def go():
        nonlocal pos
        c = s[pos]
        pos += 1
        if c == '(':
            a = go()
            assert s[pos] == '>'
            pos += 1
            b = go()
            assert s[pos] == ')'
            pos += 1
            return (a, b)
        return Z if c == 'Z' else ord(c) - ord('a')

    t = go()
    assert pos == len(s), s
    return t


def norm(t):
    if isinstance(t, tuple):
        a, b = norm(t[0]), norm(t[1])
        return Z if a == Z and b == Z else (a, b)
    return t


def walk(t, s):
    while isinstance(t, int) and t in s:
        t = s[t]
    return t


def occurs(v, t, s):
    t = walk(t, s)
    return t == v or (isinstance(t, tuple) and (occurs(v, t[0], s) or occurs(v, t[1], s)))


def unify(x, y, s):
    """Most general unifier modulo Z = Z > Z."""
    todo = [(x, y)]
    while todo:
        x, y = (walk(t, s) for t in todo.pop())
        if x == y:
            continue
        if isinstance(x, int) and x >= 0 and not occurs(x, y, s):
            s[x] = y
        elif isinstance(y, int) and y >= 0 and not occurs(y, x, s):
            s[y] = x
        elif x == Z and isinstance(y, tuple):
            todo += [(Z, y[0]), (Z, y[1])]
        elif y == Z and isinstance(x, tuple):
            todo += [(x[0], Z), (x[1], Z)]
        elif isinstance(x, tuple) and isinstance(y, tuple):
            todo += [(x[0], y[0]), (x[1], y[1])]
        else:
            raise ValueError('no unifier')
    return s


def subst(t, s):
    t = walk(t, s)
    return (subst(t[0], s), subst(t[1], s)) if isinstance(t, tuple) else t


def rename(t, f):
    return (rename(t[0], f), rename(t[1], f)) if isinstance(t, tuple) else (t if t == Z else f(t))


def variables(t, acc):
    if isinstance(t, tuple):
        variables(t[0], acc)
        variables(t[1], acc)
    elif t >= 0 and t not in acc:
        acc.append(t)
    return acc


def subterm(u, a):
    return u == a or (isinstance(a, tuple) and (subterm(u, a[0]) or subterm(u, a[1])))


def match(g, t, s):
    """Extend s so that g instantiated by s is t (variables of t are constants)."""
    if isinstance(g, int) and g >= 0:
        if s.setdefault(g, t) != t:
            raise ValueError('no match')
    elif g == Z or not isinstance(g, tuple):
        if g != t:
            raise ValueError('no match')
    else:
        if not isinstance(t, tuple):
            raise ValueError('no match')
        match(g[0], t[0], s)
        match(g[1], t[1], s)
    return s


def has_zz(t):
    return isinstance(t, tuple) and ((t[0] == Z and t[1] == Z) or has_zz(t[0]) or has_zz(t[1]))


# ---------- derivation ----------

ROW = parse('(((a>b)>c)>((c>a)>(d>a)))')


def read(path):
    rows, goals = {}, []
    for line in path.read_text(encoding='utf-8').splitlines():
        if line.startswith('#GOAL '):
            _, i, f = line.split(' ')
            goals.append((int(i), parse(f)))
        if not line.strip() or line.startswith(('#', 'PROOF')):
            continue
        i, j, k, f, cs = line.split(' ', 4)
        cs = cs.strip()[1:-1]
        cons = [tuple(parse(x) for x in c.split('<=')) for c in split(cs)] if cs else []
        rows[int(i)] = (int(j), int(k), parse(f), cons)
    return rows, goals or [(max(rows), ROW)]


def split(s):
    parts, depth, cur = [], 0, ''
    for ch in s:
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
            continue
        depth += (ch == '(') - (ch == ')')
        cur += ch
    return parts + [cur]


def steps(rows, core=False):
    out = []
    names = _steps(rows, out, core)
    return out, names


def _steps(rows, out, core):
    """Yield (name, formula, side conditions, major, minor) with explicit instances.

    major/minor are (kind, name, arguments, side-condition instances) where kind is
    'truth', 'row' or 'lemma'; every instance is in the variables of the formula."""
    names = {}
    k = 0
    for i in sorted(rows):
        j, m, t, cons = rows[i]
        if j < 0:
            names[i] = 'truth' if j == -1 else 'row'
            continue
        k += 1
        names[i] = 'd%d' % k
        (jt, jc), (mt, mc) = (rows[j][2:]), (rows[m][2:])
        off = 1 + max(variables(jt, []) + [v for c in jc for x in c for v in variables(x, [])] + [-1])
        mt = rename(mt, lambda v: v + off)
        mc = [tuple(rename(x, lambda v: v + off) for x in c) for c in mc]
        x, y = (Z, Z) if jt == Z else jt
        su = unify(x, mt, {})
        res = norm(subst(y, su))
        side = [tuple(norm(subst(x, su)) for x in c) for c in jc + mc]
        side = [c for c in side if not (c[0] == Z or subterm(*c))]
        # a side-condition variable occurring nowhere else is chosen: lhs := Z (core: rhs), rhs := lhs;
        # other variables lost by the unifier become Z (core: the lemma's first variable)
        free = {}
        changed = True
        while changed:
            changed = False
            for c in side:
                other = variables(res, [])
                for d in side:
                    if d is not c:
                        variables(d[0], other)
                        variables(d[1], other)
                a, b = c
                if isinstance(a, int) and a >= 0 and a not in other and a not in variables(b, []):
                    free[a] = b if core else Z
                elif isinstance(b, int) and b >= 0 and b not in other and b not in variables(a, []):
                    free[b] = a
                else:
                    continue
                side.remove(c)
                changed = True
                break
        ren = match(res, t, {})
        assert len(side) == len(cons), (i, side, cons)
        for c, d in zip(side, cons):
            match(c, d, ren)

        def inst(v):
            def fin(x):
                if isinstance(x, tuple):
                    return (fin(x[0]), fin(x[1]))
                if x == Z:
                    return Z
                return fin(free[x]) if x in free else ren.get(x, variables(t, [])[0] if core else Z)
            return norm(fin(subst(v, su)))

        def premise(ix, shift, f, fc):
            if names[ix] == 'truth':
                return ('truth', None, [], [], False)
            vs = variables(f, [])
            for c in fc:
                variables(c[0], vs)
                variables(c[1], vs)
            args = [inst(v + shift) for v in range(max(vs) + 1)] if vs else []
            value = lambda x: rename(x, lambda v: args[v])
            hb = [tuple(norm(value(x)) for x in c) for c in fc]
            return (names[ix], names[ix], args, hb, has_zz(value(f)))

        out.append((names[i], t, cons, premise(j, 0, jt, jc), premise(m, off, *rows[m][2:])))
    return names


# ---------- rendering ----------

class Var:
    """A named variable of a public statement."""
    def __init__(self, name):
        self.name = name

    def __eq__(self, other):
        return isinstance(other, Var) and other.name == self.name

    def __hash__(self):
        return hash(self.name)


class Syntax:
    def __init__(self, mode):
        self.rocq = mode == 'rocq'
        self.rcd = mode == 'rocqcd'
        self.luk = mode in ('luk', 'rocqcd')
        self.core = mode in ('core', 'luk', 'rocqcd')

    def term(self, t, top=True):
        if isinstance(t, Var):
            return t.name
        if isinstance(t, tuple):
            s = '%s %s %s' % ('imp' if self.luk and not self.rcd else 'wim', self.term(t[0], False), self.term(t[1], False))
            return s if top else '(' + s + ')'
        return '0' if t == Z else 'v%d' % t

    def le(self, u, a, hyps):
        if (u, a) in hyps:
            return 'hb%d' % hyps.index((u, a))
        if u == Z and not self.core:
            return '(Nat.le_0_l _)' if self.rocq else '(Nat.zero_le _)'
        if u == a:
            return '(le_n _)' if self.rocq else '(L.refl _)' if self.core else '(Nat.le_refl _)'
        if isinstance(a, tuple) and subterm(u, a[0]):
            return '(le_l %s %s)' % (self.term(a[1], False), self.le(u, a[0], hyps))
        if isinstance(a, tuple) and subterm(u, a[1]):
            return '(le_r %s %s)' % (self.term(a[0], False), self.le(u, a[1], hyps))
        raise ValueError('no proof of %r <= %r' % (u, a))

    def use(self, p, hyps):
        kind, name, args, hb, _ = p
        if kind == 'truth':
            assert not self.core, 'the core has no truth'
            return '(dtruth h)' if self.rocq else 'h.truth'
        if kind == 'row':
            pa, q, r, s = (args + [Z] * 4)[:4]
            if self.rcd:
                return '(W_r8 %s)' % ' '.join(self.term(x, False) for x in (r, s, pa, q))
            if self.luk:
                return '(h.rho8 %s)' % ' '.join(self.term(x, False) for x in (pa, q, r, s))
            head = 'drho8 h' if self.rocq else 'h.rho8'
            return '(%s %s %s)' % (head, ' '.join(self.term(x, False) for x in (r, s, pa, q)),
                                   self.le(q, r, hyps))
        pieces = [name] + ([] if self.rocq or self.rcd else ['h']) + [self.term(x, False) for x in args]
        pieces += [self.le(u, a, hyps) for u, a in hb]
        return '(' + ' '.join(pieces) + ')'

    def lemma(self, name, t, cons, major, minor):
        vs = variables(t, [])
        for c in cons:
            variables(c[0], vs)
            variables(c[1], vs)
        binders = ' '.join('v%d' % v for v in sorted(vs))
        hyps = ''.join(' (hb%d : %s %s %s)' % (k, self.term(a), '<=' if self.rocq else '≼' if self.core else '≤',
                                                self.term(b))
                       for k, (a, b) in enumerate(cons))
        mp = '%s %s' % (self.use(major, cons), self.use(minor, cons))
        if self.rocq:
            assert not (major[4] or minor[4]), 'Rocq rendering expects Z-normal instances'
            return 'Lemma %s%s%s :\n  T (%s).\nProof. exact (dmp h _ _ %s). Qed.\n' % (
                name, ' ' + binders if binders else '', hyps, self.term(t), mp)
        assert not (self.core and (major[4] or minor[4]))
        if self.rcd:
            assert not cons
            return 'Lemma %s%s : thm222 (%s).\nProof. exact (W_mp _ _ %s %s). Qed.' % (
                name, ' (%s : nat)' % binders if binders else '', self.term(t),
                self.use(minor, cons), self.use(major, cons))
        if self.luk:
            assert not cons
            return 'private theorem %s (h : Implicational imp T)%s :\n    T (%s) :=\n  h.mp %s\n' % (
                name, ' (%s : α)' % binders if binders else '', self.term(t), mp)
        body = ('by simpa only [wim00] using h.mp ' if major[4] or minor[4] else 'h.mp ') + mp
        return 'private theorem %s%s%s :\n    T (%s) :=\n  %s\n' % (
            name, ' (%s : %s)' % (binders, 'A' if self.core else 'Nat') if binders else '', hyps,
            self.term(t), body)

    def instance(self, lemma, goal, names):
        """Arguments applying the lemma for formula `lemma` to the goal (variables -> names)."""
        s = match(lemma, goal, {})
        name = lambda x: rename(x, lambda v: Var(names[v]))
        return ' '.join(self.term(name(s[v]), False) for v in sorted(variables(lemma, [])))


LEAN_HEAD = '''import BusyBeaver.ZFC.Code254

/-!
Dominated rho8 derives unrestricted rho8, for arbitrary natural codes.

`rho8 a b c u` is Lukasiewicz's single axiom ((c → u) → a) → ((a → c) → (b → c)) of the
implicational calculus; `DomImp` grants it only when `u ≤ a`. The {n} lemmas below are one
condensed-detachment derivation of the unrestricted row from truth, modus ponens and the
dominated rows, generated by `Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py` from
`rho8cd/derivation.txt` (found by the untrusted search in `rho8cd/search/`; the Rocq lane's
`DomRho8.v` renders the same derivation). Each side condition `u ≤ a` holds because `u` is a
literal subterm of `a` (`le_l`, `le_r`), is the code 0, or is a hypothesis of the lemma.
-/

namespace SetTheory.BusyBeaver.ZFC.DomRho8

open Code254

/-- Truth, modus ponens and the dominated rho8 instances. -/
structure DomImp (T : Nat → Prop) : Prop where
  truth : T 0
  mp : ∀ {{a b : Nat}}, T (wim a b) → T a → T b
  rho8 : ∀ a b c u : Nat, u ≤ a → T (Code254.rho8 a b c u)

theorem le_l {{u x : Nat}} (y : Nat) (h : u ≤ x) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_left x y; simp only [wim]; omega)

theorem le_r {{u y : Nat}} (x : Nat) (h : u ≤ y) : u ≤ wim x y :=
  Nat.le_trans h (by have := le_P_right x y; simp only [wim]; omega)

/-- A substitution: the valuation sending variable `i` to the `i`-th code. -/
def sub (l : List Nat) (i : Nat) : Nat := l.getD i 0

theorem wim00 : wim 0 0 = 0 := by simp [wim, P, Cantor.toNat, Cantor.tri]
attribute [local irreducible] wim

section
variable {{T : Nat → Prop}} (h : DomImp T)
include h

'''

LEAN_TAIL = '''/-- Every rho8 instance follows from the dominated ones. -/
theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) := {row}

end
#print axioms rho8_all
end SetTheory.BusyBeaver.ZFC.DomRho8
'''

ROCQ_HEAD = '''(** Dominated rho8 derives every rho8 instance.

    [rho8 a b c u] is Lukasiewicz's single axiom ((c -> u) -> a) -> ((a -> c) -> (b -> c));
    [DomImp] grants it only when [u <= a]. The {n} lemmas are the condensed-detachment
    derivation of k225-formal/rho8cd/derivation.txt, rendered by generate_domrho8_cd.py
    exactly as for the Lean DomRho8 (the search that found it is untrusted). *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.

Record DomImp (T : nat -> Prop) : Prop := {{
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }}.
Arguments dtruth {{T}} _.
Arguments dmp {{T}} _ _ _ _ _.
Arguments drho8 {{T}} _ _ _ _ _ _.

Lemma le_l {{u x}} y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {{u y}} x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

Section Derivation.
Variable T : nat -> Prop.
Variable h : DomImp T.
Local Opaque wim.

'''

ROCQ_TAIL = '''(** Every rho8 instance follows from the dominated ones. *)
Theorem rho8_all a b c u : T (rho8 a b c u).
Proof. exact ({row}). Qed.

End Derivation.
Print Assumptions rho8_all.
'''


COMPOSITION = parse('((a>b)>((b>c)>(a>c)))')
PREFIX = parse('((a>b)>((c>a)>(c>b)))')
ROW_NAMES = ['c', 'u', 'a', 'b']       # rho8 a b c u = ((c > u) > a) > ((a > c) > (b > c))


K = parse('(a>(b>a))')
PEIRCE = parse('(((a>b)>a)>a)')
S = parse('((a>(b>c))>((a>b)>(a>c)))')
LUK_END = 'end SetTheory.BusyBeaver.ZFC.Lukasiewicz\n'


def render(rows, goals, mode, keep=''):
    syn = Syntax(mode)
    lemmas, names = steps(rows, mode in ('core', 'luk', 'rocqcd'))
    body = [syn.lemma(*s) for s in lemmas]
    if mode == 'rocqcd':
        need = [(K, ['p', 'q']), (PEIRCE, ['p', 'q']), (COMPOSITION, ['p', 'q', 'r']), (S, ['p', 'q', 'r'])]
    elif mode == 'luk':
        need = [(K, ['a', 'b']), (PEIRCE, ['a', 'b']), (S, ['a', 'b', 'c'])]
        need += [(COMPOSITION, ['a', 'b', 'c'])] if any(g == COMPOSITION for _, g in goals) else []
    else:
        need = [(ROW, ROW_NAMES)] + ([(COMPOSITION, ['a', 'b', 'c']), (PREFIX, ['a', 'b', 'x'])] if mode == 'core' else [])
        if mode == 'core':
            need += [(g, n) for g, n in ((K, ['a', 'b']), (PEIRCE, ['a', 'b']), (S, ['a', 'b', 'c']))
                     if any(h == g for _, h in goals)]
    use = {}
    for goal, vnames in need:
        i = next(i for i, g in goals if g == goal)
        assert not rows[i][3], 'a public statement has no side condition'
        use[goal] = '%s h %s' % (names[i], syn.instance(rows[i][2], goal, vnames)) if mode not in ('rocq', 'rocqcd') else \
            '%s %s' % (names[i], syn.instance(rows[i][2], goal, vnames))
    if mode == 'rocqcd':
        return RCD_HEAD.format(n=len(body)) + '\n'.join(body) + '\n' + RCD_TAIL.format(
            k=use[K], p=use[PEIRCE], b=use[COMPOSITION], s=use[S])
    if mode == 'luk':
        tail = LUK_TAIL.format(k=use[K], peirce=use[PEIRCE], s=use[S])
        if COMPOSITION in use:
            tail = tail.replace(LUK_S_DOC, LUK_COMPOSITION.format(composition=use[COMPOSITION]) + LUK_S_DOC)
        return LUK_HEAD.format(n=len(body)) + '\n'.join(body) + '\n' + tail + keep
    head, tail = {'lean': (LEAN_HEAD, LEAN_TAIL), 'rocq': (ROCQ_HEAD, ROCQ_TAIL), 'core': (CORE_HEAD, CORE_TAIL)}[mode]
    if mode == 'core' and K in use:
        tail = tail.replace(CORE_END, CORE_BASIS + CORE_END).replace(CORE_AXIOMS, CORE_AXIOMS + CORE_BASIS_AXIOMS)
    return head.format(n=len(body)) + '\n'.join(body) + '\n' + tail.format(
        row=use[ROW], composition=use.get(COMPOSITION), prefix=use.get(PREFIX),
        k=use.get(K), peirce=use.get(PEIRCE), s=use.get(S))


CORE_HEAD = '''import Init

/-!
A representation-independent dominated implication theorem.

`rho8 L a b c u` is Lukasiewicz's single axiom ((c → u) → a) → ((a → c) → (b → c)) of the
implicational calculus; `Restricted` grants it only when `u` is below `a`. The {n} lemmas
below are one condensed-detachment derivation of the unrestricted row, composition and
prefixing from modus ponens and the restricted rows alone, generated by
`Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py --core` from `rho8cd/derivation_core.txt`
(found by the untrusted search in `rho8cd/search/`). Each side condition holds by reflexivity
and insertion into an implication operand, or is a hypothesis of the lemma; no truth value,
formula decoder, injectivity or transitivity is assumed.
-/
namespace SetTheory.BusyBeaver.ZFC.DominatedImplication

universe v

structure Language (A : Type v) where
  imp : A → A → A
  below : A → A → Prop
  refl : ∀ a, below a a
  grow_left : ∀ {{u x : A}} (y : A), below u x → below u (imp x y)
  grow_right : ∀ {{u y : A}} (x : A), below u y → below u (imp x y)

def rho8 {{A : Type v}} (L : Language A) (a b c u : A) : A :=
  L.imp (L.imp (L.imp c u) a) (L.imp (L.imp a c) (L.imp b c))

structure Restricted {{A : Type v}} (L : Language A) (T : A → Prop) : Prop where
  mp : ∀ {{a b : A}}, T (L.imp a b) → T a → T b
  rho8 : ∀ a b c u : A, L.below u a → T (DominatedImplication.rho8 L a b c u)

section
variable {{A : Type v}} {{L : Language A}} {{T : A → Prop}}
local notation "wim" => L.imp
local infix:50 " ≼ " => L.below

private theorem le_l {{u x : A}} (y : A) (h : u ≼ x) : u ≼ wim x y :=
  L.grow_left y h
private theorem le_r {{u y : A}} (x : A) (h : u ≼ y) : u ≼ wim x y :=
  L.grow_right x h

variable (h : Restricted L T)
include h

'''

CORE_TAIL = '''/-- Restricted rows and modus ponens alone derive every unrestricted row. -/
theorem rho8_all (a b c u : A) : T (rho8 L a b c u) :=
  {row}

theorem composition (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  {composition}

/-- A proved implication lifts under any antecedent. -/
theorem lift_right {{a b : A}} (hab : T (L.imp a b)) (x : A) :
    T (L.imp (L.imp x a) (L.imp x b)) :=
  h.mp ({prefix}) hab

end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
end SetTheory.BusyBeaver.ZFC.DominatedImplication
'''


CORE_END = 'end\n#print axioms rho8_all\n'
CORE_AXIOMS = '#print axioms lift_right\n'
CORE_BASIS = '''/-- The classical basis K, Peirce and S, from the same derivation. -/
theorem k (a b : A) : T (L.imp a (L.imp b a)) :=
  {k}

theorem peirce (a b : A) : T (L.imp (L.imp (L.imp a b) a) a) :=
  {peirce}

theorem s (a b c : A) : T (L.imp (L.imp a (L.imp b c)) (L.imp (L.imp a b) (L.imp a c))) :=
  {s}

'''
CORE_BASIS_AXIOMS = '#print axioms k\n#print axioms peirce\n#print axioms s\n'

LUK_HEAD = '''import BusyBeaver.ZFC.TarskiComplete

/-!
Finite implicational certificates and the unconditional Tarski logic bridge.

K, S and Peirce follow from modus ponens and Lukasiewicz's single axiom rho8
((c → u) → a) → ((a → c) → (b → c)) alone. The {n} lemmas below are one
condensed-detachment derivation, generated by
`Research/ZFC/k225-formal/rho8cd/generate_domrho8_cd.py --luk` from
`rho8cd/derivation_luk.txt` and found by the untrusted search in `rho8cd/search/`,
seeded with the statements of the 107-step DAG of Jeff's `ZF/m254/coq/logic/CD254.v`
(busy-beaver commit `297ab8df7e5de329605c3875b4934643b371a5e3`, Mira-Cult's
machine) that this module previously ported. No implication injectivity or
assumption about falsity is used.

Ex falso additionally uses the original rho6, whose existential is defined
relative to `NF.bot`. Thus `Tarski.classical` supplies both explicit hypotheses
of the previously conditional `Tarski.completeness`, for any theory predicate `Ax`.

This concerns the named syntax with primitive falsity. It does not identify
that syntax with numerical machine codes, justify the runtime falsity
alias, verify a theory bundle, or prove a binary machine consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz

universe u
variable {{α : Type u}}

/-- Only the actual implicational row and its inference rule. -/
structure Implicational (imp : α → α → α) (T : α → Prop) : Prop where
  mp : ∀ {{a b}}, T (imp a b) → T a → T b
  rho8 : ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))

variable {{imp : α → α → α}} {{T : α → Prop}}

'''

RCD_HEAD = '''(** * CD222: implicational theorems of thm222 from the Lukasiewicz row rho8 alone.

    The {n} lemmas are the condensed-detachment derivation of k225-formal/rho8cd/derivation_luk.txt,
    rendered by generate_domrho8_cd.py --rocq-cd exactly as the Lean Lukasiewicz.lean (the search
    that found it, seeded with the statements of the pinned m254/CD254.v, is untrusted). *)
From K230L Require Import Codes230.
From K215F Require Import Thm222.

'''
RCD_TAIL = '''
Lemma thm_K (p q : nat) : thm222 (wim p (wim q p)).
Proof. exact ({k}). Qed.
Lemma thm_P (p q : nat) : thm222 (wim (wim (wim p q) p) p).
Proof. exact ({p}). Qed.
Lemma thm_B (p q r : nat) : thm222 (wim (wim p q) (wim (wim q r) (wim p r))).
Proof. exact ({b}). Qed.
Lemma thm_S (p q r : nat) : thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))).
Proof. exact ({s}). Qed.
'''

LUK_S_DOC = '/-- S follows from rho8 alone. -/\n'
LUK_COMPOSITION = '''/-- Implication composition. -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) := {composition}

'''
LUK_TAIL = '''/-- K follows from rho8 alone. -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  {k}

/-- Peirce follows from rho8 alone. -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) := {peirce}

/-- S follows from rho8 alone. -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := {s}

'''


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--derivation', type=Path, default=HERE / 'derivation.txt')
    ap.add_argument('--lean', type=Path)
    ap.add_argument('--rocq', type=Path)
    ap.add_argument('--core', type=Path)
    ap.add_argument('--rocq-cd', type=Path)
    ap.add_argument('--luk', type=Path, help='Lukasiewicz.lean to rewrite in place (its tail is kept)')
    a = ap.parse_args()
    rows, goals = read(a.derivation)
    if a.luk:
        text = a.luk.read_text(encoding='utf-8')
        keep = LUK_END + text.split(LUK_END, 1)[1]
        a.luk.write_text(render(rows, goals, 'luk', keep), encoding='utf-8', newline='\n')
    for path, mode in ((a.lean, 'lean'), (a.rocq, 'rocq'), (a.core, 'core'), (a.rocq_cd, 'rocqcd')):
        if path:
            path.write_text(render(rows, goals, mode), encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()

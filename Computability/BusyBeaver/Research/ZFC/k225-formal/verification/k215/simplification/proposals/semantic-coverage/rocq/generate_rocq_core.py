#!/usr/bin/env python3
"""Untrusted Rocq backend for ProveIt's existing 58-step abstract derivation.

The parser, unifier, and explicit instantiation pass are copied unchanged from
ProveIt 2ca3a5c16f0876d2cab842056353c03a1ed2f5f0, rho8cd/.  This backend
adds no search result.  Every output proof term is checked by the Rocq kernel.
"""
from pathlib import Path
import argparse
import upstream_generate_domrho8_cd as cd


class RocqCore(cd.Syntax):
    def __init__(self):
        self.rocq = True
        self.core = True

    def le(self, u, a, hyps):
        if (u, a) in hyps:
            return 'hb%d' % hyps.index((u, a))
        if u == a:
            return '(below_refl _)'
        return super().le(u, a, hyps)

    def lemma(self, name, t, cons, major, minor):
        vs = cd.variables(t, [])
        for u, a in cons:
            cd.variables(u, vs)
            cd.variables(a, vs)
        binders = ' (%s : A)' % ' '.join('v%d' % v for v in sorted(vs)) if vs else ''
        hyps = ''.join(' (hb%d : below (%s) (%s))' % (k, self.term(u), self.term(a))
                       for k, (u, a) in enumerate(cons))
        assert not (major[4] or minor[4])
        return ('Local Lemma %s%s%s :\n  T (%s).\n'
                'Proof. exact (dmp h _ _ %s %s). Qed.\n') % (
                    name, binders, hyps, self.term(t), self.use(major, cons), self.use(minor, cons))


HEAD = '''(** Representation-independent dominated implication: Rocq backend for the
    existing ProveIt 58-step derivation_core.txt.  No truth constant, bottom,
    injectivity, decoder, transitivity, or arithmetic is assumed.  The proof
    terms, not the Python renderer, are trusted. *)

Module DominatedImplication58.
Section Core.
Context {A : Type}.
Variable wim : A -> A -> A.
Variable below : A -> A -> Prop.
Hypothesis below_refl : forall a, below a a.
Hypothesis grow_left : forall u x y, below u x -> below u (wim x y).
Hypothesis grow_right : forall u y x, below u y -> below u (wim x y).

Definition rho8 (a b c u : A) : A :=
  wim (wim (wim c u) a) (wim (wim a c) (wim b c)).

Record Restricted (T : A -> Prop) : Prop := {
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, below u a -> T (rho8 a b c u) }.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Local Definition le_l {u x : A} y (H : below u x) : below u (wim x y) :=
  grow_left u x y H.
Local Definition le_r {u y : A} x (H : below u y) : below u (wim x y) :=
  grow_right u y x H.

Variable T : A -> Prop.
Variable h : Restricted T.

'''

TAIL = '''Theorem rho8_all a b c u : T (rho8 a b c u).
Proof. exact ({row}). Qed.

Theorem composition a b c : T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact ({composition}). Qed.

Theorem prefix a b x : T (wim (wim a b) (wim (wim x a) (wim x b))).
Proof. exact ({prefix}). Qed.

Theorem lift_right a b : T (wim a b) -> forall x, T (wim (wim x a) (wim x b)).
Proof. intros H x. exact (dmp h _ _ (prefix a b x) H). Qed.

End Core.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions prefix.
Print Assumptions lift_right.
End DominatedImplication58.
'''


def render(path):
    rows, goals = cd.read(path)
    def no_truth(t):
        return all(no_truth(x) for x in t) if isinstance(t, tuple) else t != cd.Z
    assert all(j != -1 and no_truth(t) and all(no_truth(u) and no_truth(a) for u, a in cs)
               for j, _, t, cs in rows.values()), 'the generic core rejects truth'
    lemmas, names = cd.steps(rows, core=True)
    syn = RocqCore()
    use = {}
    for name, goal, vnames in [('row', cd.ROW, cd.ROW_NAMES),
                              ('composition', cd.COMPOSITION, ['a', 'b', 'c']),
                              ('prefix', cd.PREFIX, ['a', 'b', 'x'])]:
        i = next(i for i, g in goals if g == goal)
        assert not rows[i][3]
        use[name] = '%s %s' % (names[i], syn.instance(rows[i][2], goal, vnames))
    return HEAD + '\n'.join(syn.lemma(*s) for s in lemmas) + '\n' + TAIL.format(**use)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--derivation', type=Path, default=Path(__file__).with_name('derivation_core.txt'))
    ap.add_argument('--out', type=Path, default=Path(__file__).with_name('DominatedImplication58.v'))
    args = ap.parse_args()
    args.out.write_text(render(args.derivation), encoding='utf-8')

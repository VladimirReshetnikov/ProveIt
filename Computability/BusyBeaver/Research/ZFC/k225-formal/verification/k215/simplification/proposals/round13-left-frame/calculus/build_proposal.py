#!/usr/bin/env python3
"""Owned, deterministic text-only proposal construction; does not run repository code."""
from pathlib import Path
import difflib, hashlib, json, sys
if not __debug__:
    raise SystemExit('Run without -O: source assertions are part of this audit.')
ROOT = Path(__file__).resolve().parent
INP = ROOT / 'inputs'
OUT = ROOT / 'proposed'
OUT.mkdir(exist_ok=True)

def replace(s, a, b, repl):
    i, j = s.index(a), s.index(b, s.index(a))
    return s[:i] + repl + s[j:]

def decl_block(s, start, end):
    return s[s.index(start):s.index(end, s.index(start))]

D = (INP / 'TarskiDerived.lean').read_text()
L = (INP / 'TarskiLeibniz.lean').read_text()
K = (INP / 'KThmK.lean').read_text()

helpers = '''/-! ## Equality from a single explicit vacuity witness -/

section EqualityWitness

variable (hC : Classical NF.imp NF.bot T) [R : Rows T]
include hC

/-- No freshness or general equality-vacuity schema is assumed: this one theorem suffices. -/
theorem eq_refl_of_vac (c x : Nat)
    (hv : T (imp (NF.eq x x) (all c (NF.eq x x)))) : T (NF.eq x x) := by
  have h7 : T (imp (NF.eq c x) (NF.eq x x)) :=
    ded1 hC (.mp (.mp (.ax (R.rho7 x x c)) h0) h0)
  exact hC.mp (ex_elim_of_vac hC hv)
    (hC.mp (ex_mono hC c h7) (R.rho1 c x))

theorem eq_symm_of_refl (x y : Nat) (hr : T (NF.eq x x)) :
    T (imp (NF.eq x y) (NF.eq y x)) :=
  ded1 hC (.mp (.mp (.ax (R.rho7 y x x)) h0) (.ax hr))

theorem eq_trans_of_symm (x y z : Nat) (hs : T (imp (NF.eq x y) (NF.eq y x))) :
    T (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) :=
  ded2 hC (.mp (.mp (.ax (R.rho7 x z y)) (.mp (.ax hs) h1)) h0)

end EqualityWitness

'''
D = D.replace('section Fresh\n', helpers + 'section Fresh\n', 1)
D = replace(D, 'theorem eq_refl (x : Nat)', '\nend Fresh', '''theorem eq_refl (x : Nat) : Thm Ax (NF.eq x x) :=
  eq_refl_of_vac hC (x + 1) x (.vacEq x x (x + 1) (by omega) (by omega))

theorem eq_symm (x y : Nat) : Thm Ax (imp (NF.eq x y) (NF.eq y x)) :=
  eq_symm_of_refl hC x y (eq_refl hC x)

theorem eq_trans (x y z : Nat) : Thm Ax (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) :=
  eq_trans_of_symm hC x y z (eq_symm hC x y)
''')
K = replace(K, 'theorem eq_refl (x : Nat)', '/-! ## Leibniz', '''theorem eq_refl (x : Nat) : ThmK Ax (NF.eq x x) :=
  eq_refl_of_vac classical (Code254.wel x x) x (.helper x x)

theorem eq_symm (x y : Nat) : ThmK Ax (imp (NF.eq x y) (NF.eq y x)) :=
  eq_symm_of_refl classical x y (eq_refl x)

theorem eq_trans (x y z : Nat) : ThmK Ax (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) :=
  eq_trans_of_symm classical x y z (eq_symm x y)

''')

core = '''/-- Congruence in equality's second operand requires only transitivity. -/
theorem eq_R_of_trans
    (ht : ∀ x y z, T (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))))
    (u v i : Nat) : T (imp (NF.eq u v) (imp (NF.eq i u) (NF.eq i v))) :=
  ded2 hC (.mp (.mp (.ax (ht i u v)) h0) h1)

/-- The quantified branch requests equality vacuity only at binders actually in `f`.
For a quantifier-free `f` the last premise is vacuous, even if `f` has equality atoms. -/
theorem leibniz_core [R : Rows T]
    (hs : ∀ x y, T (imp (NF.eq x y) (NF.eq y x)))
    (ht : ∀ x y z, T (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))))
    (x y : Nat) :
    ∀ f : NF, ¬ Bound x f → ¬ Bound y f →
      (∀ i, Bound i f → T (imp (NF.eq x y) (all i (NF.eq x y)))) →
      T (imp (NF.eq x y) (imp f (rn x y f))) ∧
      T (imp (NF.eq x y) (imp (rn x y f) f))
  | rel i j, _, _, _ =>
      ⟨atom_subst hC rel rel_L rel_R x y i j,
       atom_subst_rev hC hs rel rel_L rel_R x y i j⟩
  | NF.eq i j, _, _, _ =>
      ⟨atom_subst hC NF.eq eq_L (eq_R_of_trans hC ht) x y i j,
       atom_subst_rev hC hs NF.eq eq_L (eq_R_of_trans hC ht) x y i j⟩
  | NF.bot, _, _, _ => ⟨ded2 hC h0, ded2 hC h0⟩
  | imp a b, hx, hy, hv => by
      have ha := leibniz_core hs ht x y a (fun h => hx (Or.inl h))
        (fun h => hy (Or.inl h)) (fun i h => hv i (Or.inl h))
      have hb := leibniz_core hs ht x y b (fun h => hx (Or.inr h))
        (fun h => hy (Or.inr h)) (fun i h => hv i (Or.inr h))
      constructor
      · apply ded3 hC
        have a0 : Der NF.imp T [rn x y a, imp a b, NF.eq x y] a :=
          .mp (.mp (.ax ha.2) h2) h0
        exact .mp (.mp (.ax hb.1) h2) (.mp h1 a0)
      · apply ded3 hC
        have a0 : Der NF.imp T [a, imp (rn x y a) (rn x y b), NF.eq x y] (rn x y a) :=
          .mp (.mp (.ax ha.1) h2) h0
        exact .mp (.mp (.ax hb.2) h2) (.mp h1 a0)
  | all i a, hx, hy, hv => by
      have hix : i ≠ x := fun e => hx (Or.inl e.symm)
      have ha := leibniz_core hs ht x y a (fun h => hx (Or.inr h))
        (fun h => hy (Or.inr h)) (fun j h => hv j (Or.inr h))
      simp only [rn, hix, if_false]
      have lift : ∀ {p q : NF}, T (imp (NF.eq x y) (imp p q)) →
          T (imp (NF.eq x y) (imp (all i p) (all i q))) := by
        intro p q h
        have g := all_mono hC i h
        apply ded2 hC
        exact .mp (.mp (.ax (R.rho2 i p q))
          (.mp (.ax g) (.mp (.ax (hv i (Or.inl rfl))) h1))) h0
      exact ⟨lift ha.1, lift ha.2⟩

/-- Specialization needs only the forward rewriting theorem and elimination for its result.
Freshness and fragment checks belong to the callers that construct these two inputs. -/
theorem specialize_core [R : Rows T] (x y : Nat) (f g : NF)
    (hL : T (imp (NF.eq x y) (imp f g)))
    (he : T (imp (ex x g) g)) : T (imp (all x f) g) := by
  have shuffle : T (imp f (imp (NF.eq x y) g)) :=
    ded2 hC (.mp (.mp (.ax hL) h0) h1)
  have hg := all_mono hC x shuffle
  have hm := all_imp_ex hC x (NF.eq x y) g
  exact ded1 hC (.mp (.ax he) (.mp (.mp (.ax hm) (.mp (.ax hg) h0)) (.ax (R.rho1 x y))))

'''
L = L.replace('end Atoms\n', core + 'end Atoms\n', 1)
L = replace(L, 'theorem eq_R (u v i : Nat)', '/-! ## Specialization', '''theorem eq_R (u v i : Nat) : Thm Ax (imp (NF.eq u v) (imp (NF.eq i u) (NF.eq i v))) :=
  eq_R_of_trans hC (eq_trans hC) u v i

/-- Leibniz's law for formulas without rebinding of either label. -/
theorem leibniz (x y : Nat) :
    ∀ f : NF, ¬ Bound x f → ¬ Bound y f →
      Thm Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
      Thm Ax (imp (NF.eq x y) (imp (rn x y f) f)) :=
  fun f hx hy => leibniz_core hC (eq_symm hC) (eq_trans hC) x y f hx hy
    (fun i hi => .vacEq x y i (fun e => hx (e ▸ hi)) (fun e => hy (e ▸ hi)))

''')
L = replace(L, 'theorem spec {x y : Nat}', '/-- The T axiom', '''theorem spec {x y : Nat} (hxy : y ≠ x) {f : NF} (hx : ¬ Bound x f) (hy : ¬ Bound y f) :
    Thm Ax (imp (all x f) (rn x y f)) :=
  specialize_core hC x y f (rn x y f) (leibniz hC x y f hx hy).1
    (ex_elim hC x (not_occurs_rn hxy f hx))

''')
# Move existing quantifier-free Bound exclusion before its new use in Leibniz.
qfb = decl_block(K, 'theorem qf_bound', '/-- Specialization')
K = K.replace(qfb, '', 1)
K = replace(K, '/-- Leibniz\'s law for quantifier-free', '/-- Specialization', qfb + '''/-- Leibniz's law for quantifier-free, equality-free formulas.
The compatibility wrapper keeps both original guards; the core needs no binder vacuity. -/
theorem leibniz (x y : Nat) :
    ∀ f : NF, QF f → EqFree f →
      ThmK Ax (imp (NF.eq x y) (imp f (rn x y f))) ∧
      ThmK Ax (imp (NF.eq x y) (imp (rn x y f) f)) :=
  fun f hq _ => leibniz_core classical eq_symm eq_trans x y f (qf_bound hq) (qf_bound hq)
    (fun _ hi => (qf_bound hq hi).elim)

''')
K = replace(K, 'theorem spec {x y : Nat}', '/-- Alpha-renaming', '''theorem spec {x y : Nat} (hxy : y ≠ x) {f : NF} (hq : QF f) (hf : EqFree f) :
    ThmK Ax (imp (all x f) (rn x y f)) :=
  specialize_core classical x y f (rn x y f) (leibniz x y f hq hf).1
    (ex_elim x (eqFree_rn x y f hf) (not_occurs_rn hxy f (qf_bound hq)))

''')

# Keep the short symmetry/transitivity bodies rather than add adapters whose overhead
# exceeds their savings. The new shared equality resource is the diagonal-vacuity proof.
D = replace(D, 'theorem eq_symm_of_refl', 'end EqualityWitness', '')
D = replace(D, 'theorem eq_symm (x y : Nat)', '\nend Fresh',
    decl_block((INP/'TarskiDerived.lean').read_text(), 'theorem eq_symm (x y : Nat)', '\nend Fresh'))
K = replace(K, 'theorem eq_symm (x y : Nat)', '/-! ## Leibniz',
    decl_block((INP/'KThmK.lean').read_text(), 'theorem eq_symm (x y : Nat)', '/-! ## Leibniz'))
# A single already-shared propositional branch, in direct natural-deduction form.
a = L.index('      constructor', L.index('theorem leibniz_core'))
b = L.index('  | all i a, hx, hy, hv => by', a)
L = L[:a] + """      exact ⟨ded3 hC (.mp (.mp (.ax hb.1) h2)
        (.mp h1 (.mp (.mp (.ax ha.2) h2) h0))),
        ded3 hC (.mp (.mp (.ax hb.2) h2)
        (.mp h1 (.mp (.mp (.ax ha.1) h2) h0)))⟩
""" + L[b:]

files = {'TarskiDerived.lean': D, 'TarskiLeibniz.lean': L, 'KThmK.lean': K}
patch = []
summary = {'pin': '6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95',
 'status': 'UNCOMPILED_SOURCE_PROPOSAL', 'files': {}}
for name, candidate in files.items():
    before = (INP/name).read_text()
    (OUT/name).write_text(candidate)
    patch.extend(difflib.unified_diff(before.splitlines(True), candidate.splitlines(True),
        fromfile='a/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+name,
        tofile='b/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+name))
    summary['files'][name] = {
      'before_sha256': hashlib.sha256(before.encode()).hexdigest(),
      'after_sha256': hashlib.sha256(candidate.encode()).hexdigest(),
      'before_bytes':len(before.encode()), 'after_bytes':len(candidate.encode()),
      'before_lines':len(before.splitlines()), 'after_lines':len(candidate.splitlines())}
(ROOT/'local_equality_capabilities.patch').write_text(''.join(patch))
summary['totals'] = {k:sum(f[k] for f in summary['files'].values()) for k in
                    ('before_bytes','after_bytes','before_lines','after_lines')}
(ROOT/'PROPOSAL_METRICS.json').write_text(json.dumps(summary, indent=2)+'\n')
print(json.dumps(summary, indent=2))

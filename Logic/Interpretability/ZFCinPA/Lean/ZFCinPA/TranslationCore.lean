import ZF.Zf
import Foundation.FirstOrder.SetTheory.Basic.Axioms

set_option autoImplicit false

/-! Shared syntax translation and satisfaction preservation. -/
namespace LeanProofs.ZFCinPA
open LO LO.FirstOrder LO.FirstOrder.SetTheory

/-- The membership relation of a Foundation set structure, in the binary-
relation form the repository's semantic layer (`SetTheory.Sat`, `ZFAxioms`)
consumes. -/
abbrev memRel (V : Type*) [SetStructure V] : V → V → Prop := (· ∈ ·)

/-! ## The syntax translation

The repository's `Form` uses one flat De Bruijn index space: under `k`
binders, index `i < k` points at the `i`-th enclosing binder and `i ≥ k` is
free.  Foundation separates bound variables `#i : Fin k` from free variables
`&j : ℕ`, with the same "new binder is `#0`" orientation, so the translation
is index splitting and nothing else. -/

/-- The translation of a repository De Bruijn variable at binder depth `k`. -/
def toSetVar (k i : Nat) : Semiterm ℒₛₑₜ ℕ k :=
  if h : i < k then #(⟨i, h⟩ : Fin k) else &(i - k)

/-- **The syntax translation** at binder depth `k`.  Atoms go to the `mem` and
`eq` relation symbols of `ℒₛₑₜ`, the propositional connectives to Foundation's
(implication is Foundation's defined `🡒`), and the quantifiers to `∀⁰`/`∃⁰`
with the depth incremented. -/
def toSet : (k : Nat) → SetTheory.Form → SetTheorySemiproposition k
  | k, .fMem i j => .rel Language.Mem.mem ![toSetVar k i, toSetVar k j]
  | k, .fEq i j  => .rel Language.Eq.eq ![toSetVar k i, toSetVar k j]
  | _, .fBot     => ⊥
  | k, .fImp a b => toSet k a 🡒 toSet k b
  | k, .fAnd a b => toSet k a ⋏ toSet k b
  | k, .fOr a b  => toSet k a ⋎ toSet k b
  | k, .fAll a   => ∀⁰ toSet (k + 1) a
  | k, .fEx a    => ∃⁰ toSet (k + 1) a

/-! ## Satisfaction preservation

The environment-correspondence invariant: a repository environment
`e : ℕ → V` matches a Foundation valuation pair `(b, f)` at depth `k` when
`b i = e i` on the `k` bound slots and `f j = e (k + j)` on the free ones.
The correspondence is preserved on both sides of a binder: prepending `d` to
`b` matches `scons d e` at depth `k + 1` with the same `f`. -/

/-- A translated variable evaluates to the corresponding repository
environment entry. -/
theorem val_toSetVar {V : Type*} [SetStructure V] {k : Nat} {b : Fin k → V}
    {f e : ℕ → V} (hb : ∀ i : Fin k, b i = e i.val)
    (hf : ∀ j, f j = e (k + j)) (i : ℕ) :
    (toSetVar k i).val b f = e i := by
  unfold toSetVar
  by_cases h : i < k
  · rw [dif_pos h]
    exact hb ⟨i, h⟩
  · rw [dif_neg h]
    have h2 : k + (i - k) = i := by omega
    rw [Semiterm.val_fvar, hf (i - k), h2]

/-- **Satisfaction preservation.**  Over any Foundation set structure the
Tarski evaluation of the translation agrees with the repository's `Sat`,
whenever the valuations correspond.  One structural induction; the two binder
cases extend the correspondence through `scons`. -/
theorem eval_toSet {V : Type*} [SetStructure V] (φ : SetTheory.Form) :
    ∀ (k : Nat) (b : Fin k → V) (f e : ℕ → V),
      (∀ i : Fin k, b i = e i.val) → (∀ j, f j = e (k + j)) →
      ((toSet k φ).Eval b f ↔ SetTheory.Sat (memRel V) e φ) := by
  induction φ with
  | fMem i j | fEq i j =>
      intro k b f e hb hf
      simp [toSet, SetTheory.Sat, val_toSetVar hb hf]
  | fBot =>
      intro k b f e hb hf
      simp [toSet, SetTheory.Sat]
  | fImp a b iha ihb | fAnd a b iha ihb | fOr a b iha ihb =>
      intro k bb f e hb hf
      simp [toSet, SetTheory.Sat, iha k bb f e hb hf, ihb k bb f e hb hf]
  | fAll a ih | fEx a ih =>
      intro k bb f e hb hf
      simp only [toSet, Semiformula.eval_all, Semiformula.eval_ex, SetTheory.Sat]
      first
      | refine forall_congr' fun d => ih (k + 1) (d :> bb) f (SetTheory.scons d e) ?_ ?_
      | refine exists_congr fun d => ih (k + 1) (d :> bb) f (SetTheory.scons d e) ?_ ?_
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp [SetTheory.scons]
        · simpa [SetTheory.scons] using hb i'
      · intro j
        have h2 : k + 1 + j = (k + j) + 1 := by omega
        rw [h2]
        simpa [SetTheory.scons] using hf j


end LeanProofs.ZFCinPA

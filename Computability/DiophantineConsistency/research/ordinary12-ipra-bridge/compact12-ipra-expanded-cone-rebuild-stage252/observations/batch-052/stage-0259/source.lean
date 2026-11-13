import Foundation.FirstOrder.SetTheory.Basic.Axioms
import ZFCinPA.TranslationCore

set_option autoImplicit false

/-!
Ordinary semantic ZF extraction through the replacement schema.
The syntax translation and totalized Replacement argument are adapted from
ZFCinPA/Translation.lean, using only ZF axioms directly. No arbitrary internal formula is quoted or interpreted.
-/
namespace LeanProofs.ZFCinPA.NativeZFContainers254
open LO LO.FirstOrder LO.FirstOrder.SetTheory

abbrev memRel (V : Type*) [SetStructure V] : V → V → Prop := (· ∈ ·)

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
    (toSetVar k i).val b f = e i :=
  LeanProofs.ZFCinPA.val_toSetVar hb hf i

private theorem toSet_eq_shared (k : Nat) (φ : SetTheory.Form) :
    toSet k φ = LeanProofs.ZFCinPA.toSet k φ := by
  induction φ generalizing k <;>
    simp [toSet, LeanProofs.ZFCinPA.toSet, toSetVar, LeanProofs.ZFCinPA.toSetVar, *]

/-- **Satisfaction preservation.**  Over any Foundation set structure the
Tarski evaluation of the translation agrees with the repository's `Sat`,
whenever the valuations correspond.  One structural induction; the two binder
cases extend the correspondence through `scons`. -/
theorem eval_toSet {V : Type*} [SetStructure V] (φ : SetTheory.Form) :
    ∀ (k : Nat) (b : Fin k → V) (f e : ℕ → V),
      (∀ i : Fin k, b i = e i.val) → (∀ j, f j = e (k + j)) →
      ((toSet k φ).Eval b f ↔ SetTheory.Sat (memRel V) e φ) := by
  intro k b f e hb hf
  rw [toSet_eq_shared]
  exact LeanProofs.ZFCinPA.eval_toSet φ k b f e hb hf

/-! ### Valuation correspondences at the depths the extraction uses -/

private theorem env1_eq {V : Type*} (x : V) (e : ℕ → V) :
    ∀ i : Fin 1, ![x] i = SetTheory.scons x e i.val := fun i =>
  Fin.cases rfl (fun j => j.elim0) i

private theorem env1_shift {V : Type*} (x : V) (e : ℕ → V) (j : ℕ) :
    e j = SetTheory.scons x e (1 + j) := by
  rw [Nat.add_comm]
  rfl

private theorem env2_eq {V : Type*} (x y : V) (e : ℕ → V) :
    ∀ i : Fin 2, ![x, y] i = SetTheory.scons x (SetTheory.scons y e) i.val := fun i =>
  Fin.cases rfl (fun j => Fin.cases rfl (fun j' => j'.elim0) j) i

private theorem env2_shift {V : Type*} (x y : V) (e : ℕ → V) (j : ℕ) :
    e j = SetTheory.scons x (SetTheory.scons y e) (2 + j) := by
  rw [Nat.add_comm]
  rfl

section Extraction
variable {V : Type*} [SetStructure V] [Nonempty V]

/-- Ordinary Separation at an external formula, using the actual ZF axiom. -/
theorem sep_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (phi : SetTheory.Form) (e : ℕ → V) (a : V) :
    ∃ s : V, ∀ x, x ∈ s ↔ (x ∈ a ∧ SetTheory.Sat (memRel V) (SetTheory.scons x e) phi) := by
  have hh : ∀ f : ℕ → V, ∀ X : V, ∃ Y : V, ∀ z : V,
      z ∈ Y ↔ z ∈ X ∧ (toSet 1 phi).Eval ![z] f := by
    simpa [models_iff,Axiom.separationSchema,Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using
      Theory.models V 𝗭𝗙 (ZermeloFraenkel.axiom_of_separation (toSet 1 phi))
  obtain ⟨s,hs⟩ := hh e a
  refine ⟨s,fun x => (hs x).trans (and_congr_right fun _ => ?_)⟩
  exact eval_toSet phi 1 ![x] e (SetTheory.scons x e)
    (env1_eq x e) (fun j => env1_shift x e j)

def swapR : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

/-- Renaming that reads the graph under one extra binder: the new slot `0` is
the value, slot `1` remains the argument, parameters move past one binder. -/
def liftR : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => n + 3

/-- Renaming used by the image carving: the value comes from slot `1`, the
argument from the new slot `0`, parameters move past one extra binder. -/
def carveR : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 3

/-- The totalized graph of `psi`, in Foundation's argument order (slot `0` the
argument `x`, slot `1` the value `y`): either `psi` relates `y` to `x`, or `x`
has no `psi`-value at all and `y = x`. -/
def totalGraphF (psi : SetTheory.Form) : SetTheory.Form :=
  .fOr (SetTheory.rename swapR psi)
    (.fAnd (.fImp (.fEx (SetTheory.rename liftR psi)) .fBot) (.fEq 1 0))

/-- The image predicate for the carving step (slot `0` the image member `y`,
slot `1` the source set `a`, parameters shifted by two): "some `x ∈ a` has
`psi`-value `y`". -/
def carveF (psi : SetTheory.Form) : SetTheory.Form :=
  .fEx (.fAnd (.fMem 0 2) (SetTheory.rename carveR psi))

/-- Satisfaction of the totalized graph, computed. -/
theorem sat_totalGraphF {V : Type*} [SetStructure V] (psi : SetTheory.Form)
    (e : ℕ → V) (xv yv : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons xv (SetTheory.scons yv e)) (totalGraphF psi) ↔
      (SetTheory.relOf (memRel V) psi e yv xv ∨
        ((¬ ∃ z, SetTheory.relOf (memRel V) psi e z xv) ∧ yv = xv)) := by
  unfold totalGraphF
  simp only [SetTheory.Sat]
  refine or_congr ?_ (and_congr ?_ Iff.rfl)
  · exact SetTheory.Sat_rename_ext psi swapR _ _ (fun n => match n with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl)
  · refine not_congr (exists_congr fun z => ?_)
    exact SetTheory.Sat_rename_ext psi liftR _ _ (fun n => match n with
      | 0 => rfl
      | 1 => rfl
      | _ + 2 => rfl)

/-- Satisfaction of the carving predicate, computed. -/
theorem sat_carveF {V : Type*} [SetStructure V] (psi : SetTheory.Form)
    (e : ℕ → V) (a y : V) :
    SetTheory.Sat (memRel V) (SetTheory.scons y (SetTheory.scons a e)) (carveF psi) ↔
      ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) psi e y x := by
  unfold carveF
  simp only [SetTheory.Sat]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  exact SetTheory.Sat_rename_ext psi carveR _ _ (fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl)

/-- The repository's Replacement clause, from Foundation's replacement schema
at the totalized graph, followed by Separation. -/
theorem repl_clause [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (psi : SetTheory.Form) (e : ℕ → V)
    (hfun : SetTheory.Functional (SetTheory.relOf (memRel V) psi e)) (a : V) :
    ∃ r : V, ∀ y, y ∈ r ↔ ∃ x, x ∈ a ∧ SetTheory.relOf (memRel V) psi e y x := by
  -- The totalized graph, read through satisfaction preservation.
  have hTG : ∀ xv yv : V,
      ((toSet 2 (totalGraphF psi)).Eval ![xv, yv] e ↔
        (SetTheory.relOf (memRel V) psi e yv xv ∨
          ((¬ ∃ z, SetTheory.relOf (memRel V) psi e z xv) ∧ yv = xv))) := fun xv yv =>
    (eval_toSet (totalGraphF psi) 2 ![xv, yv] e
        (SetTheory.scons xv (SetTheory.scons yv e))
        (env2_eq xv yv e) (fun j => env2_shift xv yv e j)).trans
      (sat_totalGraphF psi e xv yv)
  -- Totalized functionality: exactly what Foundation's schema demands.
  have htot : ∀ x : V, ∃! y, (toSet 2 (totalGraphF psi)).Eval ![x, y] e := by
    intro x
    by_cases hx : ∃ z, SetTheory.relOf (memRel V) psi e z x
    · obtain ⟨z, hz⟩ := hx
      exact ⟨z, (hTG x z).mpr (Or.inl hz), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => hfun x y z h hz)
          (fun h => absurd ⟨z, hz⟩ h.1)⟩
    · exact ⟨x, (hTG x x).mpr (Or.inr ⟨hx, rfl⟩), fun y hy =>
        ((hTG x y).mp hy).elim (fun h => absurd ⟨y, h⟩ hx) (fun h => h.2)⟩
  -- Foundation's replacement schema at the totalized graph.
  have hrepl :
      ∀ f : ℕ → V,
        (∀ x : V, ∃! y : V, (toSet 2 (totalGraphF psi)).Eval ![x, y] f) →
        ∀ X : V, ∃ Y : V, ∀ y : V,
          y ∈ Y ↔ ∃ x ∈ X, (toSet 2 (totalGraphF psi)).Eval ![x, y] f := by
    simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons'] using
      Theory.models V 𝗭𝗙
        (ZermeloFraenkel.axiom_of_replacement (toSet 2 (totalGraphF psi)))
  obtain ⟨Y, hY⟩ := hrepl e htot a
  -- Carve the exact image out of the totalized one.
  obtain ⟨r, hr⟩ := sep_clause (carveF psi) (SetTheory.scons a e) Y
  refine ⟨r, fun y => ?_⟩
  rw [hr y, sat_carveF psi e a y]
  constructor
  · rintro ⟨-, hx⟩
    exact hx
  · rintro ⟨x, hxa, hRyx⟩
    exact ⟨(hY y).mpr ⟨x, hxa, (hTG x y).mpr (Or.inl hRyx)⟩, x, hxa, hRyx⟩

end Extraction

end LeanProofs.ZFCinPA.NativeZFContainers254

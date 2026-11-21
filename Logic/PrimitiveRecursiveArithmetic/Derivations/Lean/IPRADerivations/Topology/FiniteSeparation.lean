import IPRADerivations.Topology.FiniteInteriorClosure

/-!
# Separation collapses, compact–Hausdorff bijections and cover extraction in finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, in the framework of
`Topology/FiniteInteriorClosure` (subsets are families of iPRA formulas, open = upward, closed = downward):

* F15 (`thm:finite-tone`, "the following are equivalent: `T₁`; Hausdorff; discrete; and `x ≼ y` implies
  `x = y`"):
  - `t1_collapse`: if every singleton is closed, a comparability `x ≼ y` with `x ≠ y` derives `⊥` ("each
    singleton `{y}` is closed, so `↓y = {y}` … This eliminates every nonidentity order pair");
  - `discrete_clopen`: if `x ≼ y` implies `x = y`, every subset is open and closed ("the identity relation makes
    every subset upward closed and gives the discrete topology");
  - `hausdorff_collapse`: open `U ∋ x`, `V ∋ y` that are disjoint at `y`, with `x ≼ y`, derive `⊥` ("every
    neighborhood of `x` contains `y` and hence meets every neighborhood of `y`");
* F17 (`thm:finite-ch`): a monotone injection into a discrete preorder has a discrete source
  (`ch_source_discrete`, "the source is also discrete"), and every map out of a discrete preorder is monotone,
  in particular the inverse (`mono_of_discrete`);
* F16 (`thm:finite-cover`) for coded (decidable) subsets: `extract` scans the points of `S` in order and keeps
  the least covering index; the result has at most `|S|` entries (`extract_length`) and still covers `S`
  (`extract_covers`).
-/

namespace LeanProofs.IPRA.Topology.FiniteSeparation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open Syn
open scoped Fm

variable {n k l r : ℕ} {Γ : List (Fm PTm n)} {rel : Fin k → Fin k → Prop}

/-! ## F15 -/

/-- The singleton `{y}`. -/
def sing (y : Fin k) (z : Fin k) : Fm PTm n := if z = y then truth else Fm.bot

/-- `T₁` excludes nonidentity comparabilities (up to inconsistency). -/
theorem t1_collapse (hT1 : ∀ y, IsClosed rel Γ (sing y)) {x y : Fin k} (hxy : rel x y) (hne : x ≠ y) :
    Γ ⊢[PRAAx] Fm.bot := by
  have h := hT1 y x y hxy
  unfold sing at h
  rw [if_pos rfl, if_neg hne] at h
  exact .impE h (.eqRefl _)

/-- In a discrete preorder every subset is open and closed. -/
theorem discrete_clopen (hdisc : ∀ x y, rel x y → x = y) (U : Fin k → Fm PTm n) :
    IsOpen rel Γ U ∧ IsClosed rel Γ U :=
  ⟨fun x y h => by obtain rfl := hdisc x y h; exact .impI Prf.hyp0,
   fun x y h => by obtain rfl := hdisc x y h; exact .impI Prf.hyp0⟩

/-- Hausdorff separation excludes comparabilities (up to inconsistency). -/
theorem hausdorff_collapse {U V : Fin k → Fm PTm n} (hU : IsOpen rel Γ U) {x y : Fin k}
    (hUx : Γ ⊢[PRAAx] U x) (hVy : Γ ⊢[PRAAx] V y) (hdisj : Γ ⊢[PRAAx] U y ⟶ (V y ⟶ Fm.bot))
    (hxy : rel x y) : Γ ⊢[PRAAx] Fm.bot :=
  .impE (.impE hdisj (.impE (hU x y hxy) hUx)) hVy

/-- Distinct points of a discrete preorder are separated by their singletons. -/
theorem sing_separates {x y : Fin k} (hne : x ≠ y) :
    (Γ ⊢[PRAAx] sing x x) ∧ (Γ ⊢[PRAAx] sing y y) ∧ (∀ z, Γ ⊢[PRAAx] sing x z ⟶ (sing y z ⟶ Fm.bot)) := by
  refine ⟨by unfold sing; rw [if_pos rfl]; exact .eqRefl _, by unfold sing; rw [if_pos rfl]; exact .eqRefl _,
    fun z => ?_⟩
  unfold sing
  by_cases hx : z = x
  · subst hx
    rw [if_pos rfl, if_neg hne]
    exact .impI (.impI Prf.hyp0)
  · rw [if_neg hx]
    exact .impI (.botE _ Prf.hyp0)

/-! ## F17 -/

/-- A monotone injection into a discrete preorder has a discrete source. -/
theorem ch_source_discrete {rel' : Fin l → Fin l → Prop} (hdisc' : ∀ a b, rel' a b → a = b) {f : Fin k → Fin l}
    (hf : ∀ x y, rel x y → rel' (f x) (f y)) (hinj : Function.Injective f) : ∀ x y, rel x y → x = y :=
  fun x y h => hinj (hdisc' _ _ (hf x y h))

/-- Every map out of a discrete preorder into a reflexive one is monotone (so the inverse table is continuous). -/
theorem mono_of_discrete {rel' : Fin l → Fin l → Prop} (hdisc' : ∀ a b, rel' a b → a = b) (hrefl : ∀ x, rel x x)
    (g : Fin l → Fin k) : ∀ a b, rel' a b → rel (g a) (g b) :=
  fun a b h => by obtain rfl := hdisc' a b h; exact hrefl _

/-! ## F16 -/

/-- Keep, for every point of `S` in increasing order, the least index of a covering set. -/
def extract (S : Fin k → Prop) [DecidablePred S] (U : Fin r → Fin k → Prop) [∀ i, DecidablePred (U i)] :
    List (Fin r) :=
  ((List.finRange k).filter fun x => decide (S x)).filterMap fun x =>
    (List.finRange r).find? fun i => decide (U i x)

theorem extract_length (S : Fin k → Prop) [DecidablePred S] (U : Fin r → Fin k → Prop)
    [∀ i, DecidablePred (U i)] :
    (extract S U).length ≤ ((List.finRange k).filter fun x => decide (S x)).length :=
  List.length_filterMap_le _ _

theorem extract_covers (S : Fin k → Prop) [DecidablePred S] (U : Fin r → Fin k → Prop)
    [∀ i, DecidablePred (U i)] (hcov : ∀ x, S x → ∃ i, U i x) :
    ∀ x, S x → ∃ i ∈ extract S U, U i x := by
  intro x hx
  cases h : (List.finRange r).find? (fun i => decide (U i x)) with
  | none =>
    obtain ⟨i, hi⟩ := hcov x hx
    have := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp [hi] at this
  | some i =>
    refine ⟨i, ?_, by simpa using List.find?_some h⟩
    unfold extract
    rw [List.mem_filterMap]
    exact ⟨x, List.mem_filter.mpr ⟨List.mem_finRange x, by simpa using hx⟩, h⟩

end LeanProofs.IPRA.Topology.FiniteSeparation

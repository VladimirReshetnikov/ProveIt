/-
  PUBLISHED RESULTS, ADMITTED WITHOUT PROOF.

  Every statement in this file is a result from the literature (or a textbook
  fact), stated in the framework of `Cardinals.Foundations` and closed by `admit`.
  Nothing else in the development is admitted.  Each entry records its source.

  Sources
  * [Kun]  K. Kunen, Elementary embeddings and infinitary combinatorics, JSL 1971.
  * [Jech] T. Jech, Set Theory (3rd millennium ed.).
  * [G24]  G. Goldberg, The uniqueness of elementary embeddings, JSL 89 (2024).
  * [BG]   G. Goldberg (joint with D. Blue), Consistency beyond the Kunen
           inconsistency, lecture notes, 1 July 2026.
  * [ABL]  Aguilera–Bagaria–Lücke, Large cardinals, structural reflection, and the
           HOD Conjecture, arXiv:2411.11568.
-/
import Cardinals.Foundations.Exacting

universe u

namespace Cardinals.Published

open ZFSet Ordinal Cardinal Cardinals

/-! ### Exacting cardinals: the critical sequence ([Kun], [ABL §2], [BG]) -/

/-- An exacting cardinal has cofinality `ω`: the critical sequence of a witness is
cofinal, by the local Kunen inconsistency.  (Synthesis Lemma 3.1; [ABL, §2].) -/
theorem cof_omega_of_witness (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : ∀ α > c.ord, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness c.ord α Y)) :
    ∃ s : ℕ → Ordinal.{u}, StrictMono s ∧ (∀ n, s n < c.ord) ∧ ∀ ξ < c.ord, ∃ n, ξ ≤ s n := by
  admit

/-- An exacting cardinal is a strong limit.  ([ABL, §2].) -/
theorem strongLimit_of_witness (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : ∀ α > c.ord, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness c.ord α Y)) :
    ∀ μ < c, (2 : Cardinal.{u}) ^ μ < c := by
  admit

/-- No cardinal is exacting relative to a short cofinal subset of itself.
(Synthesis Lemma 3.2; [BG, Observation 1], the mechanism of [ABL, Thm 2.10].) -/
theorem not_REx_shortCofinal (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (a : ZFSet.{u})
    (ha : ShortCofinal a c.ord) : ¬ REx c.ord a := by
  admit

/-- Definability transfer: relative exactingness passes from `Y` to every set
ordinal definable from `Y`.  ([BG, Lemma 3.3]; synthesis Lemma 3.4.) -/
theorem REx_transfer (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (Y Z : ZFSet.{u})
    (hY : REx c.ord Y) (hZ : ODfrom (fun p => p = Y) Z) : REx c.ord Z := by
  admit

/-- The cover bound cannot be smaller than the cardinal.  ([BG]; synthesis Lemma 3.5.) -/
theorem le_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) : c ≤ γ := by
  admit

/-- Stationary characterization of cover exactingness, forward direction:
the relatively exacting predicates of size at most `γ` are stationary in
`P_{γ⁺}(V_ α)` for all large `α`.  ([BG, Proposition 3.4, (1) ⇒ (3)].) -/
theorem stationary_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) :
    ∃ α₀, ∀ α ≥ α₀, IsStationaryPkA (Order.succ γ) (V_ α) {σ | REx c.ord σ} := by
  admit

/-! ### Textbook facts ([Jech]) -/

/-- Elementary substructures of `(V_ α, ∈)` of size below a regular uncountable `κ`
that contain a given finite set form a club in `P_κ(V_ α)`.
(Löwenheim–Skolem and the elementary chain theorem; [Jech, Ch. 8, 12].) -/
theorem isClub_elemSub (κ : Cardinal.{u}) (hκ : κ.IsRegular) (hκ' : ℵ₀ < κ)
    (α : Ordinal.{u}) (F : List ZFSet.{u}) (hF : ∀ x ∈ F, x ∈ V_ α) :
    IsClubPkA κ (V_ α)
      {σ | σ ∈ PkA κ (V_ α) ∧ ElemSub σ (V_ α) ∧ ∀ x ∈ F, x ∈ σ} := by
  admit

/-- Ordinal definability composes: if `x` is ordinal definable from parameters each
of which is ordinal definable from `Q`-parameters, then `x` is ordinal definable
from `Q`-parameters.  (Uses the reflection theorem; [Jech, Ch. 13].) -/
theorem ODfrom_trans (P Q : ZFSet.{u} → Prop) (x : ZFSet.{u}) (hx : ODfrom P x)
    (hPQ : ∀ p, P p → ODfrom Q p) : ODfrom Q x := by
  admit

/-- Every extendible cardinal is strongly compact (indeed supercompact).
([Jech, Ch. 20].) -/
theorem SC_of_extendible (δ : Cardinal.{u}) (h : Extendible δ.ord) : SC δ := by
  admit

/-! ### Goldberg's theorems on `HCD` ([G24, §4]) -/

/-- `HCD(η)` is an inner model of ZF.  ([G24, Proposition 4.3].) -/
theorem HCD_isInnerModelZF (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : IsInnerModelZF (HCD η) := by
  admit

/-- If `δ` is strongly compact, `HCD(δ)` satisfies ZFC.  ([G24, Theorem 4.4].) -/
theorem HCD_isInnerModelZFC (δ : Cardinal.{u}) (hδ : SC δ) : IsInnerModelZFC (HCD δ) := by
  admit

/-- If `δ` is strongly compact, `HCD(δ)` has the `δ`-cover property; we record the
instance for sets of ordinals.  ([G24, Theorem 4.14].) -/
theorem HCD_cover (δ : Cardinal.{u}) (hδ : SC δ) (lam : Ordinal.{u}) (a : ZFSet.{u})
    (ha : SubOrd a lam) (hcard : ZFSet.card a < δ) :
    ∃ b : ZFSet.{u}, HCD δ b ∧ a ⊆ b ∧ ZFSet.card b < δ := by
  admit

/-- If `δ` is extendible, the `HCD` hierarchy stabilizes at `δ`:
`HCD(δ) = HCD = ⋂ HCD(η)`.  ([G24, Theorem 4.15].) -/
theorem HCD_stabilizes (δ : Cardinal.{u}) (h : Extendible δ.ord) (x : ZFSet.{u})
    (hx : HCD δ x) (η : Cardinal.{u}) : HCD η x := by
  admit

/-- The Blue–Goldberg exclusion is *not* admitted: it is re-derived in
`Cardinals.Below` (synthesis Corollary 6.3). -/
example : True := trivial

end Cardinals.Published

/-
  PUBLISHED RESULTS, ADMITTED WITHOUT PROOF.

  Every statement in this file is a result from the literature (or a textbook
  fact), stated in the framework of `Cardinals.Foundations` and closed by `admit`.
  Nothing else in the development is admitted.  Each entry records its source.

  References (every admitted statement cites one of these in its doc comment)
  * [ABL]  J. P. Aguilera, J. Bagaria, P. Lücke, "Large cardinals, structural reflection,
           and the HOD Conjecture", arXiv:2411.11568v4 (16 Sep 2025).
  * [ABGL] J. P. Aguilera, J. Bagaria, G. Goldberg, P. Lücke, "Large cardinals beyond HOD",
           arXiv:2509.10254v1 (12 Sep 2025).
  * [BG]   G. Goldberg, "Consistency beyond the Kunen inconsistency" (joint work with
           D. Blue), lecture notes, 1 July 2026,
           https://math.berkeley.edu/~goldberg/Slides/CoverExact.pdf
  * [G]    G. Goldberg, "The uniqueness of elementary embeddings", J. Symb. Log. 89 (2024)
           1430-1454; numbering below is that of arXiv:2103.13961v2 (the journal version
           is reported to be shifted by one in Section 4).
  * [Jech] T. Jech, "Set Theory", 3rd millennium ed., Springer 2003.
  * [Kan]  A. Kanamori, "The Higher Infinite", 2nd ed., Springer 2003.
  * [Kun71] K. Kunen, "Elementary embeddings and infinitary combinatorics",
           J. Symb. Log. 36 (1971) 407-413.
  * [Kun80] K. Kunen, "Set Theory: An Introduction to Independence Proofs",
           North-Holland 1980.
  The statement numbers of [ABL], [BG] and [G] were checked against the cited versions on
  18 September 2026.  Textbook citations are given at the level of chapters or sections
  where the exact theorem number was not checked.
-/
import Cardinals.Foundations.Exacting

universe u

namespace Cardinals.Published

open ZFSet Ordinal Cardinal Cardinals

/-! ### Exacting cardinals: the critical sequence ([Kun], [ABL §2], [BG]) -/

/-- An exacting cardinal has cofinality `ω`: the critical sequence of a witness is
cofinal, by the local Kunen inconsistency.

Reference: [ABL, remark following Definition 2.4]: "the Kunen inconsistency implies that all
exacting cardinals are elements of `C^(1)` with countable cofinality"; the Kunen
inconsistency for `V_{μ+2}` is [Kun71] and [Kan, Corollary 23.14].  The argument only uses
the restriction of the witness to `V_lam`, so it applies verbatim to witnesses carrying a
predicate.  See also [BG, proof of Observation 1].  (Synthesis Lemma 3.1.) -/
theorem cof_omega_of_witness (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : ∀ α > c.ord, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness c.ord α Y)) :
    ∃ s : ℕ → Ordinal.{u}, StrictMono s ∧ (∀ n, s n < c.ord) ∧ ∀ ξ < c.ord, ∃ n, ξ ≤ s n := by
  admit

/-- An exacting cardinal is uncountable: the restriction of a witness to `V_lam` is an
`I3` embedding, whose critical point is a measurable cardinal below `lam`.

Reference: [ABL, Section 2, discussion preceding Lemma 2.3]: the restriction of an exact
embedding to `V_lam` is an `I3`-embedding and `lam` is a limit of `n`-huge cardinals
(citing [Kan, p. 332]); measurability of critical points is [Kan, §5]. -/
theorem aleph0_lt_of_witness (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : ∀ α > c.ord, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness c.ord α Y)) :
    ℵ₀ < c := by
  admit

/-- An exacting cardinal is a strong limit.

Reference: [ABL, remark following Definition 2.4]: exacting cardinals are elements of
`C^(1)`, the class of `Σ₁`-correct cardinals, which are strong limit cardinals; see also
[Kan, §24] for `I3` cardinals. -/
theorem strongLimit_of_witness (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (h : ∀ α > c.ord, ∃ Y : ZFSet.{u}, Y ⊆ V_ α ∧ Nonempty (RelWitness c.ord α Y)) :
    ∀ μ < c, (2 : Cardinal.{u}) ^ μ < c := by
  admit

/-- No cardinal is exacting relative to a short cofinal subset of itself.

Reference: [BG, Observation 1(2)]: "If `Y ⊆ λ` is cofinal with `ot(Y) < λ`, there is no
`j : (V_α, Y) → (V_α, Y)`" (such a `j` has `crit(j) ≥ ot(Y)`, hence fixes `Y` pointwise).
The same mechanism proves [ABL, Theorem 2.10].  (Synthesis Lemma 3.2.) -/
theorem not_REx_shortCofinal (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (a : ZFSet.{u})
    (ha : ShortCofinal a c.ord) : ¬ REx c.ord a := by
  admit

/-- Definability transfer: relative exactingness passes from `Y` to every set
ordinal definable from `Y`.

Reference: [BG, Lemma 3.3]: "If `λ` is exacting relative to `Y` and `Y'` is ordinal
definable from `Y`, then `λ` is exacting relative to `Y'`."  (Synthesis Lemma 3.4.) -/
theorem REx_transfer (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (Y Z : ZFSet.{u})
    (hY : REx c.ord Y) (hZ : ODfrom (fun p => p = Y) Z) : REx c.ord Z := by
  admit

/-- The cover bound cannot be smaller than the cardinal.

Reference: [BG, remark following Definition 3.1]: "If `γ < λ`, then `λ` is not `γ`-cover
exacting by the argument that refutes relativized exacting cardinals."
(Synthesis Lemma 3.5.) -/
theorem le_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) : c ≤ γ := by
  admit

/-- Stationary characterization of cover exactingness, forward direction:
the relatively exacting predicates of size at most `γ` are stationary in
`P_{γ⁺}(V_ α)` for all large `α`.

Reference: [BG, Proposition 3.4, (1) ⇒ (3)]: "`λ` is `γ`-cover exacting" is equivalent to
"for all `α`, `λ` is exacting relative to a stationary set of `σ ∈ P_{γ⁺}(V_α)`".
[BG, Definition 3.2] asks for witnesses at every height `α ≥ rank(Y)`; `REx` only asks for
all large heights, so the statement here is a consequence. -/
theorem stationary_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) :
    ∃ α₀, ∀ α ≥ α₀, IsStationaryPkA (Order.succ γ) (V_ α) {σ | REx c.ord σ} := by
  admit

/-! ### Textbook facts ([Jech]) -/

/-- Elementary substructures of `(V_ α, ∈)` of size below a regular uncountable `κ`
that contain a given finite set form a club in `P_κ(V_ α)`.

Reference: [Jech, Chapter 8, section on closed unbounded and stationary sets in `P_κ(A)`]
(a club contains the closure set `C_F` of some `F : [A]^{<ω} → A`), together with the
downward Löwenheim–Skolem theorem and the elementary chain theorem [Jech, Chapter 12];
see also [Kan, §25]. -/
theorem isClub_elemSub (κ : Cardinal.{u}) (hκ : κ.IsRegular) (hκ' : ℵ₀ < κ)
    (α : Ordinal.{u}) (F : List ZFSet.{u}) (hF : ∀ x ∈ F, x ∈ V_ α) :
    IsClubPkA κ (V_ α)
      {σ | σ ∈ PkA κ (V_ α) ∧ ElemSub σ (V_ α) ∧ ∀ x ∈ F, x ∈ σ} := by
  admit

/-- Ordinal definability composes: if `x` is ordinal definable from parameters each
of which is ordinal definable from `Q`-parameters, then `x` is ordinal definable
from `Q`-parameters.

Reference: [Jech, Chapter 13, section "Ordinal-definable sets"]: a set is ordinal definable
from parameters in a class iff it is definable over some `V_θ` from such parameters, by the
Reflection Principle [Jech, Theorem 12.14]; closure under composition is immediate from
the `V`-definability form. -/
theorem ODfrom_trans (P Q : ZFSet.{u} → Prop) (x : ZFSet.{u}) (hx : ODfrom P x)
    (hPQ : ∀ p, P p → ODfrom Q p) : ODfrom Q x := by
  admit

/-- Every extendible cardinal is strongly compact (indeed supercompact).

Reference: [Kan, Proposition 23.6] (extendible cardinals are supercompact) and
[Kan, §22], [Jech, Chapter 20] (supercompact cardinals are strongly compact; the filter
extension property is the definition of strong compactness in [Jech, Chapter 20]). -/
theorem SC_of_extendible (δ : Cardinal.{u}) (h : Extendible δ.ord) : SC δ := by
  admit

/-! ### Goldberg's theorems on `HCD` ([G24, §4]) -/

/-- `HCD(η)` is an inner model of ZF.

Reference: [G, Proposition 4.2] (arXiv v2): "For any cardinal `κ`, `HCD(κ)` is an inner
model of ZF." -/
theorem HCD_isInnerModelZF (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : IsInnerModelZF (HCD η) := by
  admit

/-- If `δ` is strongly compact, `HCD(δ)` satisfies ZFC.

Reference: [G, Theorem 4.3] (arXiv v2): "If `κ` is a strongly compact cardinal, then
`HCD(κ)` is a model of ZFC." -/
theorem HCD_isInnerModelZFC (δ : Cardinal.{u}) (hδ : SC δ) : IsInnerModelZFC (HCD δ) := by
  admit

/-- If `δ` is strongly compact, `HCD(δ)` has the `δ`-cover property; we record the
instance for sets of ordinals.

Reference: [G, Theorem 4.13] (arXiv v2): "If `κ` is strongly compact, then `HCD(κ)` has the
`κ`-approximation and cover properties." -/
theorem HCD_cover (δ : Cardinal.{u}) (hδ : SC δ) (lam : Ordinal.{u}) (a : ZFSet.{u})
    (ha : SubOrd a lam) (hcard : ZFSet.card a < δ) :
    ∃ b : ZFSet.{u}, HCD δ b ∧ a ⊆ b ∧ ZFSet.card b < δ := by
  admit

/-- If `δ` is extendible, the `HCD` hierarchy stabilizes at `δ`:
`HCD(δ) = HCD = ⋂ HCD(η)`.

Reference: [G, Theorem 4.14] (arXiv v2): "Suppose `κ` is an extendible cardinal.  Then
`HCD(κ) = HCD`." -/
theorem HCD_stabilizes (δ : Cardinal.{u}) (h : Extendible δ.ord) (x : ZFSet.{u})
    (hx : HCD δ x) (η : Cardinal.{u}) : HCD η x := by
  admit

/-- The Blue–Goldberg exclusion is *not* admitted: it is re-derived in
`Cardinals.Below` (synthesis Corollary 6.3). -/
example : True := trivial

end Cardinals.Published

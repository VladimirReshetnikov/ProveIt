/-
  Ordinal-combinatorial cores of the synthesis:

  * critical-sequence dynamics (Lemma 3.1, second half; Lemma 3.2, last step),
  * a strictly monotone map of a set of ordinals onto itself is the identity
    (used in the finite-valued transversal theorem 9.10),
  * a cofinal ω-sequence meets every bounded set in a finite set
    (Corollary 5.5, Proposition 8.3, Theorem 10.7(4)),
  * small families of ordinals below an ordinal of large cofinality are bounded
    (the "possible values" step of Lemma 7.1),
  * the dominating-enumeration step of the internal unbounded-range theorem 11.2,
  * the projection-width argument of Theorem 8.1.

  Everything in this file is proved; there are no admitted statements.
-/
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import Mathlib.Tactic

universe u

namespace Cardinals.OrdinalLemmas

open Ordinal Cardinal Set

/-! ### Critical-sequence dynamics -/

/-- If the iterates `κ, e κ, e (e κ), …` of a map that is monotone below `lam`
are cofinal in `lam`, then `e` moves every ordinal of `[κ, lam)` strictly
upwards.  (Synthesis Lemma 3.1, second assertion.) -/
theorem moved_above_crit (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hmono : ∀ a b, a ≤ b → b < lam → e a ≤ e b)
    (hcof : ∀ ξ < lam, ∃ n : ℕ, ξ < e^[n] κ) :
    ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ := by
  intro ξ hκ hξ
  classical
  have hex := hcof ξ hξ
  have hm : ξ < e^[Nat.find hex] κ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hm
    exact absurd hm (not_lt.mpr hκ)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hk' : ¬ ξ < e^[k] κ := Nat.find_min hex (by omega)
  have hle : e^[k] κ ≤ ξ := not_lt.mp hk'
  calc ξ < e^[Nat.find hex] κ := hm
    _ = e (e^[k] κ) := by rw [hk, Function.iterate_succ_apply']
    _ ≤ e ξ := hmono _ _ hle hξ

/-- A cofinal subset of `lam` cannot consist of fixed points of such a map.
(Last step of synthesis Lemma 3.2.) -/
theorem no_fixed_cofinal_set (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hκ : κ < lam)
    (hmono : ∀ a b, a ≤ b → b < lam → e a ≤ e b)
    (hcof : ∀ ξ < lam, ∃ n : ℕ, ξ < e^[n] κ)
    (a : Set Ordinal.{u}) (ha : ∀ x ∈ a, x < lam)
    (hacof : ∀ ξ < lam, ∃ x ∈ a, ξ ≤ x)
    (hfix : ∀ x ∈ a, e x = x) : False := by
  obtain ⟨x, hxa, hx⟩ := hacof κ hκ
  have := moved_above_crit e lam κ hmono hcof x hx (ha x hxa)
  rw [hfix x hxa] at this
  exact lt_irrefl _ this

/-! ### Monotone self-bijections of sets of ordinals -/

/-- A strictly monotone map of a set of ordinals onto itself fixes it pointwise.
(Used for `e^p ↾ b` in synthesis Theorem 9.10.) -/
theorem strictMonoOn_image_eq_self (g : Ordinal.{u} → Ordinal.{u}) (b : Set Ordinal.{u})
    (hg : StrictMonoOn g b) (hb : g '' b = b) : ∀ x ∈ b, g x = x := by
  by_contra hne
  push Not at hne
  let bad : Set Ordinal.{u} := {x | x ∈ b ∧ g x ≠ x}
  have hbad : bad.Nonempty := by
    obtain ⟨x, hx, hgx⟩ := hne
    exact ⟨x, hx, hgx⟩
  let x := wellFounded_lt.min bad hbad
  have hx : x ∈ bad := wellFounded_lt.min_mem bad hbad
  have hmin : ∀ y ∈ bad, ¬ y < x := fun y hy h => (wellFounded_lt.not_lt_min bad hy) h
  have hgb : ∀ y ∈ b, g y ∈ b := fun y hy => hb ▸ mem_image_of_mem g hy
  rcases lt_or_gt_of_ne hx.2 with hlt | hgt
  · -- g x < x
    have h1 : g x ∈ b := hgb x hx.1
    have h2 : g (g x) < g x := hg h1 hx.1 hlt
    exact hmin (g x) ⟨h1, ne_of_lt h2⟩ hlt
  · -- x < g x
    have hxim : x ∈ g '' b := hb.symm ▸ hx.1
    obtain ⟨y, hy, hyx⟩ := hxim
    rcases lt_trichotomy y x with h | h | h
    · have : g y = y := by
        by_contra hc
        exact hmin y ⟨hy, hc⟩ h
      rw [this] at hyx
      exact absurd hyx (ne_of_lt h)
    · rw [h] at hyx
      exact hx.2 hyx
    · have := hg hx.1 hy h
      rw [hyx] at this
      exact lt_asymm this hgt

/-! ### Cofinal ω-sequences have finite bounded traces -/

/-- Only finitely many terms of a strictly increasing sequence lie below a bound
that is exceeded by some term. -/
theorem finite_terms_below (s : ℕ → Ordinal.{u}) (hs : StrictMono s) (β : Ordinal.{u})
    (N : ℕ) (hN : β ≤ s N) : {n | s n < β}.Finite := by
  apply (Set.finite_lt_nat N).subset
  intro n hn
  exact hs.lt_iff_lt.mp (lt_of_lt_of_le hn hN)

/-- A cofinal `ω`-sequence in `lam` meets every subset of `lam` that is bounded
below `lam` in a finite set. -/
theorem finite_inter_of_bounded (s : ℕ → Ordinal.{u}) (hs : StrictMono s) (lam : Ordinal.{u})
    (hcof : ∀ ξ < lam, ∃ n, ξ ≤ s n) (b : Set Ordinal.{u})
    (β : Ordinal.{u}) (hβ : β < lam) (hb : ∀ x ∈ b, x < β) :
    (Set.range s ∩ b).Finite := by
  obtain ⟨N, hN⟩ := hcof β hβ
  have hfin := (finite_terms_below s hs β N hN).image s
  apply hfin.subset
  rintro x ⟨⟨n, rfl⟩, hxb⟩
  exact ⟨n, hb _ hxb, rfl⟩

/-! ### Small families are bounded below an ordinal of large cofinality -/

/-- Fewer than `cof o` ordinals below `o` have a common bound below `o`. -/
theorem bounded_of_lt_cof {ι : Type u} (f : ι → Ordinal.{u}) (o : Ordinal.{u})
    (hι : #ι < o.cof) (hf : ∀ i, f i < o) : ∃ β < o, ∀ i, f i ≤ β :=
  ⟨⨆ i, f i, Ordinal.iSup_lt_of_lt_cof hι hf, Ordinal.le_iSup f⟩

/-- The "possible values" step of the chain-condition lemma (synthesis Lemma 7.1):
countably many families `B n`, each of size below `cof o`, of ordinals below `o`,
are jointly bounded below `o`, provided `cof o` is uncountable. -/
theorem countable_union_bounded {ι : ℕ → Type u} (f : ∀ n, ι n → Ordinal.{u}) (o : Ordinal.{u})
    (hunc : ℵ₀ < o.cof) (hι : ∀ n, #(ι n) < o.cof) (hf : ∀ n i, f n i < o) :
    ∃ β < o, ∀ n i, f n i ≤ β := by
  choose β hβ hβf using fun n => bounded_of_lt_cof (f n) o (hι n) (hf n)
  have hN : #(ULift.{u} ℕ) < o.cof := by simpa using hunc
  obtain ⟨γ, hγ, hγβ⟩ := bounded_of_lt_cof (fun n : ULift.{u} ℕ => β n.down) o hN
    (fun n => hβ n.down)
  exact ⟨γ, hγ, fun n i => (hβf n i).trans (hγβ ⟨n⟩)⟩

/-- Hence a name for a cofinal `ω`-sequence cannot have all its sets of possible
values small: some term of any sequence dominated by the families is bounded. -/
theorem not_cofinal_of_small_value_sets {ι : ℕ → Type u} (f : ∀ n, ι n → Ordinal.{u})
    (o : Ordinal.{u}) (hunc : ℵ₀ < o.cof) (hι : ∀ n, #(ι n) < o.cof)
    (hf : ∀ n i, f n i < o)
    (c : ℕ → Ordinal.{u}) (hc : ∀ n, ∃ i, c n = f n i)
    (hcof : ∀ ξ < o, ∃ n, ξ < c n) : False := by
  obtain ⟨β, hβ, hb⟩ := countable_union_bounded f o hunc hι hf
  obtain ⟨n, hn⟩ := hcof β hβ
  obtain ⟨i, hi⟩ := hc n
  exact absurd (hi ▸ hb n i) (not_le.mpr hn)

/-! ### The dominating-enumeration step (synthesis Theorem 11.2) -/

/-- The closure set of a function. -/
def closurePoints (θ : Ordinal.{u}) (g : Ordinal.{u} → Ordinal.{u}) : Set Ordinal.{u} :=
  {β | β < θ ∧ ∀ ξ < β, g ξ < β}

/-- If `f` dominates `j` pointwise below `θ`, then the closure points of `f`
are closure points of `j`. -/
theorem closurePoints_mono (θ : Ordinal.{u}) (j f : Ordinal.{u} → Ordinal.{u})
    (hdom : ∀ ξ < θ, j ξ ≤ f ξ) : closurePoints θ f ⊆ closurePoints θ j := by
  rintro β ⟨hβ, hcl⟩
  exact ⟨hβ, fun ξ hξ => lt_of_le_of_lt (hdom ξ (hξ.trans hβ)) (hcl ξ hξ)⟩

/-- If `A = j '' B` is enumerated increasingly by `f` (so `f ξ = j (b ξ)` with
`ξ ≤ b ξ`), then `f` dominates `j`. -/
theorem enum_dominates (θ : Ordinal.{u}) (j f b : Ordinal.{u} → Ordinal.{u})
    (hj : ∀ ξ η, ξ ≤ η → η < θ → j ξ ≤ j η)
    (hb : ∀ ξ < θ, ξ ≤ b ξ ∧ b ξ < θ) (hf : ∀ ξ < θ, f ξ = j (b ξ)) :
    ∀ ξ < θ, j ξ ≤ f ξ := by
  intro ξ hξ
  rw [hf ξ hξ]
  exact hj _ _ (hb ξ hξ).1 (hb ξ hξ).2

/-- **Core of the internal unbounded-range theorem.**  Let `T` be a set that
the target model regards as stationary (so it meets the closure set `D_f` of
every function `f` in the model), but that is disjoint from the closure club
`C_j` of `j`.  Then no function `f` of the model can dominate `j` below `θ`;
in particular no increasing enumeration of an unbounded subset of `j '' θ`
belongs to the model. -/
theorem no_dominating_function (θ : Ordinal.{u}) (j f : Ordinal.{u} → Ordinal.{u})
    (T : Set Ordinal.{u})
    (hdisj : ∀ β ∈ closurePoints θ j, β ∉ T)
    (hstat : ∃ β ∈ closurePoints θ f, β ∈ T)
    (hdom : ∀ ξ < θ, j ξ ≤ f ξ) : False := by
  obtain ⟨β, hβ, hT⟩ := hstat
  exact hdisj β (closurePoints_mono θ j f hdom hβ) hT

/-! ### Projection width (synthesis Theorem 8.1) -/

/-- **Projection-width core.**  `Reg` is the class of functions `μ → lam`
available in an inner model in which `lam` is regular: every member that is
pointwise below `lam` is bounded below `lam`.  If `F` is a nonempty family of
cofinal maps and the pointwise-supremum function of `F` (which is definable
from `F`) is available whenever all projections are bounded, then some
coordinate projection of `F` is unbounded in `lam`. -/
theorem exists_unbounded_projection {μ : Type u} (lam : Ordinal.{u})
    (F : Set (μ → Ordinal.{u})) (hF : F.Nonempty)
    (hcof : ∀ f ∈ F, ∀ β < lam, ∃ ξ, β < f ξ)
    (Reg : (μ → Ordinal.{u}) → Prop)
    (hreg : ∀ b, Reg b → (∀ ξ, b ξ ≤ lam) → (∀ ξ, b ξ < lam) → ∃ β < lam, ∀ ξ, b ξ ≤ β)
    (b : μ → Ordinal.{u}) (hb : ∀ ξ, ∀ f ∈ F, f ξ ≤ b ξ)
    (hbsup : ∀ ξ, (∃ β < lam, ∀ f ∈ F, f ξ < β) → b ξ < lam)
    (hble : ∀ ξ, b ξ ≤ lam)
    (hbReg : Reg b) :
    ∃ ξ, ∀ β < lam, ∃ f ∈ F, β ≤ f ξ := by
  by_contra hcon
  push Not at hcon
  have hblt : ∀ ξ, b ξ < lam := fun ξ => hbsup ξ (hcon ξ)
  obtain ⟨β, hβ, hβb⟩ := hreg b hbReg hble hblt
  obtain ⟨f, hf⟩ := hF
  obtain ⟨ξ, hξ⟩ := hcof f hf β hβ
  exact absurd ((hb ξ f hf).trans (hβb ξ)) (not_le.mpr hξ)

end Cardinals.OrdinalLemmas

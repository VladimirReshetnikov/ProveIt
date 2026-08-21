import ExponentialIdentities.TwoBaseIntegerExponent.MixedExponentSemigroup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Sqrt

/-!
# The crude semigroup weight bound and the window-counting bridge

This file formalizes the two *combinatorial* halves of the semigroup determinant chain of the
Alaoglu--Erdős further report: the crude weight bound for the mixed-exponent semigroup
(the report's Lemma "Crude semigroup weight bound") and the window-summation counting step
behind its "Semigroup interval count" corollary.  Neither statement mentions a determinant,
so both are reusable by the ordinary-power route and by the semigroup route alike.

## The square-box weight bound

The exponent semigroup `Λ_θ = {a + b θ : a, b ∈ ℕ}` and its pair parametrization
`mixedExponent` are developed in `MixedExponentSemigroup.lean`; in particular that file
supplies `mixedExponent_le_three_mul`, the bound `a + b θ ≤ 3 q` for a pair from the square
box `[0, q]²`, which comes from `1 < θ < 8/5 < 2`.

The quantitative input needed downstream is a bound on the total weight `Σ_r` of the `r + 1`
smallest exponents, relative to `R_r = r (r+1) / 2`.  The report's proof avoids all lattice
point counting: choose the square box `[0, q]²` with `(q+1)² ≥ r + 1` and take any `r + 1` of
its pairs; every one of them has weight at most `3 q`, so `Σ_r ≤ 3 q (r+1)`.  Taking
`q = Nat.sqrt r` gives `(q+1)² > r` (`Nat.lt_succ_sqrt`) together with `q ≤ √r`
(`Nat.sqrt_le'`), whence

  `mixedExponent (ab j) ≤ 3 √r ≤ 6 √r`,  `Σ_r ≤ 6 (r+1) √r`,  `Σ_r / R_r ≤ 12 / √r`,

which is exactly the report's `eq:crude-semigroup`.

Following the report's own advice, we do **not** construct the globally sorted semigroup:
`exists_mixedExponent_family` merely asserts the *existence* of an injective family of `r + 1`
pairs with the stated bounds, which is all the determinant estimate consumes.  The
`Fin (r+1)`-indexed family is produced by `exists_injective_box_family` from base-`(q+1)`
digits, so no ordering of the box has to be constructed either.

## The window-counting bridge

The second half converts a *span* hypothesis into a *cardinality* bound.  If every `r + 1`
elements of a finite set `S ⊆ [N, N+H]` contain two points at distance at least `L`, then no
half-open block `[N + kL, N + (k+1)L)` can contain more than `r` elements of `S`, and the
`⌊H/L⌋ + 1` blocks cover `[N, N+H]`.  Pigeonhole then gives

  `#S ≤ r * (⌊H/L⌋ + 1) ≤ r + r H / L`,

which is exactly the report's `#(Cand ∩ [N, N+H]) ≤ r + r H / L` with `L` the span lower
bound.  This block form of the argument replaces the report's sliding-window summation (where
"each adjacent gap is counted at most `r` times") by a single application of
`Finset.card_le_mul_card_image_of_maps_to`; the resulting inequality is identical.

Three formulations of the span hypothesis are provided: subsets of cardinality `r + 1`
(`card_le_of_window_span`), strictly increasing `Fin (r+1)`-indexed families
(`card_le_of_window_span_of_strictMono`, the shape a generalized Vandermonde span theorem
produces), and a natural-number interval version (`card_le_of_window_span_Icc`).
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-! ### The square-box weight bound -/

/-- **Square-box family.**  Whenever `r + 1` pairs fit into the `(q+1) × (q+1)` box
`[0, q] × [0, q]`, there is an injective family of `r + 1` pairs inside that box.  The
witness is the base-`(q+1)` digit pair `j ↦ (j % (q+1), j / (q+1))`. -/
theorem exists_injective_box_family (r q : ℕ) (hcard : r + 1 ≤ (q + 1) * (q + 1)) :
    ∃ ab : Fin (r + 1) → ℕ × ℕ, Function.Injective ab ∧
      ∀ j, (ab j).1 ≤ q ∧ (ab j).2 ≤ q := by
  refine ⟨fun j => ((j : ℕ) % (q + 1), (j : ℕ) / (q + 1)), ?_, ?_⟩
  · intro i j hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨h1, h2⟩ := hij
    have hval : (i : ℕ) = (j : ℕ) := by
      calc (i : ℕ) = (q + 1) * ((i : ℕ) / (q + 1)) + (i : ℕ) % (q + 1) :=
            (Nat.div_add_mod _ _).symm
        _ = (q + 1) * ((j : ℕ) / (q + 1)) + (j : ℕ) % (q + 1) := by rw [h1, h2]
        _ = (j : ℕ) := Nat.div_add_mod _ _
    exact Fin.val_injective hval
  · intro j
    have hq1 : 0 < q + 1 := Nat.succ_pos q
    have hj : (j : ℕ) < (q + 1) * (q + 1) := lt_of_lt_of_le j.isLt hcard
    refine ⟨?_, ?_⟩
    · show (j : ℕ) % (q + 1) ≤ q
      exact Nat.lt_succ_iff.mp (Nat.mod_lt _ hq1)
    · show (j : ℕ) / (q + 1) ≤ q
      exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq1).mpr hj)

/-- **Crude semigroup weight bound, existence form.**  For every `r` there are `r + 1`
distinct exponent pairs whose mixed exponents are all at most `6 √r` and whose total weight is
at most `6 (r+1) √r`.

This is the report's Lemma "Crude semigroup weight bound", with the globally sorted semigroup
replaced by an arbitrary admissible family — the only thing the determinant estimate uses.
The report assumes `2 ≤ r`; that hypothesis is not needed here, because the box side
`q = Nat.sqrt r` already satisfies `q ≤ √r`, whereas the report's `q = ⌈√(r+1)⌉` only
satisfies `q ≤ 2 √r` for `r ≥ 2`.  For the same reason the proof actually delivers the
sharper constant `3` in place of `6`; the weaker constant is kept to match the report. -/
theorem exists_mixedExponent_family (r : ℕ) :
    ∃ ab : Fin (r + 1) → ℕ × ℕ, Function.Injective ab ∧
      (∀ j, mixedExponent (ab j) ≤ 6 * Real.sqrt (r : ℝ)) ∧
      (∑ j, mixedExponent (ab j)) ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by
  have hbox0 : r + 1 ≤ (Nat.sqrt r + 1) * (Nat.sqrt r + 1) := Nat.lt_succ_sqrt r
  obtain ⟨ab, hinj, hbox⟩ := exists_injective_box_family r (Nat.sqrt r) hbox0
  have hqle : ((Nat.sqrt r : ℕ) : ℝ) ≤ Real.sqrt (r : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h : Nat.sqrt r ^ 2 ≤ r := Nat.sqrt_le' r
    exact_mod_cast h
  have hsr : (0 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hle : ∀ j, mixedExponent (ab j) ≤ 6 * Real.sqrt (r : ℝ) := by
    intro j
    obtain ⟨h1, h2⟩ := hbox j
    have hthree : mixedExponent (ab j) ≤ 3 * ((Nat.sqrt r : ℕ) : ℝ) :=
      mixedExponent_le_three_mul h1 h2
    linarith [hthree, hqle, hsr]
  refine ⟨ab, hinj, hle, ?_⟩
  calc (∑ j : Fin (r + 1), mixedExponent (ab j))
      ≤ ∑ _j : Fin (r + 1), (6 * Real.sqrt (r : ℝ)) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = ((r : ℝ) + 1) * (6 * Real.sqrt (r : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ = 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by ring

/-- **Distinct exponents.**  The family of `exists_mixedExponent_family` has pairwise distinct
mixed exponents, which is the report's "the `(q+1)²` pairs give distinct exponents".  The
distinctness rests on the irrationality of `θ`, through `mixedExponent_injective`. -/
theorem exists_mixedExponent_family_distinct (r : ℕ) :
    ∃ ab : Fin (r + 1) → ℕ × ℕ, Function.Injective (fun j => mixedExponent (ab j)) ∧
      (∀ j, mixedExponent (ab j) ≤ 6 * Real.sqrt (r : ℝ)) ∧
      (∑ j, mixedExponent (ab j)) ≤ 6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ) := by
  obtain ⟨ab, hinj, hle, hsum⟩ := exists_mixedExponent_family r
  exact ⟨ab, mixedExponent_injective.comp hinj, hle, hsum⟩

/-- **Crude semigroup weight bound, ratio form.**  With `R_r = r (r+1) / 2`, the family of
`exists_mixedExponent_family` satisfies `Σ_r / R_r ≤ 12 / √r`.  This is the second inequality
of the report's `eq:crude-semigroup`; it is the exponent deficit that enters the determinant
span estimate, and it is `≤ 1` as soon as `r ≥ 144`. -/
theorem exists_mixedExponent_family_ratio (r : ℕ) (hr : 1 ≤ r) :
    ∃ ab : Fin (r + 1) → ℕ × ℕ, Function.Injective ab ∧
      (∀ j, mixedExponent (ab j) ≤ 6 * Real.sqrt (r : ℝ)) ∧
      (∑ j, mixedExponent (ab j)) / ((r : ℝ) * ((r : ℝ) + 1) / 2)
        ≤ 12 / Real.sqrt (r : ℝ) := by
  obtain ⟨ab, hinj, hle, hsum⟩ := exists_mixedExponent_family r
  refine ⟨ab, hinj, hle, ?_⟩
  have hr0 : 0 < r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrpos
  have hsq : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
    Real.mul_self_sqrt hrpos.le
  have hR : (0 : ℝ) < (r : ℝ) * ((r : ℝ) + 1) / 2 := by positivity
  rw [div_le_div_iff₀ hR hs]
  calc (∑ j, mixedExponent (ab j)) * Real.sqrt (r : ℝ)
      ≤ (6 * ((r : ℝ) + 1) * Real.sqrt (r : ℝ)) * Real.sqrt (r : ℝ) :=
        mul_le_mul_of_nonneg_right hsum (Real.sqrt_nonneg _)
    _ = 6 * ((r : ℝ) + 1) * (Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ)) := by ring
    _ = 6 * ((r : ℝ) + 1) * (r : ℝ) := by rw [hsq]
    _ = 12 * ((r : ℝ) * ((r : ℝ) + 1) / 2) := by ring

/-! ### The window-counting bridge -/

/-- **Window span implies a count bound.**  Let `S` be a finite set of naturals contained in
`[N, N+H]` such that every `r + 1` of its elements contain two points at distance at least
`L > 0`.  Then `#S ≤ r + r H / L`.

This is the abstract engine behind the report's "Semigroup interval count" (and equally behind
the ordinary-power `cor:ordinary-count`): the span lower bound `L` is supplied by whichever
determinant theorem is in force, and this lemma turns it into a cardinality bound.

The proof partitions `[N, N+H]` into the `⌊H/L⌋ + 1` half-open blocks
`[N + kL, N + (k+1)L)`.  Two points of the same block are at distance `< L`, so each block
meets `S` in at most `r` points, and pigeonhole finishes. -/
theorem card_le_of_window_span {S : Finset ℕ} {r : ℕ} {L N H : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ S, N ≤ (x : ℝ) ∧ (x : ℝ) ≤ N + H)
    (hspan : ∀ T ⊆ S, T.card = r + 1 → ∃ a ∈ T, ∃ b ∈ T, L ≤ (b : ℝ) - (a : ℝ)) :
    (S.card : ℝ) ≤ (r : ℝ) + (r : ℝ) * H / L := by
  -- Every element of `S` lands in one of the `⌊H/L⌋ + 1` blocks.
  have hmaps : ∀ x ∈ S, ⌊((x : ℝ) - N) / L⌋₊ ∈ Finset.range (⌊H / L⌋₊ + 1) := by
    intro x hx
    obtain ⟨_, hx2⟩ := hbound x hx
    have hstep : ((x : ℝ) - N) / L ≤ H / L :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_mono hstep
  -- No block contains `r + 1` elements of `S`, since its diameter is `< L`.
  have hfiber : ∀ b ∈ Finset.range (⌊H / L⌋₊ + 1),
      (S.filter (fun x : ℕ => ⌊((x : ℝ) - N) / L⌋₊ = b)).card ≤ r := by
    intro b _
    by_contra hcon
    have hge : r + 1 ≤ (S.filter (fun x : ℕ => ⌊((x : ℝ) - N) / L⌋₊ = b)).card := by omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    have hTS : T ⊆ S := fun x hx => Finset.mem_of_mem_filter x (hTsub hx)
    obtain ⟨a, haT, c, hcT, hac⟩ := hspan T hTS hTcard
    have haS : a ∈ S := (Finset.mem_filter.mp (hTsub haT)).1
    have hab : ⌊((a : ℝ) - N) / L⌋₊ = b := (Finset.mem_filter.mp (hTsub haT)).2
    have hcb : ⌊((c : ℝ) - N) / L⌋₊ = b := (Finset.mem_filter.mp (hTsub hcT)).2
    have han : (0 : ℝ) ≤ ((a : ℝ) - N) / L :=
      div_nonneg (by linarith [(hbound a haS).1]) hL.le
    have h1 : (b : ℝ) ≤ ((a : ℝ) - N) / L := by
      have hfa := Nat.floor_le han
      rwa [hab] at hfa
    have h2 : ((c : ℝ) - N) / L < (b : ℝ) + 1 := by
      have hfc := Nat.lt_floor_add_one (((c : ℝ) - N) / L)
      rwa [hcb] at hfc
    have hsplit : ((c : ℝ) - (a : ℝ)) / L
        = ((c : ℝ) - N) / L - ((a : ℝ) - N) / L := by ring
    have hdiff : ((c : ℝ) - (a : ℝ)) / L < 1 := by rw [hsplit]; linarith
    have hlt : (c : ℝ) - (a : ℝ) < L := (div_lt_one hL).mp hdiff
    linarith
  -- Pigeonhole over the blocks.
  have hcard : S.card ≤ r * (⌊H / L⌋₊ + 1) := by
    have hpig := Finset.card_le_mul_card_image_of_maps_to
      (f := fun x : ℕ => ⌊((x : ℝ) - N) / L⌋₊)
      (t := Finset.range (⌊H / L⌋₊ + 1)) hmaps r hfiber
    simpa [Finset.card_range] using hpig
  have hcardR : (S.card : ℝ) ≤ (r : ℝ) * ((⌊H / L⌋₊ : ℝ) + 1) := by exact_mod_cast hcard
  have hfloor : ((⌊H / L⌋₊ : ℕ) : ℝ) ≤ H / L := Nat.floor_le (div_nonneg hH hL.le)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  calc (S.card : ℝ) ≤ (r : ℝ) * ((⌊H / L⌋₊ : ℝ) + 1) := hcardR
    _ ≤ (r : ℝ) * (H / L + 1) := mul_le_mul_of_nonneg_left (by linarith) hr0
    _ = (r : ℝ) + (r : ℝ) * H / L := by ring

/-- **Window span implies a count bound, ordered-family form.**  Same conclusion as
`card_le_of_window_span`, but with the span hypothesis phrased for strictly increasing
`Fin (r+1)`-indexed families `m 0 < ⋯ < m r` of elements of `S`.  This is the shape a
generalized Vandermonde span theorem produces. -/
theorem card_le_of_window_span_of_strictMono {S : Finset ℕ} {r : ℕ} {L N H : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H)
    (hbound : ∀ x ∈ S, N ≤ (x : ℝ) ∧ (x : ℝ) ≤ N + H)
    (hspan : ∀ m : Fin (r + 1) → ℕ, StrictMono m → (∀ j, m j ∈ S) →
      L ≤ (m (Fin.last r) : ℝ) - (m 0 : ℝ)) :
    (S.card : ℝ) ≤ (r : ℝ) + (r : ℝ) * H / L := by
  refine card_le_of_window_span hL hH hbound ?_
  intro T hTS hTcard
  refine ⟨T.orderEmbOfFin hTcard 0, T.orderEmbOfFin_mem hTcard 0,
    T.orderEmbOfFin hTcard (Fin.last r), T.orderEmbOfFin_mem hTcard (Fin.last r), ?_⟩
  exact hspan (fun j => T.orderEmbOfFin hTcard j) (T.orderEmbOfFin hTcard).strictMono
    (fun j => hTS (T.orderEmbOfFin_mem hTcard j))

/-- **Window span implies a count bound, natural-interval form.**  The specialization of
`card_le_of_window_span` to `S ⊆ Finset.Icc N (N + H)` with natural endpoints, which is the
form the candidate-counting corollaries use. -/
theorem card_le_of_window_span_Icc {S : Finset ℕ} {r N H : ℕ} {L : ℝ} (hL : 0 < L)
    (hsub : S ⊆ Finset.Icc N (N + H))
    (hspan : ∀ T ⊆ S, T.card = r + 1 → ∃ a ∈ T, ∃ b ∈ T, L ≤ (b : ℝ) - (a : ℝ)) :
    (S.card : ℝ) ≤ (r : ℝ) + (r : ℝ) * (H : ℝ) / L := by
  refine card_le_of_window_span (N := (N : ℝ)) hL (by positivity) ?_ hspan
  intro x hx
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp (hsub hx)
  refine ⟨by exact_mod_cast hx1, ?_⟩
  have hx2' : ((x : ℕ) : ℝ) ≤ ((N + H : ℕ) : ℝ) := by exact_mod_cast hx2
  push_cast at hx2'
  linarith

end LeanProofs.TwoBaseIntegerExponent

/- Modified for ProveIt: use Mathlib v4.32.0's generic prod_le_prod'
for product comparisons. Mathematical statements unchanged. -/
import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.FinitePrimitiveCorrectionBudget
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberRepresentatives
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTagRestrictionBudget
import OAI.Combinatorics.Progressions.Sampling.FiniteNormalizedRealGridCorrection

namespace OAI

section

namespace Erdos3

private theorem boundedExponentWindow_finite (K : Type*) [Fintype K] (s : ℕ) :
    ({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)).Finite := by
  classical
  let S := {m : K →₀ ℕ // m.sum (fun _ n => n) ≤ s}
  let f : S → List.Vector (Option K) s := fun m => paddedExponentWord m.val s m.property
  have hf : Function.Injective f := by
    intro m n hmn
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg
      (fun v : List.Vector (Option K) s => (v.val : Multiset (Option K)).count (some k)) hmn
    simpa only [f, paddedExponentWord_count] using hc
  let _ : Finite ↥({m : K →₀ ℕ | m.sum (fun _ n => n) ≤ s} : Set (K →₀ ℕ)) :=
    Finite.of_injective f hf
  exact Set.toFinite _

noncomputable def boundedExponentWindow (K : Type*) [Fintype K] (s : ℕ) :
    Finset (K →₀ ℕ) :=
  (boundedExponentWindow_finite K s).toFinset

@[simp] theorem boundedExponentWindow_mem_iff {K : Type*} [Fintype K]
    (s : ℕ) (m : K →₀ ℕ) :
    m ∈ boundedExponentWindow K s ↔ m.sum (fun _ n => n) ≤ s :=
  (boundedExponentWindow_finite K s).mem_toFinset

theorem boundedExponentWindow_card_le (K : Type*) [Fintype K] (s : ℕ) :
    (boundedExponentWindow K s).card ≤ (Fintype.card K + 1) ^ s :=
  boundedExponentSet_card_le _ s (fun m hm => (boundedExponentWindow_mem_iff s m).mp hm)

theorem support_subset_boundedExponentWindow {K R : Type*} [Fintype K] [CommSemiring R]
    (p : MvPolynomial K R) {s : ℕ} (hp : p.totalDegree ≤ s) :
    p.support ⊆ boundedExponentWindow K s := by
  intro m hm
  exact (boundedExponentWindow_mem_iff s m).mpr ((MvPolynomial.le_totalDegree hm).trans hp)

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

theorem exists_finite_subspace_normalized_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)
    (P : MvPolynomial (U ⊕ B) ℝ)
    (S : Finset ((U ⊕ I) →₀ ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (q : ℕ) (hq : 0 < q)
    (admissible : (MvPolynomial (U ⊕ B) ℝ × MvPolynomial (U ⊕ B) ℝ) → Prop)
    (hsupport : ∀ sr, admissible sr →
      (polynomialSubspaceRestriction K e sr.1).support ⊆ S ∧
      (polynomialSubspaceRestriction K e sr.2).support ⊆ S)
    (hslow : ∀ sr, admissible sr → ∀ α,
      |(polynomialSubspaceRestriction K e sr.1).coeff α| ≤ bound)
    (hrat : ∀ sr, admissible sr → ∀ α,
      ∃ z : ℤ, (polynomialSubspaceRestriction K e sr.2).coeff α = (z : ℝ) / q)
    (hidentity : ∀ sr, admissible sr → ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) P =
        eval (Sum.elim (fun i => u i / H i)
          (fun i => b i - eval u (A i))) sr.1 + eval (Sum.elim u b) sr.2) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m →
        (MvPolynomial (U ⊕ B) ℝ × MvPolynomial (U ⊕ B) ℝ),
        (∀ j, admissible (candidate j)) ∧
        ∀ sr, admissible sr → ∃ j,
          polynomialSubspaceRestriction K e (candidate j).1 =
            polynomialSubspaceRestriction K e sr.1 ∧
          polynomialSubspaceRestriction K e (candidate j).2 =
            polynomialSubspaceRestriction K e sr.2 ∧
          ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
            eval (Sum.elim u b) (candidate j).1 = eval (Sum.elim u b) sr.1 ∧
            eval (Sum.elim u b) (candidate j).2 = eval (Sum.elim u b) sr.2 := by
  let restrict := fun sr : MvPolynomial (U ⊕ B) ℝ × MvPolynomial (U ⊕ B) ℝ =>
    (polynomialSubspaceRestriction K e sr.1, polynomialSubspaceRestriction K e sr.2)
  obtain ⟨n, hn, restricted, _, hcover⟩ :=
    exists_finite_normalized_real_grid_corrections H hH
      (normalizedChartSubspaceCoordinates K e A hA) S
      (polynomialSubspaceRestriction K e P) bound hbound q hq
  have hcoverage : ∀ sr, admissible sr → ∃ i, restricted i = restrict sr := by
    intro sr hsr
    apply hcover
    refine ⟨(hsupport sr hsr).1, (hsupport sr hsr).2, hslow sr hsr, hrat sr hsr, ?_⟩
    exact normalizedChart_subspace_decomposition K e H A hA P sr.1 sr.2
      (hidentity sr hsr)
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_fiber_representatives restrict admissible restricted hcoverage
  refine ⟨m, hm.trans hn, candidate, hvalid, ?_⟩
  intro sr hsr
  obtain ⟨j, hj⟩ := hcomplete sr hsr
  have hleft := congrArg Prod.fst hj
  have hright := congrArg Prod.snd hj
  refine ⟨j, hleft, hright, ?_⟩
  intro u b hb
  exact ⟨polynomialSubspaceRestriction_eval_eq K e _ _ hleft u b hb,
    polynomialSubspaceRestriction_eval_eq K e _ _ hright u b hb⟩

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_vector_subspace_normalized_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (S : Finset ((U ⊕ I) →₀ ℕ)) (bound : ℝ) (hbound : 0 ≤ bound)
    (q : ℕ) (hq : 0 < q)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hsupport : ∀ a, admissible a → ∀ i,
      (polynomialSubspaceRestriction K e (slow a i)).support ⊆ S ∧
      (polynomialSubspaceRestriction K e (rat a i)).support ⊆ S)
    (hslow : ∀ a, admissible a → ∀ i d,
      |(polynomialSubspaceRestriction K e (slow a i)).coeff d| ≤ bound)
    (hrat : ∀ a, admissible a → ∀ i d,
      ∃ z : ℤ, (polynomialSubspaceRestriction K e (rat a i)).coeff d = (z : ℝ) / q)
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    ∃ m : ℕ, m ≤ ((2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  let restrict : α → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun a i => (polynomialSubspaceRestriction K e (slow a i),
      polynomialSubspaceRestriction K e (rat a i))
  choose n hn c _hc hcover using fun i : η =>
    exists_finite_normalized_real_grid_corrections H hH
      (normalizedChartSubspaceCoordinates K e A hA) S
      (polynomialSubspaceRestriction K e (P i)) bound hbound q hq
  let Index := ∀ i : η, Fin (n i)
  let enum : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
  let family : Fin (Fintype.card Index) → η →
      (MvPolynomial (U ⊕ I) ℝ × MvPolynomial (U ⊕ I) ℝ) :=
    fun j i => c i (enum.symm j i)
  have hcoverage : ∀ a, admissible a → ∃ j, family j = restrict a := by
    intro a ha
    have each (i : η) : ∃ j, c i j = restrict a i := by
      apply hcover i
      refine ⟨(hsupport a ha i).1, (hsupport a ha i).2,
        hslow a ha i, hrat a ha i, ?_⟩
      exact normalizedChart_subspace_decomposition K e H A hA (P i)
        (slow a i) (rat a i) (hidentity a ha i)
    choose indices hi using each
    refine ⟨enum indices, ?_⟩
    funext i
    simpa only [family, Equiv.symm_apply_apply] using hi i
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_fiber_representatives restrict admissible family hcoverage
  refine ⟨m, hm.trans ?_, candidate, hvalid, ?_⟩
  · change Fintype.card (∀ i : η, Fin (n i)) ≤ _
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∏ _i : η, (2 * ⌈(q : ℝ) * bound⌉₊ + 3) ^ S.card :=
        Finset.prod_le_prod' (fun i _ => hn i)
      _ = _ := by simp
  · intro a ha
    obtain ⟨j, hj⟩ := hcomplete a ha
    refine ⟨j, fun i => ?_⟩
    have hi := congrFun hj i
    exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I η α : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]

theorem exists_finite_primitive_subspace_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ d, (fun b => (A b).coeff d) ∈ K)
    (P : η → MvPolynomial (U ⊕ B) ℝ)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (slow a i).totalDegree ≤ s ∧ (rat a i).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |(slow a i).coeff ex| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ i, realPolynomialCoefficientGrid q (rat a i))
    (hidentity : ∀ a, admissible a → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval (Sum.elim u b) (P i) =
        eval (Sum.elim (fun j => u j / H j)
          (fun j => b j - eval u (A j))) (slow a i) + eval (Sum.elim u b) (rat a i)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ i,
          polynomialSubspaceRestriction K e (slow (candidate j) i) =
            polynomialSubspaceRestriction K e (slow a i) ∧
          polynomialSubspaceRestriction K e (rat (candidate j) i) =
            polynomialSubspaceRestriction K e (rat a i) := by
  classical
  dsimp only
  let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
    (max 1 ((Fintype.card I : ℝ) * L)) ^ s
  have hRcap : 0 ≤ Rcap := mul_nonneg
    (mul_nonneg (pow_nonneg (by positivity) s) hM)
    (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s)
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_vector_subspace_normalized_correction_representatives
      K e H hH A hA P (boundedExponentWindow (U ⊕ I) s)
      Rcap hRcap (q * d ^ s) (Nat.mul_pos hq (pow_pos hd s))
      slow rat admissible
      (fun a ha i => ⟨support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).1),
        support_subset_boundedExponentWindow _
        ((polynomialSubspaceRestriction_totalDegree_le K e _).trans (hdegree a ha i).2)⟩)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_le K e (slow a i) hM he
        (hdegree a ha i).1 (hcoeff a ha i) ex)
      (fun a ha i ex => polynomialSubspaceRestriction_coeff_div K e (rat a i)
        q d s hq hd hegrid (hdegree a ha i).2 (hgrid a ha i) ex)
      hidentity
  refine ⟨m, hm.trans ?_, candidate, hvalid, hcover⟩
  apply Nat.pow_le_pow_left
  exact Nat.pow_le_pow_right (by omega)
    (boundedExponentWindow_card_le (U ⊕ I) s)

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

theorem exists_uniform_finite_subspace_correction_representatives (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {U B I η α : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]
        (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
        (H : U → ℝ) (_hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ),
        (∀ d, (fun b => (A b).coeff d) ∈ K) →
        ∀ (P : η → MvPolynomial (U ⊕ B) ℝ) (q d : ℕ) (p L M : ℝ),
        0 < q → 0 < d → 0 ≤ p →
        (Fintype.card U : ℝ) ≤ p → (Fintype.card B : ℝ) ≤ p →
        (Fintype.card I : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
        (q : ℝ) ≤ Real.exp ((p + a) ^ a) → (d : ℝ) ≤ Real.exp ((p + a) ^ a) →
        L ≤ Real.exp ((p + a) ^ a) → 0 ≤ M → M ≤ Real.exp ((p + a) ^ a) →
        (∀ i b, |(e i : B → ℝ) b| ≤ L) →
        (∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b) →
        ∀ (slow rat : α → η → MvPolynomial (U ⊕ B) ℝ) (admissible : α → Prop),
        (∀ x, admissible x → ∀ i,
          (slow x i).totalDegree ≤ s ∧ (rat x i).totalDegree ≤ s) →
        (∀ x, admissible x → ∀ i ex, |(slow x i).coeff ex| ≤ M) →
        (∀ x, admissible x → ∀ i, realPolynomialCoefficientGrid q (rat x i)) →
        (∀ x, admissible x → ∀ i (u : U → ℝ) (b : B → ℝ), b ∈ K →
          eval (Sum.elim u b) (P i) =
            eval (Sum.elim (fun j => u j / H j)
              (fun j => b j - eval u (A j))) (slow x i) +
              eval (Sum.elim u b) (rat x i)) →
        ∃ m : ℕ, (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ candidate : Fin m → α,
            (∀ j, admissible (candidate j)) ∧
            ∀ x, admissible x → ∃ j, ∀ i,
              polynomialSubspaceRestriction K e (slow (candidate j) i) =
                polynomialSubspaceRestriction K e (slow x i) ∧
              polynomialSubspaceRestriction K e (rat (candidate j) i) =
                polynomialSubspaceRestriction K e (rat x i) := by
  obtain ⟨C, hC, hbudget⟩ := exists_finite_primitive_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro U B I η α _ _ _ _ K e H hH A hA P q d p L M hq hd hp
    hU hB hI hη hqCap hdCap hLCap hM hMCap he hegrid
    slow rat admissible hdegree hcoeff hgrid hidentity
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_primitive_subspace_correction_representatives
      K e H hH A hA P s q d hq hd L M hM he hegrid
      slow rat admissible hdegree hcoeff hgrid hidentity
  refine ⟨m, (Nat.cast_le.mpr hm).trans ?_, candidate, hvalid, hcover⟩
  simpa only [Fintype.card_sum] using
    hbudget (Fintype.card U) (Fintype.card B) (Fintype.card I) (Fintype.card η)
      q d p L M hp hU hB hI hη hqCap hdCap hLCap hM hMCap

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators

variable {U B I η α V : Type*} [Fintype U] [Fintype B] [Fintype I] [Fintype η]
  [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

omit [Fintype U] [Fintype B] [Fintype η] [IsScalarTower ℚ ℝ V] in
private theorem coordinate_grid_of_vector_grid (basis : Basis η ℝ V)
    (q : ℕ) (P : VectorPolynomial (U ⊕ B) ℚ V)
    (h : ∀ ex, (fun i => basis.coord i (coefficients P ex)) ∈ realDenominatorGrid q)
    (i : η) : realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom P) := by
  classical
  choose z hz using h
  refine ⟨fun ex => z ex i, funext fun ex => ?_⟩
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe, Pi.smul_apply, smul_eq_mul]
    using congrFun (hz ex) i

theorem exists_finite_vector_correction_representatives
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K) (basis : Basis η ℝ V)
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : B → MvPolynomial U ℝ)
    (hA : ∀ ex, (fun b => (A b).coeff ex) ∈ K)
    (P : VectorPolynomial (U ⊕ B) ℚ V)
    (s q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (L M : ℝ) (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L)
    (hegrid : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (slow rat : α → VectorPolynomial (U ⊕ B) ℚ V) (admissible : α → Prop)
    (hdegree : ∀ a, admissible a → ∀ i,
      (coordinate (basis.coord i).toAddMonoidHom (slow a)).totalDegree ≤ s ∧
      (coordinate (basis.coord i).toAddMonoidHom (rat a)).totalDegree ≤ s)
    (hcoeff : ∀ a, admissible a → ∀ i ex, |basis.coord i (coefficients (slow a) ex)| ≤ M)
    (hgrid : ∀ a, admissible a → ∀ ex,
      (fun i => basis.coord i (coefficients (rat a) ex)) ∈ realDenominatorGrid q)
    (hidentity : ∀ a, admissible a → ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
      eval₂ (Sum.elim u b) P =
        eval₂ (Sum.elim u b) (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) +
        eval₂ (Sum.elim u b) (rat a)) :
    let Rcap := (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
      (max 1 ((Fintype.card I : ℝ) * L)) ^ s
    ∃ m : ℕ,
      m ≤ ((2 * ⌈((q * d ^ s : ℕ) : ℝ) * Rcap⌉₊ + 3) ^
        ((Fintype.card (U ⊕ I) + 1) ^ s)) ^ Fintype.card η ∧
      ∃ candidate : Fin m → α,
        (∀ j, admissible (candidate j)) ∧
        ∀ a, admissible a → ∃ j, ∀ (u : U → ℝ) (b : B → ℝ), b ∈ K →
          eval₂ (Sum.elim u b) (slow (candidate j)) = eval₂ (Sum.elim u b) (slow a) ∧
          eval₂ (Sum.elim u b) (rat (candidate j)) = eval₂ (Sum.elim u b) (rat a) ∧
          eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow (candidate j))) =
            eval₂ (Sum.elim u b)
              (realChartSubstitute (normalizedRealPolynomialChart H A) (slow a)) := by
  let scalar := fun (p : VectorPolynomial (U ⊕ B) ℚ V) i =>
    coordinate (basis.coord i).toAddMonoidHom p
  obtain ⟨m, hm, candidate, hvalid, hcover⟩ :=
    exists_finite_primitive_subspace_correction_representatives K e H hH A hA
      (scalar P) s q d hq hd L M hM he hegrid
      (fun a => scalar (slow a)) (fun a => scalar (rat a)) admissible hdegree
      (fun a ha i ex => by simpa only [scalar, coeff_coordinate,
        LinearMap.toAddMonoidHom_coe] using hcoeff a ha i ex)
      (fun a ha i => coordinate_grid_of_vector_grid basis q (rat a) (hgrid a ha) i)
      (by
        intro a ha i u b hb
        have h := congrArg (basis.coord i) (hidentity a ha u b hb)
        rw [eval₂_normalizedRealPolynomialChart] at h
        simpa only [map_add, coordinate_eval₂] using h)
  refine ⟨m, hm, candidate, hvalid, ?_⟩
  intro a ha
  obtain ⟨j, hj⟩ := hcover a ha
  have heval (t : α → VectorPolynomial (U ⊕ B) ℚ V)
      (ht : ∀ i, polynomialSubspaceRestriction K e (scalar (t (candidate j)) i) =
        polynomialSubspaceRestriction K e (scalar (t a) i))
      (u : U → ℝ) (b : B → ℝ) (hb : b ∈ K) :
      eval₂ (Sum.elim u b) (t (candidate j)) = eval₂ (Sum.elim u b) (t a) := by
    apply basis.repr.injective
    ext i
    change basis.coord i _ = basis.coord i _
    rw [coordinate_eval₂, coordinate_eval₂]
    exact polynomialSubspaceRestriction_eval_eq K e _ _ (ht i) u b hb
  refine ⟨j, ?_⟩
  intro u b hb
  refine ⟨heval slow (fun i => (hj i).1) u b hb,
    heval rat (fun i => (hj i).2) u b hb, ?_⟩
  rw [eval₂_normalizedRealPolynomialChart, eval₂_normalizedRealPolynomialChart]
  exact heval slow (fun i => (hj i).1) _ _
    (K.sub_mem hb (normalizedChartSubspaceCoordinates_eval_mem K A hA u))

end Erdos3.VectorPolynomial

end

end OAI

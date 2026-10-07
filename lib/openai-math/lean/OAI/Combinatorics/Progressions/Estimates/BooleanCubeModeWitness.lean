/- Modified for ProveIt: import Lean 4.32 compatibility declarations and
simplify polynomial coefficient addition explicitly. Statements unchanged. -/
import OAI.Compat.Core
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficient {α R : Type*} [DecidableEq α] [CommRing R]
    (f : Finset α → R) (s : Finset α) : R :=
  ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card * f t

theorem sum_powerset_neg_one_pow_card_ring {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : (∑ t ∈ s.powerset, (-1 : R) ^ t.card) = if s = ∅ then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (Finset.sum_powerset_neg_one_pow_card (x := s))
  simpa only [map_sum, map_pow, map_neg, map_one, map_zero, apply_ite] using h

theorem boolean_interval_alternating_sum {α R : Type*} [DecidableEq α] [CommRing R]
    (s r : Finset α) (hrs : r ⊆ s) :
    (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) = if s = r then 1 else 0 := by
  classical
  have hsum : (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) =
      ∑ u ∈ (s \ r).powerset, (-1 : R) ^ u.card := by
    refine Finset.sum_bij (fun t _ => s \ t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      rw [Finset.mem_powerset]
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨has, hat⟩
      exact Finset.mem_sdiff.mpr ⟨has, fun har => hat (hrt har)⟩
    · intro t ht u hu heq
      have ht' := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
      have hu' := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
      have h := congrArg (fun v => s \ v) heq
      simpa only [Finset.sdiff_sdiff_eq_self ht', Finset.sdiff_sdiff_eq_self hu'] using h
    · intro u hu
      have hu' := Finset.mem_powerset.mp hu
      refine ⟨s \ u, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
        intro a har
        apply Finset.mem_sdiff.mpr
        refine ⟨hrs har, ?_⟩
        intro hau
        exact (Finset.mem_sdiff.mp (hu' hau)).2 har
      · exact Finset.sdiff_sdiff_eq_self (hu'.trans Finset.sdiff_subset)
    · intro t _
      rfl
  rw [hsum, sum_powerset_neg_one_pow_card_ring]
  by_cases h : s = r
  · subst s
    simp
  · have hne : s \ r ≠ ∅ := by
      intro hempty
      exact h ((Finset.sdiff_eq_empty_iff_subset.mp hempty).antisymm hrs)
    simp only [hne, h, ite_false]

theorem booleanCoefficient_monomial {α R : Type*} [DecidableEq α] [CommRing R]
    (r s : Finset α) :
    booleanCoefficient (fun t => if r ⊆ t then (1 : R) else 0) s = if s = r then 1 else 0 := by
  classical
  unfold booleanCoefficient
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  by_cases hrs : r ⊆ s
  · exact boolean_interval_alternating_sum (R := R) s r hrs
  · have hfilter : {t ∈ s.powerset | r ⊆ t} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      exact hrs (hrt.trans (Finset.mem_powerset.mp hts))
    have hne : s ≠ r := fun h => hrs (h.symm ▸ Finset.Subset.refl r)
    simp only [hfilter, Finset.sum_empty, hne, ite_false]

theorem booleanCoefficient_sum {α R B : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (b : Finset B) (f : B → Finset α → R) :
    booleanCoefficient (fun t => ∑ i ∈ b, f i t) s =
      ∑ i ∈ b, booleanCoefficient (f i) s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  exact Finset.sum_comm

theorem booleanCoefficient_const_mul {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (c : R) (f : Finset α → R) :
    booleanCoefficient (fun t => c * f t) s = c * booleanCoefficient f s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_add {α R : Type*} [DecidableEq α] [CommRing R]
    (f g : Finset α → R) (s : Finset α) :
    booleanCoefficient (fun t => f t + g t) s = booleanCoefficient f s + booleanCoefficient g s := by
  simp only [booleanCoefficient, mul_add, Finset.sum_add_distrib]

theorem booleanCoefficient_const {α R : Type*} [DecidableEq α] [CommRing R]
    (c : R) (s : Finset α) : booleanCoefficient (fun _ => c) s = if s = ∅ then c else 0 := by
  have h1 := booleanCoefficient_monomial (R := R) ∅ s
  simp only [Finset.empty_subset, ite_true] at h1
  have hc := booleanCoefficient_const_mul s c (fun _ => (1 : R))
  simpa only [mul_one, h1, mul_ite, mul_zero] using hc

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

abbrev Variable (α β : Type*) := Option (α ⊕ β)

inductive Form (α β : Type*) where
  | coordinate : Variable α β → Form α β
  | difference : α → Form α β

noncomputable def site {α β R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : Variable α β → R
  | none => 1
  | some (.inl i) => if i ∈ s then 1 else 0
  | some (.inr _) => 0

noncomputable def formPolynomial {α β R : Type*} [CommRing R] :
    Form α β → MvPolynomial (Variable α β) R
  | .coordinate v => X v
  | .difference i => X (some (.inl i)) - X none

noncomputable def formProduct {α β R : Type*} [CommRing R]
    (l : List (Form α β)) : MvPolynomial (Variable α β) R :=
  (l.map formPolynomial).prod

theorem formProduct_nil {α β R : Type*} [CommRing R] :
    formProduct (R := R) ([] : List (Form α β)) = 1 := rfl

theorem formProduct_cons {α β R : Type*} [CommRing R]
    (f : Form α β) (l : List (Form α β)) :
    formProduct (R := R) (f :: l) = formPolynomial f * formProduct l := rfl

theorem formPolynomial_homogeneous {α β R : Type*} [CommRing R] (f : Form α β) :
    (formPolynomial (R := R) f).IsHomogeneous 1 := by
  cases f with
  | coordinate v => exact isHomogeneous_X R v
  | difference i => exact (isHomogeneous_X R _).sub (isHomogeneous_X R _)

theorem formProduct_homogeneous {α β R : Type*} [CommRing R] (l : List (Form α β)) :
    (formProduct (R := R) l).IsHomogeneous l.length := by
  induction l with
  | nil => exact isHomogeneous_one (Variable α β) R
  | cons f l ih =>
    simpa only [formProduct_cons, List.length_cons, Nat.add_comm] using
      (formPolynomial_homogeneous f).mul ih

noncomputable def vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ l : List (Form α β), l.length = h ∧
    (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ P = formProduct l}

theorem formProduct_mem_vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (l : List (Form α β)) (hz : ∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) :
    formProduct (R := R) l ∈ vanishingSpan l.length :=
  Submodule.subset_span ⟨l, rfl, hz, rfl⟩

theorem vanishingSpan_eval_zero {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (s : Finset α) :
    eval (site s) P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP => obtain ⟨l, _, hz, rfl⟩ := hP; exact hz s
  | zero => simp
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [smul_eq_C_mul, map_mul, eval_C, hP, mul_zero]

theorem vanishingSpan_mul_form {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (f : Form α β) :
    formPolynomial f * P ∈ vanishingSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    have he : (f :: l).length = h + 1 := by simp [hl]
    rw [← formProduct_cons, ← he]
    apply formProduct_mem_vanishingSpan
    intro s
    rw [formProduct_cons, map_mul, hz, mul_zero]
  | zero => simpa only [mul_zero] using (vanishingSpan (h + 1)).zero_mem
  | add P Q _ _ hP hQ =>
    simpa only [mul_add] using (vanishingSpan (h + 1)).add_mem hP hQ
  | smul a P _ hP =>
    simpa only [mul_smul_comm] using (vanishingSpan (h + 1)).smul_mem a hP

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

noncomputable def booleanSiteJets {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (x : Finset α → D → ℝ) : (Σ d, O d) → ℝ :=
  fun o => booleanCoefficient (fun s => x s o.1) (sets o.1 o.2)

theorem booleanSiteJets_lipschitz {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {O : D → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α) :
    LipschitzWith ((2 : ℝ≥0)^Fintype.card α) (booleanSiteJets sets) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro o
  change |booleanCoefficient (fun s => x s o.1) (sets o.1 o.2)-
    booleanCoefficient (fun s => y s o.1) (sets o.1 o.2)| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s o.1-y s o.1| ≤ dist (x s) (y s) from dist_le_pi_dist (x s) (y s) o.1).trans
      (dist_le_pi_dist x y s)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

noncomputable def normalMonomial (h : ℕ) (s : Finset α) : MvPolynomial (Variable α β) R :=
  X none ^ (h - s.card) * ∏ i ∈ s, X (some (.inl i))

noncomputable def normalWord (h : ℕ) (s : Finset α) : List (Form α β) :=
  List.replicate (h - s.card) (.coordinate none) ++ s.toList.map (fun i => .coordinate (some (.inl i)))

omit [DecidableEq α] in
theorem normalWord_length (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    (normalWord (β := β) h s).length = h := by
  simp only [normalWord, List.length_append, List.length_replicate, List.length_map,
    Finset.length_toList, Nat.sub_add_cancel hs]

omit [DecidableEq α] in
theorem normalWord_product (h : ℕ) (s : Finset α) :
    formProduct (R := R) (normalWord (β := β) h s) = normalMonomial h s := by
  simp only [normalWord, formProduct, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate, List.map_map]
  rw [Finset.prod_map_toList]
  rfl

theorem normalMonomial_eval (h : ℕ) (s t : Finset α) :
    eval (site (β := β) t) (normalMonomial (R := R) h s) = if s ⊆ t then 1 else 0 := by
  simp only [normalMonomial, map_mul, map_pow, eval_X, site, one_pow, one_mul, map_prod]
  by_cases hst : s ⊆ t
  · rw [ite_eq_left hst]
    exact Finset.prod_eq_one (fun i hi => by simp [hst hi])
  · rw [ite_eq_right hst]
    obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hst
    exact Finset.prod_eq_zero his (by simp [hit])

theorem normalMonomial_jet (h : ℕ) (s t : Finset α) :
    booleanCoefficient (fun u => eval (site (β := β) u) (normalMonomial (R := R) h s)) t =
      if t = s then 1 else 0 := by
  simp_rw [normalMonomial_eval]
  exact booleanCoefficient_monomial s t

omit [DecidableEq α] in
theorem normalMonomial_homogeneous (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    (normalMonomial (β := β) (R := R) h s).IsHomogeneous h := by
  have hp := formProduct_homogeneous (R := R) (normalWord (β := β) h s)
  simpa only [normalWord_product, normalWord_length h s hs] using hp

noncomputable def normalSpan (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ s : Finset α, s.card ≤ h ∧ P = normalMonomial h s}

omit [DecidableEq α] in
theorem normalMonomial_mem (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    normalMonomial (β := β) (R := R) h s ∈ normalSpan h :=
  Submodule.subset_span ⟨s, hs, rfl⟩

omit [DecidableEq α] in
theorem normalMonomial_mul_root (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    X none * normalMonomial (β := β) (R := R) h s = normalMonomial (h + 1) s := by
  have he : h + 1 - s.card = (h - s.card) + 1 := by omega
  simp only [normalMonomial, he, pow_succ]
  ring

theorem normalMonomial_mul_new (h : ℕ) (s : Finset α) (i : α) (hi : i ∉ s) :
    X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
      normalMonomial (h + 1) (insert i s) := by
  simp only [normalMonomial, Finset.card_insert_of_notMem hi, Nat.add_sub_add_right,
    Finset.prod_insert hi]
  ring

theorem normalMonomial_mul_coordinate (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (v : Variable α β) :
    X v * normalMonomial (R := R) h s ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  cases v with
  | none =>
    rw [normalMonomial_mul_root h s hs]
    exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by omega))
  | some v =>
    cases v with
    | inl i =>
      by_cases hi : i ∈ s
      · have hz : (X (some (.inl i)) - X none) * normalMonomial (β := β) (R := R) h s ∈
            vanishingSpan (h + 1) := by
          have he : (Form.difference i :: normalWord (β := β) h s).length = h + 1 := by
            simp only [List.length_cons, normalWord_length h s hs]
          rw [← he, ← normalWord_product h s]
          change formProduct (R := R) (Form.difference i :: normalWord h s) ∈ _
          apply formProduct_mem_vanishingSpan
          intro t
          rw [formProduct_cons, normalWord_product, map_mul, normalMonomial_eval]
          by_cases hst : s ⊆ t
          · simp [formPolynomial, site, hst, hst hi]
          · simp [hst]
        have hn := normalMonomial_mem (β := β) (R := R) (h + 1) s (by omega)
        rw [← normalMonomial_mul_root h s hs] at hn
        have he : X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
            (X (some (.inl i)) - X none) * normalMonomial h s +
              X none * normalMonomial h s := by ring
        rw [he]
        exact Submodule.add_mem_sup hz hn
      · rw [normalMonomial_mul_new h s i hi]
        exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by
          rw [Finset.card_insert_of_notMem hi]; omega))
    | inr j =>
      apply Submodule.mem_sup_left
      have he : (Form.coordinate (some (.inr j)) :: normalWord (β := β) h s).length = h + 1 := by
        simp only [List.length_cons, normalWord_length h s hs]
      rw [← he, ← normalWord_product h s]
      change formProduct (R := R) (Form.coordinate (some (.inr j)) :: normalWord h s) ∈ _
      apply formProduct_mem_vanishingSpan
      intro t
      simp only [formProduct_cons, map_mul, formPolynomial, eval_X, site, zero_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def polynomialLinearRow {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i : σ) : R := P.coeff (Finsupp.single i 1)

noncomputable def rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (a : σ → R) : MvPolynomial σ R := ∑ i, C (a i) * X i

theorem homogeneous_eq_rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) :
    P = rowPolynomial (polynomialLinearRow P) := by
  have hp : P ∈ Submodule.span R (Set.range (X : σ → MvPolynomial σ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hP
  clear hP
  induction hp using Submodule.span_induction with
  | mem P hp =>
    obtain ⟨v, rfl⟩ := hp
    have hs (i : σ) : (Finsupp.single v 1 : σ →₀ ℕ) = Finsupp.single i 1 ↔ v = i :=
      (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)).eq_iff
    simp only [rowPolynomial, polynomialLinearRow, coeff_X, hs, apply_ite, map_one,
      map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | zero => simp [rowPolynomial, polynomialLinearRow]
  | add P Q _ _ hP hQ =>
    simpa only [rowPolynomial, polynomialLinearRow, MvPolynomial.coeff_add,
      Finsupp.add_apply, map_add, add_mul,
      Finset.sum_add_distrib] using congrArg₂ (fun a b => a + b) hP hQ
  | smul a P _ hP =>
    simpa only [rowPolynomial, polynomialLinearRow, coeff_smul, coeff_C_mul, smul_eq_mul, map_mul,
      smul_eq_C_mul, Finset.mul_sum, mul_assoc] using congrArg (fun Q => a • Q) hP

theorem rowPolynomial_eval {σ R : Type*} [Fintype σ] [CommRing R] (a x : σ → R) :
    eval x (rowPolynomial a) = ∑ i, a i * x i := by
  simp only [rowPolynomial, map_sum, map_mul, eval_C, eval_X]

theorem homogeneous_eval_eq_row {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) (x : σ → R) :
    eval x P = ∑ i, polynomialLinearRow P i * x i := by
  conv_lhs => rw [homogeneous_eq_rowPolynomial P hP]
  rw [rowPolynomial_eval]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

theorem normalSpan_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact normalMonomial_mul_coordinate h s hs v
  | zero => simp only [mul_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [mul_add]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ a hP

theorem reductionSpace_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hP
  rw [mul_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (vanishingSpan_mul_form hA (.coordinate v)))
    (normalSpan_mul_coordinate hB v)

theorem reductionSpace_mul_linear {h : ℕ} {P L : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (hL : L.IsHomogeneous 1) :
    L * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  have hL' : L ∈ Submodule.span R (Set.range (X : Variable α β → MvPolynomial _ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  clear hL
  induction hL' using Submodule.span_induction with
  | mem L hL =>
    obtain ⟨v, rfl⟩ := hL
    exact reductionSpace_mul_coordinate hP v
  | zero => simp only [zero_mul]; exact Submodule.zero_mem _
  | add A B _ _ hA hB =>
    rw [add_mul]
    exact Submodule.add_mem _ hA hB
  | smul a L _ hL =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a hL

theorem homogeneous_mem_reductionSpace {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P ∈ vanishingSpan h ⊔ normalSpan h := by
  induction h generalizing P with
  | zero =>
    have hp : P ∈ (1 : Submodule R (MvPolynomial (Variable α β) R)) := by
      rw [← homogeneousSubmodule_zero]
      exact hP
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hp
    apply Submodule.mem_sup_right
    have hone := normalMonomial_mem (β := β) (R := R) 0 (∅ : Finset α) (by simp)
    have hc := (normalSpan (α := α) (β := β) (R := R) 0).smul_mem a hone
    simpa only [normalMonomial, Finset.card_empty, Nat.sub_self, pow_zero, Finset.prod_empty,
      mul_one, smul_eq_C_mul, algebraMap_eq] using hc
  | succ h ih =>
    have hp : P ∈ homogeneousSubmodule (Variable α β) R 1 *
        homogeneousSubmodule (Variable α β) R h := by
      rw [← homogeneousSubmodule_one_pow (σ := Variable α β) R h, ← pow_succ',
        homogeneousSubmodule_one_pow (σ := Variable α β) R (h + 1)]
      exact hP
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro L hL Q hQ
      exact reductionSpace_mul_linear (ih hQ) hL
    · intro A B hA hB
      exact Submodule.add_mem _ hA hB

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def siteEvaluation :
    MvPolynomial (Variable α β) R →ₗ[R] (Finset α → R) where
  toFun P s := eval (site s) P
  map_add' P Q := by ext s; exact map_add _ _ _
  map_smul' a P := by ext s; exact smul_eval _ _ _

noncomputable def coefficientLinear (s : Finset α) : (Finset α → R) →ₗ[R] R where
  toFun f := booleanCoefficient f s
  map_add' f g := booleanCoefficient_add f g s
  map_smul' a f := booleanCoefficient_const_mul s a f

noncomputable def interpolation (h : ℕ) : (Finset α → R) →ₗ[R] MvPolynomial (Variable α β) R :=
  ∑ s : Finset α, if s.card ≤ h then (coefficientLinear s).smulRight (normalMonomial h s) else 0

theorem interpolation_apply (h : ℕ) (f : Finset α → R) :
    interpolation (β := β) h f =
      ∑ s : Finset α, if s.card ≤ h then booleanCoefficient f s • normalMonomial h s else 0 := by
  simp only [interpolation, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.card ≤ h
  · simp only [hs, ite_true, LinearMap.smulRight_apply]
    rfl
  · simp only [hs, ite_false, LinearMap.zero_apply]

theorem interpolation_normalMonomial (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    interpolation (β := β) h (siteEvaluation (normalMonomial (β := β) (R := R) h s)) =
      normalMonomial h s := by
  rw [interpolation_apply]
  change (∑ t : Finset α, if t.card ≤ h then
    booleanCoefficient (fun u => eval (site u) (normalMonomial (β := β) (R := R) h s)) t •
      normalMonomial h t else 0) = _
  simp_rw [normalMonomial_jet]
  rw [Finset.sum_eq_single s]
  · simp only [hs, ite_true, one_smul]
  · intro t _ ht
    simp only [ht, ite_false, zero_smul, ite_self]
  · simp

theorem interpolation_eq_of_mem_normalSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) : interpolation h (siteEvaluation P) = P := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact interpolation_normalMonomial h s hs
  | zero => simp only [map_zero]
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ]
  | smul a P _ hP => simp only [map_smul, hP]

theorem normalSpan_eq_zero_of_eval_zero {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) (hz : ∀ s : Finset α, eval (site s) P = 0) : P = 0 := by
  have he : siteEvaluation P = 0 := by ext s; exact hz s
  rw [← interpolation_eq_of_mem_normalSpan hP, he, map_zero]

theorem homogeneous_vanishing_mem_span {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) (hz : ∀ s : Finset α, eval (site s) P = 0) :
    P ∈ vanishingSpan h := by
  obtain ⟨A, hA, B, hB, he⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  have hb : B = 0 := normalSpan_eq_zero_of_eval_zero hB (by
    intro s
    have hp := hz s
    rw [← he, map_add, vanishingSpan_eval_zero hA s, zero_add] at hp
    exact hp)
  rw [hb, add_zero] at he
  exact he ▸ hA

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

theorem remainder_mem_vanishingSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P - interpolation h (siteEvaluation P) ∈ vanishingSpan h := by
  obtain ⟨A, hA, B, hB, he⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  have hEA : siteEvaluation A = 0 := by ext s; exact vanishingSpan_eval_zero hA s
  rw [← he, map_add, hEA, zero_add, interpolation_eq_of_mem_normalSpan hB, add_sub_cancel_right]
  exact hA

omit [Fintype α] in
theorem map_vanishingSpan_eq_zero (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) {h : ℕ}
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) : Λ P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    exact hkill l hl hz
  | zero => exact map_zero Λ
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [map_smul, hP, smul_zero]

theorem factor_through_sites_of_kills_products
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h) :
    Λ P = (Λ.comp (interpolation h)) (siteEvaluation P) := by
  have hz := map_vanishingSpan_eq_zero Λ hkill (remainder_mem_vanishingSpan hP)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem exists_vanishing_product_of_nonfactor
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (siteEvaluation P)) :
    ∃ l : List (Form α β), l.length = h ∧
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ Λ (formProduct l) ≠ 0 := by
  by_contra hnone
  apply hnonfactor
  refine ⟨Λ.comp (interpolation h), fun P hP => factor_through_sites_of_kills_products Λ h ?_ hP⟩
  intro l hl hz
  by_contra hne
  exact hnone ⟨l, hl, hz, hne⟩

theorem exists_vector_vanishing_product {W : Type*} [AddCommGroup W] [Module R W]
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] (W →ₗ[R] R)) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] (W →ₗ[R] R),
      ∀ P, P.IsHomogeneous h → Λ P = L (siteEvaluation P)) :
    ∃ l : List (Form α β), l.length = h ∧
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧
      ∃ w : W, Λ (formProduct l) w ≠ 0 := by
  obtain ⟨l, hl, hz, hΛ⟩ := exists_vanishing_product_of_nonfactor Λ h hnonfactor
  refine ⟨l, hl, hz, ?_⟩
  by_contra hnone
  apply hΛ
  ext w
  by_contra hw
  exact hnone ⟨w, hw⟩

end Erdos3.BooleanCubeKernel

end

end OAI

import GowersSzemeredi.Proofs16LinearSampleFibres

/-! Signed subsums hit a small set for few sample tuples. The same count
bounds collisions between Boolean subsums, a required input to Claim 6.3's
sampling argument. No probability library is needed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def ternarySampleCoefficient {N : Nat} (i : Fin 3) : ZMod N :=
  if i = 0 then 0 else if i = 1 then 1 else -1

def nonzeroTernaryCoefficients (N r : Nat) : Finset (Fin r → ZMod N) :=
  (Finset.univ.image (fun s : Fin r → Fin 3 => fun i => ternarySampleCoefficient (s i))).filter
    (fun c => c ≠ 0)

theorem nonzeroTernaryCoefficients_card_le (N r : Nat) :
    (nonzeroTernaryCoefficients N r).card ≤ 3^r := by
  apply (Finset.card_filter_le _ _).trans
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin r → Fin 3)))
    (f := fun s i => ternarySampleCoefficient (N := N) (s i))
  simpa using h

theorem nonzeroTernaryCoefficients_nonzero {N r : Nat}
    {c : Fin r → ZMod N} (hc : c ∈ nonzeroTernaryCoefficients N r) : ∃ j, c j ≠ 0 := by
  have hn := (Finset.mem_filter.mp hc).2
  by_contra! h
  apply hn
  funext j
  exact h j

def ternarySamplesMeeting {N r : Nat} [NeZero N] (Z : Finset (ZMod N)) : Finset (Fin r → ZMod N) :=
  Finset.univ.filter fun e => ∃ c ∈ nonzeroTernaryCoefficients N r, linearSampleValue c e ∈ Z

theorem ternary_samples_meeting_card_le {N r : Nat} [NeZero N] [Fact N.Prime]
    (Z : Finset (ZMod N)) : (ternarySamplesMeeting (r := r) Z).card ≤ 3^r*Z.card*N^(r-1) := by
  have h := linear_samples_union_card_le (nonzeroTernaryCoefficients N r) Z
    (fun _ hc => nonzeroTernaryCoefficients_nonzero hc)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (nonzeroTernaryCoefficients_card_le N r)))

def booleanSampleValue {N r : Nat} (e : Fin r → ZMod N) (s : Fin r → Bool) : ZMod N :=
  ∑ i, (if s i then (1 : ZMod N) else 0)*e i

def booleanDifferenceLabels {r : Nat} (s t : Fin r → Bool) : Fin r → Fin 3 :=
  fun i => match s i, t i with
    | true, false => 1
    | false, true => 2
    | _, _ => 0

theorem boolean_difference_sample_value {N r : Nat} (e : Fin r → ZMod N)
    (s t : Fin r → Bool) :
    linearSampleValue (fun i => ternarySampleCoefficient (booleanDifferenceLabels s t i)) e =
      booleanSampleValue e s-booleanSampleValue e t := by
  unfold linearSampleValue booleanSampleValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hs : s i <;> cases ht : t i <;>
    simp [booleanDifferenceLabels, ternarySampleCoefficient, hs, ht]

theorem boolean_difference_coefficients_mem {N r : Nat} [NeZero N] [Fact N.Prime]
    (s t : Fin r → Bool) (hst : s ≠ t) :
    (fun i => ternarySampleCoefficient (N := N) (booleanDifferenceLabels s t i)) ∈
      nonzeroTernaryCoefficients N r := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨booleanDifferenceLabels s t, Finset.mem_univ _, rfl⟩, ?_⟩
  intro heq
  apply hst
  funext i
  have h := congrFun heq i
  cases hs : s i <;> cases ht : t i <;>
    simp [booleanDifferenceLabels, ternarySampleCoefficient, hs, ht] at h ⊢

/-- At most `3^r*N^(r-1)` samples have colliding Boolean subsums. -/
theorem boolean_sample_collisions_card_le {N r : Nat} [NeZero N] [Fact N.Prime] :
    (Finset.univ.filter fun e : Fin r → ZMod N => ¬ Function.Injective (booleanSampleValue e)).card ≤
      3^r*N^(r-1) := by
  have hsub : (Finset.univ.filter fun e : Fin r → ZMod N =>
      ¬ Function.Injective (booleanSampleValue e)) ⊆ ternarySamplesMeeting (r := r) {0} := by
    intro e he
    have hn := (Finset.mem_filter.mp he).2
    simp only [Function.Injective] at hn
    push Not at hn
    obtain ⟨s, t, hvalue, hst⟩ := hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (fun i => ternarySampleCoefficient (booleanDifferenceLabels s t i)),
      boolean_difference_coefficients_mem s t hst, ?_⟩
    rw [boolean_difference_sample_value, hvalue, sub_self]
    exact Finset.mem_singleton_self 0
  have h := (Finset.card_le_card hsub).trans (ternary_samples_meeting_card_le (r := r) {0})
  simpa using h

end LeanProofs.GowersSzemeredi

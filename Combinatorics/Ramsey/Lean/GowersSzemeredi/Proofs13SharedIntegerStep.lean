import GowersSzemeredi.Proofs13NaturalSquareAxes

/-! Separate integer representatives and equal modular steps do not imply
one common integer step. This is a counterexample to that implication, not
to Theorem13.12, whose stronger natural-axis certificate is proved separately. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def SharedNaturalRepresentatives {N : Nat} (P Q : ModAP N) : Prop :=
  ∃ A B : NatAP, A.IsProper ∧ B.IsProper ∧ A.step = B.step ∧
    A.length = P.length ∧ B.length = Q.length ∧
    A.carrier ⊆ Finset.range N ∧ B.carrier ⊆ Finset.range N ∧
    (A.toModAP N).carrier = P.carrier ∧ (B.toModAP N).carrier = Q.carrier

private theorem canonical_nat_axis {N : Nat} [NeZero N]
    (P : NatAP) (hP : P.carrier ⊆ Finset.range N) :
    (P.toModAP N).carrier.image ZMod.val = P.carrier := by
  classical
  rw [NatAP.toModAP_carrier, Finset.image_image]
  calc
    _ = P.carrier.image id := by
      apply Finset.image_congr
      intro x hx
      exact ZMod.val_natCast_of_lt (Finset.mem_range.mp (hP hx))
    _ = P.carrier := Finset.image_id

private theorem two_point_nat_step (P : NatAP) (c : Nat)
    (hP : P.IsProper) (hlen : P.length = 2) (hcarrier : P.carrier = {0, c}) :
    P.step = c := by
  classical
  have h0 : P.start ∈ P.carrier := Finset.mem_image.mpr
    ⟨⟨0, by omega⟩, Finset.mem_univ _, by simp⟩
  have h1 : P.start + P.step ∈ P.carrier := Finset.mem_image.mpr
    ⟨⟨1, by omega⟩, Finset.mem_univ _, by simp⟩
  rw [hcarrier] at h0 h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
  have hp := hP.1
  omega

/-- The two representative sets are `{0,3}` and `{0,4}` modulo7.
Both modular parameterizations have step3, but their ordinary steps differ. -/
theorem equal_modular_steps_separate_integer_axes_counterexample :
    ∃ P Q : ModAP 7, P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
      Q.HasIntegerRepresentatives ∧ ¬ SharedNaturalRepresentatives P Q := by
  classical
  let P : ModAP 7 := ⟨0, 3, 2⟩
  let Q : ModAP 7 := ⟨4, 3, 2⟩
  have hP : P.HasIntegerRepresentatives := by
    exact (⟨0, 3, 2⟩ : NatAP).toModAP_hasIntegerRepresentatives_of_bound
      (by norm_num) (by intro i hi; change i < 2 at hi; change 0 + i * 3 < 7; omega)
  have hQ : Q.HasIntegerRepresentatives := by
    have h := (⟨0, 4, 2⟩ : NatAP).toModAP_hasIntegerRepresentatives_of_bound (N := 7)
      (by norm_num) (by intro i hi; change i < 2 at hi; change 0 + i * 4 < 7; omega)
    obtain ⟨A, hA, hl, hN, hcar⟩ := h
    refine ⟨A, hA, hl, hN, hcar.trans ?_⟩
    decide
  refine ⟨P, Q, rfl, hP, hQ, ?_⟩
  rintro ⟨A, B, hA, hB, hs, hAl, hBl, hAN, hBN, hAc, hBc⟩
  have hAcar : A.carrier = {0, 3} := by
    rw [← canonical_nat_axis A hAN, hAc]
    decide
  have hBcar : B.carrier = {0, 4} := by
    rw [← canonical_nat_axis B hBN, hBc]
    decide
  have ha := two_point_nat_step A 3 hA hAl hAcar
  have hb := two_point_nat_step B 4 hB hBl hBcar
  omega

end LeanProofs.GowersSzemeredi

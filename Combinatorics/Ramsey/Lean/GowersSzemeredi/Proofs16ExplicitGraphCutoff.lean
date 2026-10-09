import GowersSzemeredi.Proofs16TupleBohrQuasirandom

/-! Explicit parameters for turning sparse bounded relations into a small
box norm. The cutoff and modulus threshold depend only on epsilon, the
cell count, and a bound on the number of frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def relationProfileSmoothing (epsilon : Real) (Q m : Nat) : Real :=
  epsilon / (2880 * (m + 1 : Real) * (Q : Real)^m)

def relationProfileCutoff (epsilon : Real) (Q m : Nat) : Nat :=
  ⌈1 / (relationProfileSmoothing epsilon Q m)^2⌉₊

/-- The explicit smoothing scale pays for both the size and box-error budgets. -/
theorem relationProfileSmoothing_budget {epsilon : Real} (heps : 0 < epsilon)
    (hepsOne : epsilon ≤ 1) (Q m : Nat) [NeZero Q] :
    0 < relationProfileSmoothing epsilon Q m ∧
      relationProfileSmoothing epsilon Q m < 1 / 4 ∧
      120 * m * relationProfileSmoothing epsilon Q m ≤ 1 / (Q : Real)^m ∧
      480 * m * relationProfileSmoothing epsilon Q m / (1 / (Q : Real)^m) ≤ epsilon / 6 := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hQone : (1 : Real) ≤ Q := by exact_mod_cast NeZero.pos Q
  have hbeta : 0 < 1 / (Q : Real)^m := by positivity
  have hb1 : 1 / (Q : Real)^m ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hQone)
  have ht : 0 < relationProfileSmoothing epsilon Q m := by unfold relationProfileSmoothing; positivity
  have heq : relationProfileSmoothing epsilon Q m * (2880 * (m + 1 : Real)) =
      epsilon * (1 / (Q : Real)^m) := by
    unfold relationProfileSmoothing
    field_simp
  have hepsbeta : epsilon * (1 / (Q : Real)^m) ≤ 1 / (Q : Real)^m := by nlinarith
  have hm : (0 : Real) ≤ m := Nat.cast_nonneg _
  refine ⟨ht, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · apply (div_le_iff₀ hbeta).mpr
    nlinarith

/-- Few bounded bad relations at the explicit cutoff give the requested
box error. No analytic truncation, annulus, or base-size hypothesis remains. -/
theorem tuple_bohr_quasirandom_explicit {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D C : Finset (ZMod N)) (hC : C ⊆ D) (hCne : C.Nonempty)
    (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (m : Nat) {rho nu epsilon : Real}
    (hrho : 0 ≤ rho) (hnu : 0 ≤ nu) (hrhoQuarter : rho < 1 / 4) (hnuQuarter : nu < 1 / 4)
    (heps : 0 < epsilon) (hepsOne : epsilon ≤ 1)
    (hN : 1 / relationProfileSmoothing epsilon Q m ≤ N) (hQ : 1 ≤ rho * Q)
    (hm : Fintype.card ι + 2 * Fintype.card κ ≤ m)
    (hbad : ((boundedBadRelationPairs gamma D L C (relationProfileCutoff epsilon Q m)).card : Real) ≤
      (epsilon / 6) * (C.card : Real)^2) :
    ∃ delta : Real, 0 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (x : ↥(bohr (Finset.univ.image gamma) rho)) (y : ↥C) =>
        (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j y) nu
          then (1 : Real) else 0) - delta) ≤
      epsilon * ((bohr (Finset.univ.image gamma) rho).card : Real)^2 * (C.card : Real)^2 := by
  obtain ⟨ht, htquarter, hsmall, herror⟩ := relationProfileSmoothing_budget heps hepsOne Q m
  have hN' : 1 ≤ relationProfileSmoothing epsilon Q m * N := by
    have h := (div_le_iff₀ ht).mp hN
    nlinarith only [h]
  have hR : 1 / (relationProfileSmoothing epsilon Q m)^2 ≤ relationProfileCutoff epsilon Q m + 1 :=
    (Nat.le_ceil _).trans (by norm_num [relationProfileCutoff])
  obtain ⟨delta, hd0, hd1, hbox⟩ := tuple_bohr_quasirandom_scaled gamma D C hC hCne L hzero
    m (relationProfileCutoff epsilon Q m) hrho hnu ht (by linarith) (by linarith)
    hN' hQ hm hR hsmall (by linarith : epsilon / 6 < 1) hbad
  refine ⟨delta, hd0, hd1, hbox.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

end LeanProofs.GowersSzemeredi

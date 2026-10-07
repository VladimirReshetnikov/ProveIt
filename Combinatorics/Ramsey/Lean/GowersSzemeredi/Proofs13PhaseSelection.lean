import GowersSzemeredi.Proofs13UntrimmedSelection
import GowersSzemeredi.Proofs05PhaseMetric

/-! Phase clusters control the affine expressions on full quadratic cells,
including endpoints, and preserve the stronger critical-height density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem stage135_full_cell_small_affine_of_phase {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2) (Q : ModAP N) (hQ : 3 ≤ Q.length)
    (a b : ZMod N) (U : Nat) (hU : 0 < U) (z : Complex)
    (hphase : ∀ x ∈ Q.carrier,
      ‖exponential (-(stage135AmbientQuadratic a b x)) - z‖ ≤ 1 / (4 * U))
    {h : ZMod N} (hh : h ∈ Q.carrier) :
    (centeredAbs ((a * h + b) * Q.step) : Real) ≤ (N : Real) / (2 * U) := by
  have hs : (0 : Real) ≤ N * (1 / (4 * U)) / 2 := by positivity
  have h := stage135_full_cell_small_affine_of_pairwise hprime hodd Q hQ a b hs
    (fun x hx y hy => centeredAbs_sub_le_of_phase_cluster _ _ z (hphase x hx) (hphase y hy)) hh
  convert h using 1 <;> ring

theorem stage135_of_phase_cell {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2)
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N)
    (hQ : Q.IsProper) (hstep : Q.step != 0) (hsub : Q.carrier ⊆ D.P.carrier)
    (hthree : 3 ≤ Q.length) (U : Nat) (hU : 0 < U)
    (hlength : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ Q.length)
    (hscale : 1 / (2 * (U : Real)) ≤
      (D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))))
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * Q.length / 8 ≤
      (goodHeightWeight S (Q.carrier ∩ D.H) : Real))
    (hphase : ∀ i, ∃ z : Complex, ∀ x ∈ Q.carrier,
      ‖exponential (-(stage135AmbientQuadratic (D.a i) (D.b i) x)) - z‖ ≤ 1 / (4 * U)) :
    IsStage135Data S D ⟨Q⟩ ∧
      S.alpha ^ 32 * Q.length / 16 ≤ (criticalHeights S D ⟨Q⟩).card := by
  have hcount := stage135_critical_count_of_weight S D Q hQ hweight
  refine ⟨⟨hstep, hQ, hsub, hlength, ?_, ?_⟩, hcount⟩
  · intro i h hh
    obtain ⟨z, hz⟩ := hphase i
    calc
      _ ≤ (N : Real) / (2 * U) :=
        stage135_full_cell_small_affine_of_phase hprime hodd Q hthree (D.a i) (D.b i) U hU z hz hh
      _ = (1 / (2 * (U : Real))) * N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg N)
  · have hmass : 0 ≤ S.alpha ^ 32 * (Q.length : Real) := by positivity
    change S.alpha ^ 32 * (Q.length : Real) / 20 ≤ _
    linarith only [hcount, hmass]

end LeanProofs.GowersSzemeredi

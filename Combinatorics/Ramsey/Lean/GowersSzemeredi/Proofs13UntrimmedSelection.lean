import GowersSzemeredi.Proofs13QuadraticEndpoints
import GowersSzemeredi.Proofs13QuadraticPartition

/-! Weighted quadratic selection with the entire selected progression
retained. A factor-four diameter reserve replaces the density-dependent
endpoint-deletion budget and preserves strong-height density alpha^32/16. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem stage135_of_untrimmed_quadratic_cell {N : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2)
    (S : Section13Context N) (D : Stage134Data N) (Q : ModAP N)
    (hQ : Q.IsProper) (hstep : Q.step != 0) (hsub : Q.carrier ⊆ D.P.carrier)
    (hthree : 3 ≤ Q.length)
    (hlength : (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ Q.length)
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * Q.length / 8 ≤
      (goodHeightWeight S (Q.carrier ∩ D.H) : Real))
    (hdiam : ∀ i, diameterAtMostReal
      (Q.carrier.image (stage135AmbientQuadratic (D.a i) (D.b i)))
      (((D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N) / 4)) :
    IsStage135Data S D ⟨Q⟩ ∧
      S.alpha ^ 32 * Q.length / 16 ≤ (criticalHeights S D ⟨Q⟩).card := by
  have hcount := stage135_critical_count_of_weight S D Q hQ hweight
  refine ⟨⟨hstep, hQ, hsub, hlength, ?_, ?_⟩, hcount⟩
  · intro i h hh
    have hsmall := stage135_full_cell_small_affine hprime hodd Q hthree
      (D.a i) (D.b i) (by positivity) (hdiam i) hh
    dsimp only at hsmall ⊢
    linarith only [hsmall]
  · have hmass : 0 ≤ S.alpha ^ 32 * (Q.length : Real) := by positivity
    change S.alpha ^ 32 * (Q.length : Real) / 20 ≤ _
    linarith only [hcount, hmass]

theorem stage135_select_untrimmed_partition {N M : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : N != 2)
    (S : Section13Context N) (D : Stage134Data N) (Q : Fin M → ModAP N)
    (hM : 0 < M) (hP : D.P.IsProper) (hH : D.H ⊆ D.P.carrier)
    (hpart : IsPartition (fun j => (Q j).carrier) D.P.carrier)
    (hproper : ∀ j, (Q j).IsProper) (hstep : ∀ j, (Q j).step != 0)
    (hthree : ∀ j, 3 ≤ (Q j).length)
    (hlength : ∀ j, (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ (Q j).length)
    (hweight : S.alpha ^ 32 * (N : Real) ^ 31 * D.P.length / 8 ≤
      (goodHeightWeight S D.H : Real))
    (hdiam : ∀ i j, diameterAtMostReal
      ((Q j).carrier.image (stage135AmbientQuadratic (D.a i) (D.b i)))
      (((D.P.length : Real) ^ (-((1 : Real) / (2 : Real) ^ (11 * D.q))) * N) / 4)) :
    ∃ j, IsStage135Data S D ⟨Q j⟩ ∧
      S.alpha ^ 32 * (Q j).length / 16 ≤ (criticalHeights S D ⟨Q j⟩).card := by
  obtain ⟨j, hj⟩ := stage135_select_weighted_cell S D Q hM hP hH hpart hproper hweight
  exact ⟨j, stage135_of_untrimmed_quadratic_cell hprime hodd S D (Q j)
    (hproper j) (hstep j) (hpart.cell_subset j) (hthree j) (hlength j) hj
    (fun i => hdiam i j)⟩

end LeanProofs.GowersSzemeredi

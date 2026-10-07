import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical NNReal

theorem preparedUniformDegreeGeometryAt_decidableTransport
    {m : ℕ} {G : Type} [fG : Fintype G]
    {I : Fin m → Type} [fI : ∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [fB : ∀ a, Fintype (B a)]
    {J : Fin m → Type} [fJ : ∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {s Cdetect nX : ℕ}
    {Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog : ℝ}
    {dG dG' : DecidableEq G}
    {dB dB' : ∀ a, DecidableEq (B a)}
    (h : @PreparedUniformDegreeGeometryAt m G fG dG I fI n B fB dB J fJ
      U basis R σ S s Cdetect nX Bstruct Pscale D target Pk Prho Qstride
      pDetect pRadius aDetect gainLog) :
    @PreparedUniformDegreeGeometryAt m G fG dG' I fI n B fB dB' J fJ
      U basis R σ S s Cdetect nX Bstruct Pscale D target Pk Prho Qstride
      pDetect pRadius aDetect gainLog := by
  cases Subsingleton.elim dG dG'
  cases Subsingleton.elim dB dB'
  exact h

theorem preparedScheduledDirectSourceAvailability_decidableTransport
    {m s : ℕ} {G : Type} [Fintype G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {S : LayerSamplerScale (G := G) B U basis R σ} {nX : ℕ}
    {selection : Fin (s + 1) ↪ G} {stride N : Fin nX → ℕ}
    {Pdetect : Polynomial ℕ} {sourceU pModel pSlice : ℝ} {Vtail : Fin m → ℝ≥0}
    {τ : ℝ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ}
    {dG dG' : DecidableEq G}
    (h : letI := dG
      PreparedScheduledDirectSourceAvailability
        (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
        (selection := selection) (stride := stride) (N := N)
        (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
        (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
        Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    letI := dG'
    PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  cases Subsingleton.elim dG dG'
  exact h

end Erdos3.VectorPolynomial

end

end OAI

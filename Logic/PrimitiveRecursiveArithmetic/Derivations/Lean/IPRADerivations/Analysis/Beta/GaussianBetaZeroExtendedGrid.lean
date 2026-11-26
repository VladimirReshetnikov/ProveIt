import IPRADerivations.Analysis.Beta.GaussianBetaZeroExtension

/-!
# Exact supported and exterior quadratures of the extended beta evaluator

At every active grid index, the time code is the original affine
fraction. On a supported interval the whole quadrature is the old beta
quadrature. An interval starting at or after the degree has zero sum,
including its first row at an exact degree endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaZeroExtendedGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaZeroExtension (evaluatorF row_at_supported row_at_exterior row_at_endpoint)
open GaussianBetaKernelGridComparison (sampleDataBeta)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sample (p M a C E z B N : PTm n) : PTm n :=
  quadrature evaluatorF p M a C E (sampleDataBeta z B N)

private theorem supported_grid_read (i p M a C E z B N : PTm n)
    (hi : Γ ⊢[PRAAx] lt i M) (hend : Γ ⊢[PRAAx] le (a+C) (E*N)) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i (sampleData p M a C E (sampleDataBeta z B N)) ≐
      inst2 (sampleBody GaussianBetaKernelGridComparison.evaluatorF) i
        (sampleData p M a C E (sampleDataBeta z B N)) := by
  let u := a*M+C*i
  let v := E*M
  let x := sampleDataBeta z B N
  have grow := add_le_add₂ (le_refl (Γ := Γ) (a*M))
    (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right C (le_of_lt hi)))
  have reach : Γ ⊢[PRAAx] le (a*M+C*M) (v*N) :=
    le_congr (by ipra_ring) (by dsimp only [v]; ipra_ring) (mul_le_mul_right M hend)
  have support : Γ ⊢[PRAAx] le u (v*N) := le_trans grow reach
  exact (sample_body_at evaluatorF i p M a C E x).eqTrans
    ((row_at_supported p z B u v N support).eqTrans
      ((GaussianBetaKernelGridComparison.row_at p z B u v N).eqSymm.eqTrans
        (sample_body_at GaussianBetaKernelGridComparison.evaluatorF i p M a C E x).eqSymm))

/-- The original beta quadrature is unchanged on its supported part. -/
theorem same_supported_grid (p M a C E z B N : PTm n) (hend : Γ ⊢[PRAAx] le (a+C) (E*N)) :
    Γ ⊢[PRAAx] sample p M a C E z B N ≐
      quadrature GaussianBetaKernelGridComparison.evaluatorF p M a C E (sampleDataBeta z B N) := by
  apply qmul_congr (.eqRefl _)
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have ep : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a+Syn.shift C) (Syn.shift E*Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hend.shift
  simpa only [Syn.shift,GaussianCompactRiemannName.subst_sampleData,GaussianBetaKernelGridComparison.subst_sampleDataBeta] using
    supported_grid_read (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
      (Syn.shift z) (Syn.shift B) (Syn.shift N) Prf.hyp0 ep.wk

private theorem exterior_grid_read (i p M a C E z B N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hstart : Γ ⊢[PRAAx] le (E*N) a) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i (sampleData p M a C E (sampleDataBeta z B N)) ≐ qzero := by
  let u := a*M+C*i
  let v := E*M
  let x := sampleDataBeta z B N
  have fromStart : Γ ⊢[PRAAx] le (v*N) u :=
    le_trans (le_congr (by dsimp only [v]; ipra_ring) (.eqRefl _) (mul_le_mul_right M hstart))
      (le_add_right _ _)
  refine (sample_body_at evaluatorF i p M a C E x).eqTrans ?_
  refine .orE (lt_or_eq_of_le fromStart) (row_at_exterior p z B u v N Prf.hyp0) ?_
  have time : ((v*N ≐ u) :: Γ) ⊢[PRAAx] grid i M a C E ≐ pairT (v*N) v :=
    congrPairT Prf.hyp0.eqSymm (.eqRefl _)
  exact (congrAp3 evaluatorF (.eqRefl _) time (.eqRefl _)).eqTrans
    (row_at_endpoint p z B v N (positive_product _ _ hE.wk hM.wk) hN.wk)

/-- Zero at the degree endpoint is included in the whole exterior grid. -/
theorem exterior_grid_zero (p M a C E z B N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hstart : Γ ⊢[PRAAx] le (E*N) a) :
    Γ ⊢[PRAAx] sample p M a C E z B N ≐ qzero := by
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift E*Syn.shift N) (Syn.shift a) := by
    simpa [Fm.shift,Syn.shift] using hstart.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.zeroTerms (sampleBody evaluatorF) M
      (sampleData p M a C E (sampleDataBeta z B N)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianCompactRiemannName.subst_sampleData,GaussianBetaKernelGridComparison.subst_sampleDataBeta] using
      exterior_grid_read (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift a) (Syn.shift C) (Syn.shift E)
        (Syn.shift z) (Syn.shift B) (Syn.shift N) es.wk ms.wk ns.wk ps.wk
  have body := GaussianRationalMatrixFiniteSums.sum_zero_of_terms _ _ _ terms
  exact (qmul_congr (.eqRefl _) body).eqTrans (qmul_zero_right _)

theorem original_beta_zero_extended_supported_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (le (var 2+var 3) (var 4*var 7) ⟶ sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
        quadrature GaussianBetaKernelGridComparison.evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4)
          (sampleDataBeta (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (same_supported_grid _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_beta_zero_extended_exterior_grid_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((le one (var 4) ⋏ (le one (var 1) ⋏ (le one (var 7) ⋏ le (var 4*var 7) (var 2)))) ⟶
        sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ qzero) :=
  closeUniv 8 (.impI (exterior_grid_zero _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaZeroExtendedGrid

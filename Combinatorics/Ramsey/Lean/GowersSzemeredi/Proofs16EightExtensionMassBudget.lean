import GowersSzemeredi.Proofs16PurificationMassBudget

/-! A strengthened error budget supplies four common anchors and retains
a dense tiny endpoint set for extending quadruple compatibility to eight terms. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Reserve the tiny progression mass, rather than merely half the larger core. -/
theorem progression_eight_extension_loss_budget {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) {delta eta : Real}
    (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(1024*(65536 : Real)^Q.rank)) :
    2*(eta*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
      ((progressionPurificationVertexThreshold Q : Real)+1) ≤
        delta*N/(16*(1024 : Real)^Q.rank) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨hb,ht⟩ := progression_purification_threshold_mass Q hQ hmass
  let A := delta*N/(4^(Q.rank+1) : Real)
  let B := delta*N/(8*(16 : Real)^Q.rank)
  let C := delta*N/(16*(1024 : Real)^Q.rank)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hprod : A*B ≤ ((progressionGoodPairThreshold Q : Real)+1)*
      ((progressionPurificationVertexThreshold Q : Real)+1) :=
    mul_le_mul hb ht hB (by positivity)
  have heq : C*(A*B) = 2*(delta^3/(1024*(65536 : Real)^Q.rank))*(N : Real)^3 := by
    dsimp [A,B,C]
    have hpow : (65536 : Real)^Q.rank = (1024 : Real)^Q.rank*(4 : Real)^Q.rank*(16 : Real)^Q.rank := by
      rw [←mul_pow, ←mul_pow]
      norm_num
    rw [pow_succ, hpow]
    field_simp
    ring
  have herror : 2*eta*(N : Real)^3 ≤ C*(A*B) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heta (by norm_num)) (by positivity)
  have hscaled := herror.trans (mul_le_mul_of_nonneg_left hprod hC)
  apply (div_le_iff₀ (by positivity : 0 < (progressionPurificationVertexThreshold Q : Real)+1)).mpr
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < (progressionGoodPairThreshold Q : Real)+1)).mpr
  convert hscaled using 1 <;> first | rfl | ring

/-- The all-quadruple core retains the stronger explicit complement bound. -/
theorem exists_progression_near_full_quad_core {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho delta eta : Real} (hrho : 0 < rho) (hK : 0 < K) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(1024*(65536 : Real)^Q.rank))
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hfail : ((progressionMapImageFailures Q.carrier T L rho K).card : Real) ≤ eta*(N : Real)^3) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    ∃ S ⊆ (centeredProgressionShrink Q 16).carrier,
      (((centeredProgressionShrink Q 16).carrier \ S).card : Real) ≤
        delta*N/(16*(1024 : Real)^Q.rank) ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation T L (rho/4)
          (M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)) a b c e := by
  intro M
  obtain ⟨S,hS,hmassS,hquad⟩ := exists_progression_all_quad_image_core Q hQ T L hrho hK hT hL hfail
  have hloss := progression_eight_extension_loss_budget Q hQ hdelta hmass heta
  have hpartition : (((centeredProgressionShrink Q 16).carrier \ S).card : Real)+(S.card : Real) =
      (centeredProgressionShrink Q 16).carrier.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hS
  exact ⟨S,hS,by linarith,hquad⟩

end LeanProofs.GowersSzemeredi

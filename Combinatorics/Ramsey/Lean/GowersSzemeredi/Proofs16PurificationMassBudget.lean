import GowersSzemeredi.Proofs16AllQuadImagePurification

/-! Quantitative nonvacuity of the purified vertex core. An explicit cubic
error budget in the parent density retains half the guaranteed sixteenth
progression mass. All rounding is included in the natural thresholds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Natural division followed by adding one dominates the real quotient. -/
theorem rounded_division_real_lower (a : Nat) {b : Nat} (hb : 0 < b) :
    (a : Real)/b ≤ ((a/b : Nat) : Real)+1 := by
  have hdiv := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  have hnat : a ≤ b*(a/b+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have hR : (a : Real) ≤ (b : Real)*(((a/b : Nat) : Real)+1) := by exact_mod_cast hnat
  have hbR : (0 : Real) < b := by exact_mod_cast hb
  exact (div_le_iff₀ hbR).mpr (by simpa only [mul_comm] using hR)

/-- Convert the rank loss in shrinking into a real cardinality lower bound. -/
theorem centered_progression_shrink_real_mass {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) {m : Nat} (hm : 0 < m) :
    (Q.carrier.card : Real)/(2*(m : Real))^Q.rank ≤
      ((centeredProgressionShrink Q m).carrier.card : Real) := by
  have h := centered_progression_shrink_card Q hQ hm
  have hR : (Q.carrier.card : Real) ≤ (2*(m : Real))^Q.rank*
      (centeredProgressionShrink Q m).carrier.card := by exact_mod_cast h
  exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hR)

/-- The rounded pair and vertex thresholds have the required linear mass
lower bounds, independently of the input scale. -/
theorem progression_purification_threshold_mass {N : Nat} (Q : CenteredProgression N)
    (hQ : Q.Proper) {delta : Real} (hmass : delta*N ≤ (Q.carrier.card : Real)) :
    delta*N/(4^(Q.rank+1) : Real) ≤ (progressionGoodPairThreshold Q : Real)+1 ∧
    delta*N/(8*(16 : Real)^Q.rank) ≤ (progressionPurificationVertexThreshold Q : Real)+1 := by
  constructor
  · have h := rounded_division_real_lower Q.carrier.card (by positivity : 0 < 4^(Q.rank+1))
    have he : ((4^(Q.rank+1) : Nat) : Real) = (4 : Real)^(Q.rank+1) := by norm_cast
    rw [he] at h
    exact (div_le_div_of_nonneg_right hmass (by positivity)).trans h
  · have h8 := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (8 : Nat))
    norm_num only [Nat.cast_ofNat] at h8
    have h := rounded_division_real_lower (centeredProgressionShrink Q 8).carrier.card (by decide : 0 < (8 : Nat))
    have hmass8 : delta*N/(16 : Real)^Q.rank ≤ ((centeredProgressionShrink Q 8).carrier.card : Real) :=
      (div_le_div_of_nonneg_right hmass (by positivity)).trans h8
    have hd := (div_le_div_of_nonneg_right hmass8 (by norm_num : (0 : Real) ≤ 8)).trans h
    convert hd using 1 <;> first | rfl | ring

/-- A small enough input error makes the pruning loss at most half the
sixteenth shrinking's guaranteed mass. -/
theorem progression_purification_loss_budget {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) {delta eta : Real}
    (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(128*(2048 : Real)^Q.rank)) :
    2*(eta*(N : Real)^3/((progressionGoodPairThreshold Q : Real)+1))/
      ((progressionPurificationVertexThreshold Q : Real)+1) ≤
        delta*N/(2*(32 : Real)^Q.rank) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨hb,ht⟩ := progression_purification_threshold_mass Q hQ hmass
  let A := delta*N/(4^(Q.rank+1) : Real)
  let B := delta*N/(8*(16 : Real)^Q.rank)
  let C := delta*N/(2*(32 : Real)^Q.rank)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hprod : A*B ≤ ((progressionGoodPairThreshold Q : Real)+1)*
      ((progressionPurificationVertexThreshold Q : Real)+1) :=
    mul_le_mul hb ht hB (by positivity)
  have heq : C*(A*B) = 2*(delta^3/(128*(2048 : Real)^Q.rank))*(N : Real)^3 := by
    dsimp [A,B,C]
    have hpow : (2048 : Real)^Q.rank = (32 : Real)^Q.rank*(4 : Real)^Q.rank*(16 : Real)^Q.rank := by
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

/-- A nonempty quantitatively dense core with every additive quadruple
controlled on the endpoint-only quarter-radius domain. -/
theorem exists_dense_progression_all_quad_image_core {N d K : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho delta eta : Real} (hrho : 0 < rho) (hK : 0 < K) (hdelta : 0 < delta)
    (hmass : delta*N ≤ (Q.carrier.card : Real))
    (heta : eta ≤ delta^3/(128*(2048 : Real)^Q.rank))
    (hT : ∀ x ∈ Q.carrier, (T x).card ≤ d)
    (hL : ∀ x ∈ Q.carrier, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hfail : ((progressionMapImageFailures Q.carrier T L rho K).card : Real) ≤ eta*(N : Real)^3) :
    let M := K*K*refinementKernelCap (4*d) (2*d) rho rho
    ∃ S ⊆ (centeredProgressionShrink Q 16).carrier,
      delta*N/(2*(32 : Real)^Q.rank) ≤ (S.card : Real) ∧ S.Nonempty ∧
      ∀ a b c e : ZMod N, a ∈ S → b ∈ S → c ∈ S → e ∈ S → a-b = c-e →
        ColumnQuadImageRelation T L (rho/4)
          (M*M*refinementKernelCap (4*d) (2*d) (rho/2) (rho/2)) a b c e := by
  intro M
  obtain ⟨S,hS,hmassS,hquad⟩ := exists_progression_all_quad_image_core Q hQ T L hrho hK hT hL hfail
  have hloss := progression_purification_loss_budget Q hQ hdelta hmass heta
  have hshrink := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (16 : Nat))
  have hD : delta*N/(32 : Real)^Q.rank ≤ ((centeredProgressionShrink Q 16).carrier.card : Real) := by
    norm_num only [Nat.cast_ofNat] at hshrink
    exact (div_le_div_of_nonneg_right hmass (by positivity)).trans hshrink
  have hhalf : delta*N/(32 : Real)^Q.rank = 2*(delta*N/(2*(32 : Real)^Q.rank)) := by ring
  have hSbound : delta*N/(2*(32 : Real)^Q.rank) ≤ (S.card : Real) := by
    rw [hhalf] at hD
    linarith
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hSpos : (0 : Real) < S.card := (by positivity : 0 < delta*N/(2*(32 : Real)^Q.rank)).trans_le hSbound
  exact ⟨S,hS,hSbound,Finset.card_pos.mp (by exact_mod_cast hSpos),hquad⟩

end LeanProofs.GowersSzemeredi

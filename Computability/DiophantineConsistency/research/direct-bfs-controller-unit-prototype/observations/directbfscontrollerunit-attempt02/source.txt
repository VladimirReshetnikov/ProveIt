import DiophantineConsistency.ArithmeticConstructionUnitCompact44
import DirectBFSGammaOrder
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFSControllerUnit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPow ArithmeticControllerLift ArithmeticControllerDataCompact44 ArithmeticConstructionUnitCompact44

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bfs_Gamma_res (K : V) (hK : K % 342946332593 = 264033855341) (m e : V) :
    Gamma K (power 581197 (m + 1)) (power 581197 e) % 342946332593 = ((299052170727 : ℕ) : V) := by
  have hq := exp_p_res (V := V) (m + 1)
  have hs := exp_p_res (V := V) e
  have hq2 : (Exp.exp (590069 * power (581197 : V) (m + 1)) ^ 2) % 342946332593 =
      ((201792753151 : ℕ) : V) := by
    rw [pow_two, mul_res hq hq]
  have hq21 := sub_one_res (by norm_num) (by norm_num) hq2
  have hKs := add_res hK hs
  have hqK := mul_res hq hKs
  have h1 := add_res one_res hqK
  have hr := mul_res (mul_res rho_res hq21) h1
  exact hr

/-- `Γ` is a unit modulo `d·N`, conditional on the stated kernel residue. -/
theorem bfs_gamma_unit (K : V) (hK : K % 342946332593 = 264033855341) (m e : V) :
    ∃ Γi, (Gamma K (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  set G := Gamma K (power (581197 : V) (m + 1)) (power 581197 e) with hG
  have hGr := bfs_Gamma_res K hK m e
  rw [← hG] at hGr
  -- G^λ ≡ 1 (mod L)
  have hpow : power G 581196 % 342946332593 = 1 := by
    rw [pow_cong L_pos G ((299052170727 : ℕ) : V) (by rw [hGr, mod_eq_self_of_lt (by norm_num)]),
      show (581196 : V) = ((581196 : ℕ) : V) by simp, power_natCast, ← Nat.cast_pow,
      show (342946332593 : V) = ((342946332593 : ℕ) : V) by simp, cast_mod_eq DirectBFSGammaOrder.gamma_order]
    simp
  obtain ⟨v1, hd⟩ : ∃ v1, power G 581196 = 1 + 590069 * 581197 * v1 :=
    ⟨_, by simpa only [show (590069 : V) * 581197 = 342946332593 by norm_num, hpow, add_comm]
      using (div_add_mod (power G 581196) (590069 * 581197)).symm⟩
  obtain ⟨w, _, hw⟩ := lte (c := (590069 : V)) (v := v1) p_odd m
  refine ⟨power G (581196 * power 581197 m - 1), ?_⟩
  have hpos : 1 ≤ 581196 * power (581197 : V) m :=
    one_le_mul (by norm_num) (pos_iff_one_le.mp (power_pos _ _ p_pos))
  have hmul : G * power G (581196 * power 581197 m - 1) = power G (581196 * power 581197 m) := by
    conv_rhs => rw [← tsub_add_cancel_of_le hpos]
    rw [power_succ]
  rw [hmul, ← power_iterate, hd, hw, power_succ,
    show (590069 : V) * (581197 * power 581197 m) = 590069 * 581197 * power 581197 m by ring,
    mod_add_mul' _ _ (mul_pos C0_pos (power_pos _ _ p_pos))]

/-- The residue premise can be supplied by a standard natural-number calculation. -/
theorem bfs_gamma_unit_nat (k : ℕ) (hk : k % 342946332593 = 264033855341) (m e : V) :
    ∃ Γi, (Gamma (k : V) (power 581197 (m + 1)) (power 581197 e) * Γi) %
        (590069 * power 581197 (m + 1)) = 1 % (590069 * power 581197 (m + 1)) := by
  exact bfs_gamma_unit (k : V) (cast_mod_eq hk) m e


#print axioms DirectBFSControllerUnit.bfs_Gamma_res
#print axioms DirectBFSControllerUnit.bfs_gamma_unit
end DirectBFSControllerUnit

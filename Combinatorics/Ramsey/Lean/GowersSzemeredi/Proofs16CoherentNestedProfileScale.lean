import GowersSzemeredi.Proofs16CoherentRadiusProfile

/-! Reserve graph-profile resolution for both endpoint-word radii and
an additional factor 3000 used in subsequent local extension arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentNestedBridgeDepth (K L : Nat) : Nat := 13+2*(K+L+2)

def coherentNestedProfileRadius (sigma : Real) (K L : Nat) : Real :=
  sigma/((1296 : Real)^2*9^(K+L+2)*3000)

theorem coherentNestedBridgeDepth_ge_seven (K L : Nat) : 7 ≤ coherentNestedBridgeDepth K L := by
  unfold coherentNestedBridgeDepth
  omega

theorem coherentNestedProfileRadius_pos {sigma : Real} (hs : 0 < sigma) (K L : Nat) :
    0 < coherentNestedProfileRadius sigma K L := by unfold coherentNestedProfileRadius; positivity

theorem coherentNestedProfileDenominator_le (K L : Nat) :
    (1296 : Real)^2*9^(K+L+2)*3000 ≤ (6 : Real)^(coherentNestedBridgeDepth K L) := by
  have hp : (9 : Real)^(K+L+2) ≤ (6 : Real)^(2*(K+L+2)) := by
    simpa only [←pow_mul] using pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 9)
      (by norm_num : (9 : Real) ≤ 6^2) (K+L+2)
  have hc : (1296 : Real)^2*3000 ≤ (6 : Real)^13 := by norm_num
  have hm := mul_le_mul hc hp (by positivity) (by positivity : (0 : Real) ≤ 6^13)
  simpa only [coherentNestedBridgeDepth,pow_add,mul_assoc,mul_left_comm,mul_comm] using hm

theorem coherentNestedProfileRadius_cells {sigma : Real} (hs : 0 < sigma)
    (ell K L s : Nat) (hsell : s ≤ ell) :
    3 ≤ coherentNestedProfileRadius (sigma/(2 : Real)^s) K L *
      coherentRadiusProfileCells sigma ell (coherentNestedBridgeDepth K L) := by
  have hm := coherentRadiusProfileCells_spec hs hsell (le_refl (coherentNestedBridgeDepth K L))
  have hr : (sigma/(2 : Real)^s)/(6 : Real)^(coherentNestedBridgeDepth K L) ≤
      coherentNestedProfileRadius (sigma/(2 : Real)^s) K L :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (coherentNestedProfileDenominator_le K L)
  exact hm.trans (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _))

end LeanProofs.GowersSzemeredi

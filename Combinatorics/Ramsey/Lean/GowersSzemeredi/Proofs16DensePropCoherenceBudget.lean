import GowersSzemeredi.Proofs16DenseIndexWindow

/-! Uniform quantitative controls for completing Proposition 9.3's dense
active window. The family-size bound is independent of the modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def densePropWindowCost (delta : Real) (s : Nat) : Nat :=
  (⌈(s : Real)/delta⌉₊+8*s).choose (8*s)

def densePropQuadDensity (coefficient delta : Real) (s : Nat) : Real :=
  (coefficient/2)/(densePropWindowCost delta s : Real)

theorem densePropWindowCost_pos (delta : Real) (s : Nat) : 0 < densePropWindowCost delta s :=
  Nat.choose_pos (by omega)

theorem densePropQuadDensity_pos {coefficient : Real} (hc : 0 < coefficient) (delta : Real) (s : Nat) :
    0 < densePropQuadDensity coefficient delta s := by
  have hcost : (0 : Real) < densePropWindowCost delta s := by exact_mod_cast densePropWindowCost_pos delta s
  unfold densePropQuadDensity
  positivity

/-- The source quadruple count and potential bound give one uniform density,
without choosing a window and then estimating errors inside it. -/
theorem dense_prop_quadruple_mass {N m s : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) {coefficient delta : Real} (hd : 0 < delta)
    (hm : ⌈delta*(N : Real)^2⌉₊ * m ≤ N*N*s)
    (hcount : coefficient*(N : Real)^3-6*(N : Real)^2 ≤
      ((m+8*s).choose (8*s) : Real)*Q.card)
    (hN : 12 ≤ coefficient*(N : Real)) :
    densePropQuadDensity coefficient delta s*(N : Real)^3 ≤ Q.card := by
  have hmBound := dense_chart_family_size_bound hd hm
  have hcost : (0 : Real) < densePropWindowCost delta s := by exact_mod_cast densePropWindowCost_pos delta s
  have hchoose : ((m+8*s).choose (8*s) : Real) ≤ densePropWindowCost delta s := by
    exact_mod_cast Nat.choose_le_choose (8*s) (Nat.add_le_add_right hmBound (8*s))
  have hsmall : 6*(N : Real)^2 ≤ (coefficient/2)*(N : Real)^3 := by
    have h := mul_le_mul_of_nonneg_right hN (sq_nonneg (N : Real))
    nlinarith only [h]
  have htotal : (coefficient/2)*(N : Real)^3 ≤ (densePropWindowCost delta s : Real)*Q.card := by
    calc (coefficient/2)*(N : Real)^3 ≤ coefficient*(N : Real)^3-6*(N : Real)^2 := by linarith only [hsmall]
      _ ≤ ((m+8*s).choose (8*s) : Real)*Q.card := hcount
      _ ≤ _ := mul_le_mul_of_nonneg_right hchoose (Nat.cast_nonneg _)
  unfold densePropQuadDensity
  rw [div_mul_eq_mul_div,div_le_iff₀ hcost]
  simpa only [mul_comm] using htotal

end LeanProofs.GowersSzemeredi

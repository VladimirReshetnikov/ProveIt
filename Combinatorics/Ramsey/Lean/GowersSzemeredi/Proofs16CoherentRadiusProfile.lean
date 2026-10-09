import GowersSzemeredi.Proofs16CoherentAdaptiveProfiles

/-! A single cell budget covers all radii of a prescribed finite chain,
including the one-third radii used by weak transitivity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentRadiusProfileCells (sigma : Real) (ell depth : Nat) : Nat :=
  ⌈3*(2 : Real)^ell*(6 : Real)^depth/sigma⌉₊

theorem coherentRadiusProfileCells_pos {sigma : Real} (hs : 0 < sigma) (ell depth : Nat) :
    0 < coherentRadiusProfileCells sigma ell depth := Nat.ceil_pos.mpr (by positivity)

theorem coherentRadiusProfileCells_spec {sigma : Real} (hs : 0 < sigma)
    {ell depth s i : Nat} (hsell : s ≤ ell) (hidepth : i ≤ depth) :
    3 ≤ (sigma/(2 : Real)^s/(6 : Real)^i)*(coherentRadiusProfileCells sigma ell depth : Real) := by
  have hc : 3*(2 : Real)^ell*(6 : Real)^depth/sigma ≤
      (coherentRadiusProfileCells sigma ell depth : Real) := Nat.le_ceil _
  have hm := (div_le_iff₀ hs).mp hc
  have hp : (2 : Real)^s*(6 : Real)^i ≤ (2 : Real)^ell*(6 : Real)^depth :=
    mul_le_mul (pow_le_pow_right₀ (by norm_num) hsell) (pow_le_pow_right₀ (by norm_num) hidepth)
      (by positivity) (by positivity)
  rw [div_div,div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hm,hp]

theorem DenseBohrGraphProfiles.radius_chain {N ell H m : Nat} [NeZero N]
    {B C : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N} {epsilon sigma : Real}
    (h : DenseBohrGraphProfiles B C theta H m epsilon)
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (s i : Nat)
    (hH : 3 ≤ (sigma/(2 : Real)^s/(6 : Real)^i)*(H : Real)) :
    let r := sigma/(2 : Real)^s/(6 : Real)^i
    ∃ delta : Real, (1/(H : Real)^m)/2 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (z : ↥(bohr B (r/3))) (u : ↥C) =>
        (if (z : ZMod N) ∈ bohr (Finset.univ.image fun j => theta j u) (r/3)
          then (1 : Real) else 0)-delta) ≤
      epsilon^4*((bohr B (r/3)).card : Real)^2*(C.card : Real)^2 := by
  let r := sigma/(2 : Real)^s/(6 : Real)^i
  have hr : 0 < r := by dsimp [r]; positivity
  have hrle : r ≤ sigma := (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans
    (div_le_self hs.le (one_le_pow₀ (by norm_num)))
  exact h (r/3) (r/3) (by positivity) le_rfl (by linarith) (by dsimp only [r]; nlinarith only [hH])

end LeanProofs.GowersSzemeredi

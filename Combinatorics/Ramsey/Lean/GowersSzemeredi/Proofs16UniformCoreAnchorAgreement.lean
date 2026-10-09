import GowersSzemeredi.Proofs16CoreAnchorAgreementDomain

/-! Eliminate the auxiliary integer from the core agreement density.
All losses are explicit functions of radii and rank, independent of N. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coreAnchorAgreementDensity (t : Real) (k g d : Nat) (r sigma : Real) : Real :=
  t/(refinementCells (min sigma (r/4)) : Real)^(k+g+4*d)

theorem coreAnchorAgreementDensity_pos {t r sigma : Real} (ht : 0 < t)
    (hr : 0 < r) (hs : 0 < sigma) (k g d : Nat) :
    0 < coreAnchorAgreementDensity t k g d r sigma := by
  have hm : 0 < min sigma (r/4) := lt_min hs (by positivity)
  have hc : 0 < refinementCells (min sigma (r/4)) := Nat.ceil_pos.mpr (by positivity)
  have hcR : (0 : Real) < refinementCells (min sigma (r/4)) := by exact_mod_cast hc
  unfold coreAnchorAgreementDensity
  positivity

theorem coreAnchorAgreementDomain_uniform_density {N k g d : Nat} [NeZero N]
    (P Gamma D : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (x : ZMod N → ZMod N) {a : ZMod N} {r sigma t : Real}
    (hr : 0 < r) (hs : 0 < sigma)
    (hD : D.card ≤ k) (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hx : x a ∈ columnShiftBases P a) (hpopular : t*N ≤ ((columnShiftBases P a).card : Real)) :
    coreAnchorAgreementDensity t k g d r sigma*(N : Real)^2 ≤
      (coreAnchorAgreementDomain P Gamma D T x a r sigma).card := by
  have hm : 0 < min sigma (r/4) := lt_min hs (by positivity)
  let Q := refinementCells (min sigma (r/4))
  have hQ : 0 < Q := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  have hcell : 1 ≤ min sigma (r/4)*(Q : Real) := by
    have hc : 1/min sigma (r/4) ≤ (Q : Real) := Nat.le_ceil _
    simpa only [mul_comm] using (div_le_iff₀ hm).mp hc
  have h := coreAnchorAgreementDomain_density P Gamma D T x hD hG hT hx hpopular hcell
  unfold coreAnchorAgreementDensity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : (0 : Real) < (Q : Real)^(k+g+4*d))).mpr
  simpa only [mul_comm] using h

end LeanProofs.GowersSzemeredi

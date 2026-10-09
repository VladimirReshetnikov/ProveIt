import GowersSzemeredi.Proofs16VarietyExplicitExponent

/-! Actual multilinear covers with ceiling-free variety-lift controls. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16VarietyCeilingFreeGraphBound (Q : Nat) (theta gamma rho : Real) : Real :=
  let r := section16Lemma9R (theta / 2) gamma 2
  let u := (multipleC ((rho / 4) / (2 * r)) gamma 3)^r
  max (81 * (7 / ((rho / 4) * u))^4 * (Q : Real)^2) 27

def section16VarietyCeilingFreeExponent (C p Cv pv D Q q : Nat)
    (c theta gamma E rho : Real) : Real :=
  let r := section16Lemma9R (theta / 2) gamma 2
  let u := (multipleC ((rho / 4) / (2 * r)) gamma 3)^r
  let z := section16Zeta (theta / 2) gamma 2 / (4 * ((C * (q + 1) : Nat) : Real))
  (u * E / (8 * (p : Real) * ((q : Real) + 1)^16)) *
    (((rho / 4) * u)^17 /
      (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
        (7^17 * ((Q : Real) + 1)^17))) / (16 + 4 * Real.log (16 / z))

theorem section16VarietyCeilingFreeExponent_pos {C p Cv pv D Q q : Nat}
    (hC : 2 ≤ C) (hp : 0 < p) (hpv : 0 < pv) {c theta gamma E rho : Real}
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hE : 0 < E)
    (hr : 0 < rho) (hr1 : rho ≤ 1) :
    0 < section16VarietyCeilingFreeExponent C p Cv pv D Q q c theta gamma E rho := by
  let r := section16Lemma9R (theta / 2) gamma 2
  let u := (multipleC ((rho / 4) / (2 * r)) gamma 3)^r
  let z := section16Zeta (theta / 2) gamma 2 / (4 * ((C * (q + 1) : Nat) : Real))
  have hu : 0 < u := (section16_variety_sampling_controls ht ht1 hg hg1
    (by positivity : 0 < rho / 4) (by linarith : rho / 4 ≤ 1)).1
  obtain ⟨hZ, hZ1⟩ := section16Zeta_pos_le_half 2
    (by positivity : 0 < theta / 2) (by linarith : theta / 2 ≤ 1) hg hg1
  have hCpos : 0 < C := by omega
  have hz : 0 < z := div_pos hZ (by positivity)
  have hz1 : z ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hsize : (1 : Real) ≤ ((C * (q + 1) : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ C * (q + 1) by nlinarith)
    linarith
  have hlog : 0 ≤ Real.log (16 / z) := Real.log_nonneg ((one_le_div hz).mpr (by linarith))
  have hbase := two_le_milicevic_base hc hc1
  have hB : 0 ≤ milicevicBound D c := pow_nonneg (by linarith) D
  change 0 < (u * E / (8 * (p : Real) * ((q : Real) + 1)^16)) *
    (((rho / 4) * u)^17 /
      (1024 * (pv : Real)^2 * (4 * Cv + 18) * (milicevicBound D c + 2)^17 *
        (7^17 * ((Q : Real) + 1)^17))) / (16 + 4 * Real.log (16 / z))
  apply div_pos _ (by positivity)
  exact mul_pos (div_pos (mul_pos hu hE) (by positivity))
    (div_pos (pow_pos (mul_pos (by positivity) hu) 17) (by positivity))

/-- Transfer the bounds to the actual covers, preserving their mass and
partition properties on every box. -/
theorem MultiplyLinearWith.variety_ceiling_free_controls {N C p Cv pv D Q q : Nat}
    [NeZero N] {c theta gamma E : Real} {Gamma : Finset (Point N 3 × ZMod N)}
    (h : MultiplyLinearWith
      (fun rho => max (section16VarietyLiftGraphBound Q (theta / 2) gamma rho) 27)
      (fun rho => section16CappedWidthExponent
        (section16PolynomialVarietyLiftExponent p Cv pv D Q c (theta / 2) gamma
          (fun _ => (q : Real)) (fun _ => E) rho)
        (section16PolynomialVarietyLiftThreshold C p Cv pv D Q c (theta / 2) gamma
          (fun _ => (q : Real)) (fun _ => E) rho)) Gamma)
    (hC : 2 ≤ C) (hCv : 2 ≤ Cv) (hp : 0 < p) (hpv : 0 < pv)
    (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hE : 0 < E) (hE1 : E ≤ 1) :
    MultiplyLinearWith (section16VarietyCeilingFreeGraphBound Q theta gamma)
      (section16VarietyCeilingFreeExponent C p Cv pv D Q q c theta gamma E) Gamma := by
  apply h.weaken
  · intro rho hr hr1
    have hbound := (section16_variety_sample_budget Cv D Q hpv hc hc1 ht ht1 hg hg1
      (by positivity : 0 < rho / 4) (by linarith : rho / 4 ≤ 1)).1
    rw [show 4 * (rho / 4) = rho by ring] at hbound
    exact max_le_max hbound le_rfl
  · intro rho hr hr1
    exact section16VarietyCeilingFreeExponent_pos hC hp hpv hc hc1 ht ht1 hg hg1 hE hr hr1
  · intro rho hr hr1
    have hbound := section16_variety_lift_exponent_lower C Cv D Q q hC hCv hp hpv
      hc hc1 ht ht1 hg hg1 (by positivity : 0 < rho / 4)
      (by linarith : rho / 4 ≤ 1) hE hE1
    rw [show 4 * (rho / 4) = rho by ring] at hbound
    exact hbound

end LeanProofs.GowersSzemeredi

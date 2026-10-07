import GowersSzemeredi.Proofs16GoodDomainTransport

/-! Solve the alternating cube identity for its all-ones vertex with the
actual parity signs. This proves the identity required by Lemma 16.9. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section16_phi_one_cube_identity {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (x0 : Point N k) (z : Point N (k + 1)) :
    section16PhiOne phi x0 z =
      (-1 : ZMod N) ^ k * section16CubeValueAtBase phi x0 (section16Init z) (section16Last z) +
        section16PhiRemainder phi x0 z := by
  classical
  let e1 : Fin k → Bool := fun _ => true
  let f : (Fin k → Bool) → ZMod N := fun e =>
    (-1 : ZMod N) ^ (k + boolWeight e) * section16TranslatedVertex phi x0 e z
  have hw : boolWeight e1 = k := by simp [boolWeight, countWhere, e1]
  have he : f e1 = section16PhiOne phi x0 z := by
    dsimp only [f]
    rw [hw, ← two_mul, pow_mul]
    simp [section16TranslatedVertex, section16PhiOne, e1]
  have hs : (-1 : ZMod N) ^ k *
      section16CubeValueAtBase phi x0 (section16Init z) (section16Last z) = ∑ e, f e := by
    unfold section16CubeValueAtBase
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [f, pow_add, section16TranslatedVertex, mul_assoc]
  have hfilter : (Finset.univ.filter fun e : Fin k → Bool => e ≠ e1) = Finset.univ.erase e1 := by
    ext e
    simp
  have hr : section16PhiRemainder phi x0 z = -∑ e ∈ Finset.univ.erase e1, f e := by
    unfold section16PhiRemainder
    change -(∑ e ∈ Finset.univ.filter (fun e => e ≠ e1), f e) = _
    rw [hfilter]
  rw [hs, hr, ← Finset.sum_erase_add _ _ (Finset.mem_univ e1), he]
  ring

/-- The common-base conclusion of Lemma 16.7 supplies the exact alternating
identity used in the line-cover construction, without an additional premise. -/
theorem section16_phi_one_identity_of_common_base {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) (phiPrime : Point N k → ZMod N → ZMod N)
    (hvalue : ∀ z, Section16GoodInducedPair B H Y x0 z →
      phiPrime z.1 z.2 = section16CubeValueAtBase phi x0 z.1 z.2) :
    Section16PhiOneIdentity (section16GoodDomain B H Y x0) phi x0 phiPrime := by
  classical
  intro z hz
  have hh := hvalue (section16Init z, section16Last z) (Finset.mem_filter.mp hz).2
  rw [section16_phi_one_cube_identity]
  change _ = (-1 : ZMod N) ^ k * phiPrime (section16Init z) (section16Last z) + _
  rw [hh]

end LeanProofs.GowersSzemeredi

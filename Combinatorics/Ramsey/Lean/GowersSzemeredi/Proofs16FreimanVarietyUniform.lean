import GowersSzemeredi.Proofs16FreimanVarietyCover

/-! Uniform controls from rank and radius bounds for Freiman varieties.

Increasing the permitted ranks and decreasing the radius weakens the
positive all-box exponent. This removes the actual variety parameters
from the cover controls when a structure theorem bounds them uniformly.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Capping is monotone in the exponent and antitone in the threshold. -/
theorem section16CappedWidthExponent_mono {e e' T T' : Real}
    (he : e ≤ e') (hT : T' ≤ T) :
    section16CappedWidthExponent e T ≤ section16CappedWidthExponent e' T' := by
  unfold section16CappedWidthExponent
  apply min_le_min he
  have hpos : (0 : Real) < max 2 T' := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hlog := Real.log_le_log hpos (max_le_max le_rfl hT)
  exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num))
    (Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))) hlog

theorem section16FreimanVarietyDegree_mono {p s S r R : Nat} (hs : s ≤ S) (hr : r ≤ R) :
    section16FreimanVarietyDegree p s r ≤ section16FreimanVarietyDegree p S R := by
  unfold section16FreimanVarietyDegree
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 8))
    (Nat.mul_le_mul_left p (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 8))

theorem section16FreimanVarietyExponent_antitone {p s S r R : Nat}
    (hp : 0 < p) (hs : s ≤ S) (hr : r ≤ R) :
    section16FreimanVarietyExponent p S R ≤ section16FreimanVarietyExponent p s r := by
  have hpos := section16FreimanVarietyDegree_pos hp s r
  unfold section16FreimanVarietyExponent
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.mul_le_mul_left 2 (section16FreimanVarietyDegree_mono hs hr)

theorem section16FreimanVarietyThreshold_mono {C p s S r R : Nat} {rho delta : Real}
    (hC : 0 < C) (hs : s ≤ S) (hr : r ≤ R) (hd : 0 < delta) (hdr : delta ≤ rho) :
    section16FreimanVarietyThreshold C p s r rho ≤
      section16FreimanVarietyThreshold C p S R delta := by
  have hbase : max (C * (s + r + 1)) (Nat.ceil (16 / rho)) ≤
      max (C * (S + R + 1)) (Nat.ceil (16 / delta)) := by
    apply max_le_max
    · exact Nat.mul_le_mul_left C (by omega)
    · exact Nat.ceil_mono (div_le_div_of_nonneg_left (by norm_num) hd hdr)
  have hpos : 0 < max (C * (S + R + 1)) (Nat.ceil (16 / delta)) :=
    (Nat.mul_pos hC (by omega)).trans_le (le_max_left _ _)
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right hpos (Nat.mul_le_mul_left 2 (section16FreimanVarietyDegree_mono hs hr)))

/-- Rank upper bounds and a positive radius lower bound give a common
positive exponent for all the corresponding variety covers. -/
theorem section16FreimanVarietyControl_mono {C p s S r R : Nat} {rho delta : Real}
    (hC : 0 < C) (hp : 0 < p) (hs : s ≤ S) (hr : r ≤ R)
    (hd : 0 < delta) (hdr : delta ≤ rho) :
    section16CappedWidthExponent (section16FreimanVarietyExponent p S R)
      (section16FreimanVarietyThreshold C p S R delta) ≤
    section16CappedWidthExponent (section16FreimanVarietyExponent p s r)
      (section16FreimanVarietyThreshold C p s r rho) := by
  apply section16CappedWidthExponent_mono (section16FreimanVarietyExponent_antitone hp hs hr)
  exact_mod_cast section16FreimanVarietyThreshold_mono hC hs hr hd hdr

/-- Uniform all-box controls depend only on rank and radius bounds. -/
theorem exists_uniform_freiman_variety_cover :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (Gamma Psi : Finset (ZMod N)) (r S R : Nat)
    (L : Fin r → ZMod N → ZMod N) (rho delta : Real),
    0 < delta → delta ≤ rho → Gamma.card + Psi.card ≤ S → r ≤ R →
    (∀ i, IsFreimanLinearOn (bohr Psi rho) (L i)) →
    ∀ Phi : ZMod N × ZMod N → ZMod N,
      IsEBihomomorphism (bilinearBohrVariety Gamma Psi L rho) Phi {0} →
    ∀ G : Finset (Point N 2 × ZMod N),
      IsGraphOver G (bilinearBohrVariety Gamma Psi L (rho / 2)) Phi →
      MultiplyLinearWith (fun _ => 9)
        (fun _ => section16CappedWidthExponent
          (section16FreimanVarietyExponent p S R)
          (section16FreimanVarietyThreshold C p S R delta)) G := by
  obtain ⟨C, p, hC, hp, hcover⟩ := exists_freiman_variety_cover
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ _ Gamma Psi r S R L rho delta hd hdr hs hr hL Phi hPhi G hG
  apply (hcover N Gamma Psi r L rho (hd.trans_le hdr) hL Phi hPhi G hG).weaken
  · intros; exact le_rfl
  · intros
    exact section16CappedWidthExponent_pos (section16FreimanVarietyExponent_pos hp S R)
  · intros
    exact section16FreimanVarietyControl_mono (by omega) hp hs hr hd hdr

end LeanProofs.GowersSzemeredi

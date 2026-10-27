import DiophantineConsistency.NativePellBootstrap

/-! The free-J adaptive carrier permits 3 to divide q. This signed integer
cancellation loses at most one factor q, without assuming gcd(q,H)=1,
positivity, a restored source, or a Pell index. Only finite polynomial
identities and integer division are used. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveFactorThree

/-- A literal finite geometric inverse modulo q^4. -/
theorem cancel_four_of_unit_residue {q B d t : ℤ}
    (hB : B = 1+q*d) (hd : q^4 ∣ B*t) : q^4 ∣ t := by
  obtain ⟨w,hw⟩ := hd
  refine ⟨(1-q*d+q^2*d^2-q^3*d^3)*w+d^4*t, ?_⟩
  calc
    t = (1-q*d+q^2*d^2-q^3*d^3)*(B*t)+q^4*d^4*t := by rw [hB]; ring
    _ = q^4*((1-q*d+q^2*d^2-q^3*d^3)*w+d^4*t) := by rw [hw]; ring

/-- Explicit Bezout coefficients for q and 3, without a prime-factor oracle. -/
theorem bezout_three {q : ℤ} (h : ¬ (3 : ℤ) ∣ q) :
    ∃ a b : ℤ, a*q+b*3=1 := by
  have hz : q%3 ≠ 0 := fun he => h (Int.dvd_of_emod_eq_zero he)
  have hr : q%3=1 ∨ q%3=2 := by omega
  have he := Int.emod_add_ediv_mul q 3
  rcases hr with hr | hr
  · exact ⟨1,-(q/3),by omega⟩
  · exact ⟨-1,q/3+1,by omega⟩

/-- The factor-three loss is uniform over all signed integers. No numerical
positivity, mask condition, source-index equation or auxiliary norm is used. -/
theorem cancel_factor_three {q Y X t : ℤ}
    (hY : q^3 ∣ Y) (hd : q^5 ∣ (4*Y*(X+1)+3)*t) : q^4 ∣ t := by
  obtain ⟨s,hs⟩ := hY
  let H : ℤ := 4*Y*(X+1)+3
  have hH : H = 3+q^3*(4*s*(X+1)) := by dsimp [H]; rw [hs]; ring
  by_cases h3 : (3 : ℤ) ∣ q
  · obtain ⟨a,ha⟩ := h3
    let B : ℤ := 1+36*a^3*s*(X+1)
    have hB : B=1+q*(12*a^2*s*(X+1)) := by dsimp [B]; rw [ha]; ring
    have hHB : H=3*B := by rw [hH,ha]; dsimp [B]; ring
    obtain ⟨w,hw⟩ := hd
    have he : (3 : ℤ)*(B*t)=3*(q^4*(a*w)) := by
      calc
        3*(B*t)=H*t := by rw [hHB]; ring
        _ = q^5*w := hw
        _ = 3*(q^4*(a*w)) := by rw [ha]; ring
    have hc : B*t=q^4*(a*w) := mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) he
    exact cancel_four_of_unit_residue hB ⟨a*w,hc⟩
  · obtain ⟨a,b,hab⟩ := bezout_three h3
    have hB : b*H=1+q*(b*q^2*(4*s*(X+1))-a) := by
      calc
        b*H=(a*q+b*3)+q*(b*q^2*(4*s*(X+1))-a) := by rw [hH]; ring
        _ = 1+q*(b*q^2*(4*s*(X+1))-a) := by rw [hab]
    have hpow : q^4 ∣ q^5 := ⟨q,by ring⟩
    have hc : q^4 ∣ (b*H)*t := by
      obtain ⟨w,hw⟩ := dvd_trans hpow hd
      refine ⟨b*w,?_⟩
      calc
        (b*H)*t=b*(H*t) := by ring
        _ = q^4*(b*w) := by rw [hw]; ring
    exact cancel_four_of_unit_residue hB hc

/-- The actual adaptive main-norm transport restores the stronger index
congruence after the first carrier has supplied q^3 dividing Y. -/
theorem index_difference_dvd {q Y X v : ℤ} (hY : q^3 ∣ Y)
    (hd : q^5 ∣ (4*Y*(X+1)+3)*(q*X*Y-v)) : q^4 ∣ v := by
  have hc := cancel_factor_three hY hd
  have he : q^4 ∣ q*X*Y := by
    obtain ⟨s,hs⟩ := hY
    exact ⟨X*s,by rw [hs]; ring⟩
  simpa only [sub_sub_cancel] using dvd_sub he hc

end DiophantineConsistency.NativeAdaptiveFactorThree

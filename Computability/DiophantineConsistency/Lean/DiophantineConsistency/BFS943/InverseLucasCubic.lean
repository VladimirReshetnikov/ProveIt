import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.BFS943.Trace80Parity

/-! # The inverse-Lucas cubic correction inside a model of IΣ₁

Package 172's inverse charts replace the offset `k - R - 1` by
`e* = k - R - 1 - v k (k² - 4) / 6`, with `k = 2 ψ_{1+2v}(m)`. This module
proves, for arbitrary internal indices, the arithmetic behind that correction:

* `second_order`: at the Pell base `b + 2 = 2P + 1` (`b + 1 = 2P`), by internal
  induction, `x_n = 1 + 2P n² + P² W` and `y_n = n + 4P C + P² Z` with
  `6 C + n = n³` (so `C = binom(n+1, 3)`); only the residue modulo `P²` is
  used, not the sign or size of `Z`;
* `cubic_split`: then `6 (k + Δ) - P k (k² - 4) = 6 u` and
  `3 u = 3 (2n + Δ) + P² w` for integral `u, w` (`k = 2 y_n`, any `Δ`); this
  is the identity `3 (e* - d₀) = 4 v² [24 Z_m - A_m S_m]` of the package proof
  with the denominator cleared;
* `cancel_three`: `q^(m+1) ∣ 3 x ⇒ q^m ∣ x` (both when `3 ∣ q` and when `q² ≡ 1
  (mod 3)`), the step `ord_l(e* - d₀) ≥ 6 a_l - ord_l 3`;
* `pow2_cancel_signed_odd`: a power of two cancels against any signed odd factor
  `2 m + 1`;
* `positive_carrier_signed`: the carrier coordinate `n` at a signed offset
  quotient `ρ` (`Trace76ReverseData.positive_carrier_weight` with `ρ` in the
  difference ring). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace InverseLucasCubic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Second-order expansion of the Pell pair at base `b + 2 = 2P + 1`. -/
theorem second_order (b P n : V) (hb : b+1=2*P) :
    ∃ C T W Z : V, 6*C+n=n*n*n ∧ 2*T=n*n+n ∧
      xcoord n b=1+2*P*(n*n)+P*P*W ∧ ycoord n b=n+4*P*C+P*P*Z := by
  have hbase : b+2=2*P+1 := by
    calc b+2=(b+1)+1 := by ring
      _=2*P+1 := by rw [hb]
  have hd : delta b=4*P*P+4*P := by
    unfold delta
    calc (b+1)*(b+3)=(b+1)*((b+1)+2) := by ring
      _=4*P*P+4*P := by rw [hb]; ring
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,0,0,0,by simp,by simp,by simp,by simp⟩
  case succ n ih =>
    obtain ⟨C,T,W,Z,hC,hT,hx,hy⟩ := ih
    refine ⟨C+T,T+n+1,W+4*(n*n)+2*P*W+4*n+16*P*C+4*P*P*Z+16*C+4*P*Z,
      W+8*C+2*P*Z+Z,?_,?_,?_,?_⟩
    · calc 6*(C+T)+(n+1)=(6*C+n)+3*(2*T)+1 := by ring
        _=(n+1)*(n+1)*(n+1) := by rw [hC,hT]; ring
    · calc 2*(T+n+1)=2*T+2*n+2 := by ring
        _=(n+1)*(n+1)+(n+1) := by rw [hT]; ring
    · rw [x_succ,hx,hy,hbase,hd]; ring
    · rw [y_succ,hx,hy,hbase]
      calc 1+2*P*(n*n)+P*P*W+(2*P+1)*(n+4*P*C+P*P*Z)
          =(n+1)+4*P*C+2*P*(n*n+n)+P*P*(W+8*C+2*P*Z+Z) := by ring
        _=(n+1)+4*P*(C+T)+P*P*(W+8*C+2*P*Z+Z) := by rw [←hT]; ring

theorem three_cases (a : V) : ∃ t : V, a=3*t ∨ a=3*t+1 ∨ a=3*t+2 := by
  induction a using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,Or.inl (by simp)⟩
  case succ a ih =>
    obtain ⟨t,h|h|h⟩ := ih
    · exact ⟨t,Or.inr (Or.inl (by rw [h]))⟩
    · exact ⟨t,Or.inr (Or.inr (by rw [h]; ring))⟩
    · exact ⟨t+1,Or.inl (by rw [h]; ring)⟩

theorem cube_three (d : V) : ∃ t : V, d*d*d=d+3*t := by
  induction d using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,by simp⟩
  case succ d ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨t+d*d+d,?_⟩
    calc (d+1)*(d+1)*(d+1)=d*d*d+3*(d*d)+3*d+1 := by ring
      _=d+3*t+3*(d*d)+3*d+1 := by rw [ht]
      _=(d+1)+3*(t+d*d+d) := by ring

/-- The cubic correction is a multiple of `6`, and its quotient agrees with the
first-order offset `2 n + Δ` modulo `P²`, up to the factor `3`. -/
theorem cubic_split (n C Z P y : V) (Δ : DiffRing V)
    (hC : 6*C+n=n*n*n) (hy : y=n+4*P*C+P*P*Z) :
    ∃ u w : DiffRing V,
      6*(2*(ι y:DiffRing V)+Δ)-ι P*(2*ι y)*((2*ι y)*(2*ι y)-4)=6*u ∧
      3*u=3*(2*(ι n:DiffRing V)+Δ)+ι P*ι P*w := by
  obtain ⟨t,ht⟩ := cube_three (P*(4*C+P*Z))
  have hyR : (ι y:DiffRing V)=ι n+ι P*(4*ι C+ι P*ι Z) := by
    rw [hy]; simp only [map_add,map_mul,map_ofNat]; ring
  have hCR : 6*(ι C:DiffRing V)+ι n=ι n*ι n*ι n := by
    have h := congrArg (ι : V →+* DiffRing V) hC
    simpa only [map_add,map_mul,map_ofNat] using h
  have htR : (ι P*(4*ι C+ι P*ι Z))*(ι P*(4*ι C+ι P*ι Z))*(ι P*(4*ι C+ι P*ι Z))=
      (ι P*(4*ι C+ι P*ι Z):DiffRing V)+3*ι t := by
    have h := congrArg (ι : V →+* DiffRing V) ht
    simpa only [map_add,map_mul,map_ofNat] using h
  refine ⟨2*ι y+Δ-4*ι P*(2*ι C+(ι P*(4*ι C+ι P*ι Z))*
      (ι n*ι n+ι n*(ι P*(4*ι C+ι P*ι Z)))+ι t),
    6*ι Z-12*(4*ι C+ι P*ι Z)*(ι n*ι n+ι n*(ι P*(4*ι C+ι P*ι Z)))-
      4*(4*ι C+ι P*ι Z)*((ι P*(4*ι C+ι P*ι Z))*(ι P*(4*ι C+ι P*ι Z))-1),?_,?_⟩
  · rw [hyR]; linear_combination 8*ι P*hCR-8*ι P*htR
  · rw [hyR]; linear_combination 4*ι P*htR

/-- `cubic_split` at the Pell ordinate itself. -/
theorem pell_cubic_split (b P n : V) (Δ : DiffRing V) (hb : b+1=2*P) :
    ∃ u w : DiffRing V,
      6*(2*(ι (ycoord n b):DiffRing V)+Δ)-
          ι P*(2*ι (ycoord n b))*((2*ι (ycoord n b))*(2*ι (ycoord n b))-4)=6*u ∧
      3*u=3*(2*(ι n:DiffRing V)+Δ)+ι P*ι P*w := by
  obtain ⟨C,_T,_W,Z,hC,_hT,_hx,hy⟩ := second_order b P n hb
  exact cubic_split n C Z P (ycoord n b) Δ hC hy

theorem one_add_three_pow {R : Type*} [CommRing R] (s : R) :
    ∀ j : ℕ, ∃ S : R, (1+3*s)^j=1+3*S
  | 0 => ⟨0,by simp⟩
  | j+1 => by
    obtain ⟨S,hS⟩ := one_add_three_pow s j
    exact ⟨S+s+3*S*s,by rw [pow_succ,hS]; ring⟩

theorem cancel_three_of_unit (qq x s : DiffRing V) (m : ℕ) (hq2 : qq^2=1+3*s)
    (hd : qq^(m+1)∣3*x) : qq^m∣x := by
  obtain ⟨y,hy⟩ := hd
  have h3 : (3:DiffRing V)≠0 := ne_of_gt (by norm_num)
  obtain ⟨S,hS⟩ := one_add_three_pow s (m+1)
  have hpow : qq^(m+1)*qq^(m+1)=1+3*S := by
    rw [←mul_pow,←sq,hq2]; exact hS
  have hy3 : y=3*(x*qq^(m+1)-S*y) := by
    linear_combination (-(qq^(m+1)))*hy-y*hpow
  refine ⟨qq*(x*qq^(m+1)-S*y),?_⟩
  apply mul_left_cancel₀ h3
  linear_combination hy+qq^(m+1)*hy3

/-- `q^(m+1) ∣ 3 x ⇒ q^m ∣ x` in the difference ring. -/
theorem cancel_three (q0 : V) (x : DiffRing V) (m : ℕ)
    (hd : (ι q0:DiffRing V)^(m+1)∣3*x) : (ι q0:DiffRing V)^m∣x := by
  have h3 : (3:DiffRing V)≠0 := ne_of_gt (by norm_num)
  obtain ⟨t,ht|ht|ht⟩ := three_cases q0
  · obtain ⟨y,hy⟩ := hd
    have hq : (ι q0:DiffRing V)=3*ι t := by rw [ht]; simp only [map_mul,map_ofNat]
    refine ⟨ι t*y,?_⟩
    apply mul_left_cancel₀ h3
    rw [hy,hq]; ring
  · apply cancel_three_of_unit (ι q0) x (3*ι t*ι t+2*ι t) m _ hd
    rw [ht]; simp only [map_add,map_mul,map_ofNat,map_one]; ring
  · apply cancel_three_of_unit (ι q0) x (3*ι t*ι t+4*ι t+1) m _ hd
    rw [ht]; simp only [map_add,map_mul,map_ofNat,map_one]; ring

/-- A power of two cancels against a signed odd factor. -/
theorem pow2_cancel_signed_odd (P : V) (m e : DiffRing V) (hP : Pow2 P)
    (hd : (ι P:DiffRing V)∣(2*m+1)*e) : (ι P:DiffRing V)∣e := by
  have hdisc : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
  have hnot : ∀ c : DiffRing V, 2*c≠1 := by
    intro c hc
    rcases _root_.le_or_gt c 0 with h|h
    · linarith
    · have := hdisc c h; linarith
  rcases nonneg_or_nonpos (2*m+1) with ⟨a,ha⟩|⟨a,ha⟩
  · have hodd : ¬ (2:V)∣a := by
      rintro ⟨c,hc⟩
      apply hnot (ι c-m)
      have hh : (ι a:DiffRing V)=2*ι c := by rw [hc]; simp only [map_mul,map_ofNat]
      linear_combination -ha-hh
    rw [ha] at hd
    exact Trace80Parity.pow2_cancel_odd P a e hP hodd hd
  · have hodd : ¬ (2:V)∣a := by
      rintro ⟨c,hc⟩
      apply hnot (-ι c-m)
      have hh : (ι a:DiffRing V)=2*ι c := by rw [hc]; simp only [map_mul,map_ofNat]
      linear_combination -ha+hh
    rw [ha,neg_mul] at hd
    exact Trace80Parity.pow2_cancel_odd P a e hP hodd ((dvd_neg).mp hd)

/-- The carrier coordinate at a signed offset quotient `ρ`. -/
theorem positive_carrier_signed (b D H Kpos t kappa L tau f y : V) (rho : DiffRing V)
    (hK : Kpos=H*kappa) (hbig : (ι kappa:DiffRing V)-rho<ι (tau*f*y)) :
    ∃ n : V, 0<n ∧
      ((ι b:DiffRing V)*ι D)*(ι H*(ι n-ι L*(ι b*ι t))+ι Kpos)-
        ι H*((ι D)*(ι b*ι t)+ι b*((ι D)*rho)) =
      (ι b*ι D*ι H)*(ι tau*ι f*ι y) := by
  let x : DiffRing V := ι (tau*f*y)+ι L*(ι b*ι t)+ι t+rho-ι kappa
  have hx : 0<x := by
    have h1 : (0:DiffRing V)≤ι L*(ι b*ι t)+ι t := by
      rw [←map_mul,←map_mul,←map_add]; exact ι_nonneg _
    dsimp [x]; linarith
  obtain ⟨n,hn⟩ := nonneg_iff.mp (le_of_lt hx)
  have hnpos : 0<n := ι_lt_ι.mp (by rw [map_zero]; rwa [hn] at hx)
  have hKR := congrArg (ι : V →+* DiffRing V) hK
  simp only [map_mul] at hKR
  refine ⟨n,hnpos,?_⟩
  rw [hKR,←hn]
  dsimp [x]
  simp only [map_mul]
  ring

#print axioms InverseLucasCubic.second_order
#print axioms InverseLucasCubic.pell_cubic_split
#print axioms InverseLucasCubic.cancel_three
#print axioms InverseLucasCubic.pow2_cancel_signed_odd
#print axioms InverseLucasCubic.positive_carrier_signed
end InverseLucasCubic

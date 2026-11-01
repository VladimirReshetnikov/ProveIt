import DiophantineConsistency.AdaptiveGap85ThresholdAuxiliarySeed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85DoubleThreshold
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85ThresholdArithmetic
open AdaptiveGap85ThresholdSeed AdaptiveGap85ThresholdOuter
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem auxiliary_T_exceeds_twice_cube (c I f T u R : V)
    (hc : 0<c) (hI : 2*c*c≤I) (hf : f*f≤2*I*I) (hu : I^4≤u)
    (he : f*f*c*T=u+c+f*f*R) : 2*c^3<T := by
  have hI2 : (2*c*c)*(2*c*c)≤I*I := mul_le_mul hI hI (by simp) (by simp)
  have hc4 : 4*c^4≤I*I := by
    calc
      _=(2*c*c)*(2*c*c) := by ring
      _≤_ := hI2
  have hstrict : I^4<f*f*c*T := by
    rw [he]
    exact lt_of_le_of_lt hu (lt_of_lt_of_le (lt_add_of_pos_right u hc) (by simp))
  by_contra hn
  have hT : T≤2*c^3 := le_of_not_gt hn
  have hupper : f*f*c*T≤I^4 := calc
    _≤f*f*c*(2*c^3) := mul_le_mul_of_nonneg_left hT (by simp)
    _≤(2*I*I)*c*(2*c^3) := by gcongr
    _=(I*I)*(4*c^4) := by ring
    _≤(I*I)*(I*I) := mul_le_mul_of_nonneg_left hc4 (by simp)
    _=I^4 := by ring
  exact (not_le_of_gt hstrict) hupper

theorem auxiliary_T_exceeds_two_shifts (b q Y c I f T u R : V)
    (hc : 0<c) (hq : 1≤q) (hb : b≤q) (hY : Y≤c) (hq3 : q^3≤c)
    (hI : 2*c*c≤I) (hf : f*f≤2*I*I) (hu : I^4≤u)
    (he : f*f*c*T=u+c+f*f*R) :
    let D := b*(Y*(q*q))*(q*q-1)
    D+D<T := by
  let D := b*(Y*(q*q))*(q*q-1)
  have hD : D≤c^3 := shift_decrement_le_cube b q Y c hq hb hY hq3
  have h2 : D+D≤2*c^3 := by
    calc
      _≤c^3+c^3 := add_le_add hD hD
      _=2*c^3 := by ring
  exact lt_of_le_of_lt h2 (auxiliary_T_exceeds_twice_cube c I f T u R hc hI hf hu he)

theorem full_seed_exceeds_two_shifts (a R b s eta zeta f i T u : V)
    (hR : 5 ≤ R) (hs : 0 < s) (heta : 0 < eta) (hzeta : 0 < zeta)
    (hi : 0 < i) (hf : 0 < f)
    (hc : let q := 1+b; let Y := s*q^3; eta+Y*(eta+zeta)=ycoord R a)
    (hn : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      f*f=1+delta a*(i*c*c)*(i*c*c))
    (hux : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      let I := delta a*i*c*c; xcoord R (I-2)=I*u)
    (he : let q := 1+b; let Y := s*q^3; let c := eta+Y*(eta+zeta);
      f*f*c*T=u+c+f*f*R) :
    let q := 1+b; let Y := s*q^3; let D := b*(Y*(q*q))*(q*q-1); D+D<T := by
  let q := 1+b
  let Y := s*q^3
  let c := eta+Y*(eta+zeta)
  let I := delta a*i*c*c
  have hq : (1:V)≤q := by dsimp [q]; exact le_add_of_nonneg_right (by simp)
  have hb : b≤q := by dsimp [q]; exact le_add_of_nonneg_left (by simp)
  have ⟨hq3,hY⟩ := outer_seed_lower_bounds q s eta zeta hs heta hzeta
  change c=ycoord R a at hc
  have hc0 : 0<c := by
    rw [hc]
    exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0:V)<5) hR) (time_le_y R a)
  have hnorm : I*I+delta a=delta a*(f*f) := by
    calc
      I*I+delta a=delta a*(1+delta a*(i*c*c)*(i*c*c)) := by dsimp [I]; ring
      _=delta a*(f*f) := by rw [←hn]
  obtain ⟨hI,hfbound⟩ := strong_seed_estimates a c i f I hc0 hi hf rfl hnorm
  have hc1 : 1≤c := pos_iff_one_le.mp hc0
  have hc2 : (1:V)≤c*c := one_le_mul hc1 hc1
  have hI2 : 2≤I := calc
    (2:V)=2*1 := by ring
    _≤2*(c*c) := mul_le_mul_of_nonneg_left hc2 (by simp)
    _=2*c*c := by ring
    _≤I := hI
  have hu : I^4≤u := odd_quotient_growth I R u hI2 hR hux
  exact auxiliary_T_exceeds_two_shifts b q Y c I f T u R hc0 hq hb hY hq3 hI hfbound hu he
/-- The checked auxiliary seed can be chosen above the two-shift threshold.
The outer coordinate and phase hypotheses remain explicit. -/
theorem auxiliary_seed_with_two_shifts (a R b s eta zeta : V)
    (hR : 5≤R) (hphase : R%4=3) (hs : 0<s) (heta : 0<eta) (hzeta : 0<zeta)
    (hc : let q := 1+b; let Y := s*q^3; eta+Y*(eta+zeta)=ycoord R a) :
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      (let c := ycoord R a; f*f=1+delta a*(i*c*c)*(i*c*c)) ∧
      (let c := ycoord R a; let I := delta a*i*c*c; y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u) ∧
      f*f*(ycoord R a)*T=u+(ycoord R a)+f*f*R ∧
      (let q := 1+b; let Y := s*q^3; let D := b*(Y*(q*q))*(q*q-1); D+D<T) := by
  obtain ⟨f,i,T,u,y,hf,hi,hT,hu,hy,_,_,hn,hye,hux,_,_,_,he,_,_⟩ :=
    ArithmeticPellAuxiliarySeed.auxiliary_seed a R hphase
  have hthreshold := full_seed_exceeds_two_shifts a R b s eta zeta f i T u hR hs heta hzeta hi hf hc
    (by simpa only [hc] using hn) (by simpa only [hc] using hux) (by simpa only [hc] using he)
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hn,⟨hye,hux⟩,he,hthreshold⟩
end DiophantineConsistency.AdaptiveGap85DoubleThreshold

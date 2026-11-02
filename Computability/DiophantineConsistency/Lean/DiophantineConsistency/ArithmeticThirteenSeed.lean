import DiophantineConsistency.ArithmeticPellAuxiliarySeed
import DiophantineConsistency.ArithmeticPellPigeonhole
import DiophantineConsistency.ArithmeticOddOrdinateResidue
/-! # Fresh thirteen-coordinate Pell seeds in every model of `𝗜𝚺₁`

Internal counterpart of `ThirteenFreshSeed.auxiliary_exists`. The maintained
`ArithmeticPellAuxiliarySeed.auxiliary_seed` takes its strong seed at index
`R·c`; the thirteen-coordinate carrier needs a strong ordinate divisible by
`b·c²` for an arbitrary internal `b`. `ArithmeticPellPigeonhole.ordinate_dvd`
supplies such an index, and `auxiliary_seed_of` repeats the auxiliary
construction from any index `t` with `ycoord t a = i·c·c`. The signed
auxiliary ordinate is `≡ -1` modulo `4I²` by `ArithmeticOddOrdinateResidue.pair`,
because `R ≡ 3 (mod 4)` makes `(R-1)/2` odd. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.ArithmeticThirteenSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellAuxiliarySeed

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A strong index whose ordinate is a positive multiple of `b·c²`. -/
theorem strong_index (a b c : V) (hb : 0 < b) (hc : 0 < c) :
    ∃ t j : V, 0 < t ∧ 0 < j ∧ ycoord t a = (b*j)*c*c := by
  obtain ⟨t, ht, ⟨j, hj⟩⟩ := ArithmeticPellPigeonhole.ordinate_dvd a (b*c*c)
    (mul_pos (mul_pos hb hc) hc)
  have hy : 0 < ycoord t a := lt_of_lt_of_le ht (time_le_y t a)
  have hj0 : 0 < j := by
    rcases eq_zero_or_pos j with h0 | h0
    · rw [h0, mul_zero] at hj; rw [hj] at hy; exact absurd hy (_root_.lt_irrefl 0)
    · exact h0
  exact ⟨t, j, ht, hj0, by rw [hj]; ring⟩

/-- Complete positive auxiliary witnesses from any strong index. -/
theorem auxiliary_seed_of (a R t i : V) (hphase : R % 4 = 3) (hi : 0 < i)
    (hyt : ycoord t a = i*ycoord R a*ycoord R a) :
    let c:=ycoord R a
    let f:=xcoord t a
    ∃ T u y : V, 0<f ∧ 0<T ∧ 0<u ∧ 0<y ∧
      f*f=1+delta a*(i*c*c)*(i*c*c) ∧
      let I:=delta a*i*c*c
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      f*f*c*T=u+c+f*f*R ∧ u=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*u*u+y*y=1+I*I*y*y ∧ (y+1)%(4*I*I)=0 := by
  let c:=ycoord R a
  obtain ⟨hR,hodd,hhalf⟩ := phase_indices R hphase
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
  let f:=xcoord t a
  have hf : 0<f := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x t a)
  have hn : f*f=1+delta a*(i*c*c)*(i*c*c) := by
    have h := norm t a
    change xcoord t a*xcoord t a=1+delta a*ycoord t a*ycoord t a at h
    rw [hyt] at h
    exact h
  let I:=delta a*i*c*c
  have hd : 2≤delta a := by
    unfold delta
    calc
      (2:V)≤a+3 := le_trans (le_of_lt (by
        simpa only [show (2:V)+1=3 by ring] using lt_add_one (2:V))) (by simp)
      _≤(a+1)*(a+3) := le_mul_of_one_le_left (by simp) (by simp)
  have hi1 : 1≤ i*c*c := one_le_mul (one_le_mul (pos_iff_one_le.mp hi)
    (pos_iff_one_le.mp hc)) (pos_iff_one_le.mp hc)
  have hI : 2≤I := le_trans hd (by
    simpa only [I,mul_assoc] using le_mul_of_one_le_right (by simp : (0:V)≤delta a) hi1)
  have hb : I-2+2=I := tsub_add_cancel_of_le hI
  have hnorm : I*I+delta a=delta a*f*f := by
    calc
      I*I+delta a=delta a*(1+delta a*(i*c*c)*(i*c*c)) := by dsimp [I]; ring
      _=delta a*f*f := by rw [←hn]; ring
  have hIc : c∣I := ⟨delta a*i*c,by dsimp [I]; ring⟩
  let u:=oddQuotient ((R-1)/2) (I-2)
  let y:=ycoord R (I-2)
  have hux : xcoord R (I-2)=I*u := by
    simpa only [u, ←hodd,hb] using odd_exact ((R-1)/2) (I-2)
  have hu : 0<u := by
    apply pos_of_mul_pos_right (a := I) _ (by simp)
    rw [←hux]
    exact lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x R (I-2))
  have hy : 0<y := lt_of_lt_of_le hR (time_le_y R (I-2))
  have hphaseindex : 2*(2*(R/4)+1)+1=R := by
    calc
      2*(2*(R/4)+1)+1=2*((R-1)/2)+1 := by rw [hhalf]
      _=R := hodd.symm
  have huf : (u+c)%(f*f)=0 := by
    simpa only [u,hhalf,hphaseindex] using (quotient_square_pair a I f (R/4) hI hf hnorm).2
  have huc : (u+R)%c=0 := by
    have hh := (quotient_divisor_pair I c (R/4) hI hc hIc).2
    have hfour : 4*(R/4)+3=R := by simpa only [hphase] using div_add_mod R 4
    simpa only [u,hhalf,hfour] using hh
  have hfc : f*f=1+c*(delta a*i*i*c*c*c) := by rw [hn]; ring
  obtain ⟨T,hT,hliteral,habsolute⟩ := positive_quotient c f R u _ hc hu hfc huf huc
  have hdelta : delta (I-2)+1=I*I := by
    calc
      delta (I-2)+1=(I-2+2)*(I-2+2) := by unfold delta; ring
      _=I*I := by rw [hb]
  have haux : I*I*u*u+y*y=1+I*I*y*y := by
    have hh := norm R (I-2)
    change xcoord R (I-2)*xcoord R (I-2)=1+delta (I-2)*y*y at hh
    calc
      I*I*u*u+y*y=(I*u)*(I*u)+y*y := by ring
      _=1+(delta (I-2)+1)*y*y := by rw [←hux,hh]; ring
      _=1+I*I*y*y := by rw [hdelta]
  have hres : (y+1)%(4*I*I)=0 := by
    have h := (ArithmeticOddOrdinateResidue.pair (I-2) (R/4)).2
    rw [hphaseindex, hb] at h
    simpa only [mul_assoc] using h
  exact ⟨T,u,y,hf,hT,hu,hy,hn,rfl,hux,hliteral,habsolute,haux,hres⟩

end DiophantineConsistency.ArithmeticThirteenSeed

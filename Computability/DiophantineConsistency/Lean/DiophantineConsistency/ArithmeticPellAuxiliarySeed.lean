import DiophantineConsistency.ArithmeticPellSquaredSeed
import DiophantineConsistency.ArithmeticPellHalfIndex

/-! Positive fourteen-variable auxiliary witnesses in arbitrary IΣ1 models.
The negative residue phase is retained modulo f² and the actual ordinate.
Outer simultaneous witnesses and the polynomial/HA composition are separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellAuxiliarySeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellResidueClasses
open ArithmeticPellHalfIndex ArithmeticPellSquaredSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord oddQuotient

/-- The two phases modulo the full square, at every internal block index. -/
theorem quotient_square_pair (a I f t : V) (hI : 2≤I) (hf : 0<f)
    (hn : I*I+delta a=delta a*f*f) :
    oddQuotient (2*t) (I-2) % (f*f)=ycoord (2*(2*t)+1) a % (f*f) ∧
    (oddQuotient (2*t+1) (I-2)+ycoord (2*(2*t+1)+1) a) % (f*f)=0 := by
  let b:=I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hm : 0<f*f := mul_pos hf hf
  have hcoef : (4*(b+2)*(b+2)+4*(a+2)*(a+2))%(f*f)=(4:V)%(f*f) := by
    have he : 4*(b+2)*(b+2)+4*(a+2)*(a+2)=4+(f*f)*(4*delta a) := by
      rw [hb]
      calc
        4*I*I+4*(a+2)*(a+2)=4+4*(I*I+delta a) := by unfold delta; ring
        _=4+(f*f)*(4*delta a) := by rw [hn]; ring
    rw [he,mod_add_mul' _ _ hm]
  have hfirst : (oddQuotient 1 b+ycoord 3 a)%(f*f)=0 := by
    have he : oddQuotient 1 b+ycoord 3 a=(f*f)*(4*delta a) := by
      apply add_right_cancel (b:=(4:V))
      calc
        (oddQuotient 1 b+ycoord 3 a)+4=
            (oddQuotient 1 b+3)+(ycoord 3 a+1) := by ring
        _=4*I*I+4*(a+2)*(a+2) := by rw [ArithmeticPellHalfIndex.odd_one,y_three,hb]
        _=(f*f)*(4*delta a)+4 := by
          calc
            4*I*I+4*(a+2)*(a+2)=4*(I*I+delta a)+4 := by unfold delta; ring
            _=(f*f)*(4*delta a)+4 := by rw [hn]; ring
    rw [he,mod_mul_self_right]
  change oddQuotient (2*t) b%(f*f)=ycoord (2*(2*t)+1) a%(f*f) ∧
    (oddQuotient (2*t+1) b+ycoord (2*(2*t+1)+1) a)%(f*f)=0
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
    constructor
    · simp only [mul_zero,zero_add,odd_zero,hy1]
    · simpa only [mul_zero,zero_add,show (2:V)*1+1=3 by ring] using hfirst
  case succ t ih =>
    have h2 := transport_equal (f*f) (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
      _ _ _ _ _ _ hm hcoef (odd_rec (2*t) b) (odd_y_rec (2*t) a) ih.1 ih.2
    have h3 := transport_opposite (f*f) (4*(b+2)*(b+2)) (4*(a+2)*(a+2))
      _ _ _ _ _ _ hm hcoef (odd_rec (2*t+1) b) (odd_y_rec (2*t+1) a) ih.2
      (by simpa only [add_assoc,one_add_one_eq_two] using h2)
    constructor
    · simpa only [show 2*(t+1)=2*t+2 by ring] using h2
    · simpa only [show 2*(t+1)+1=(2*t+1)+2 by ring] using h3

/-- The same negative phase represents the index modulo any ordinate divisor. -/
theorem quotient_divisor_pair (I c t : V) (hI : 2≤I) (hc : 0<c) (hd : c∣I) :
    oddQuotient (2*t) (I-2)%c=(4*t+1)%c ∧
    (oddQuotient (2*t+1) (I-2)+(4*t+3))%c=0 := by
  let b:=I-2
  have hb : b+2=I := tsub_add_cancel_of_le hI
  have hd4 : c∣4*I*I := by
    obtain ⟨v,hv⟩ := hd
    exact ⟨4*v*I,by rw [hv]; ring⟩
  have hcoef : (4*(b+2)*(b+2)+4)%c=(4:V)%c := by
    rw [hb]
    exact mod_add_remove_left_of_dvd hd4 hc
  have hfirst : (oddQuotient 1 b+3)%c=0 := by
    rw [ArithmeticPellHalfIndex.odd_one,hb]
    exact mod_eq_zero_iff_dvd.mpr hd4
  have linear_rec (h : V) :
      (2*(h+2)+1)+(2*h+1)+2*(2*(h+1)+1)=4*(2*(h+1)+1) := by ring
  have pair (t : V) : oddQuotient (2*t) b%c=(2*(2*t)+1)%c ∧
      (oddQuotient (2*t+1) b+(2*(2*t+1)+1))%c=0 := by
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      constructor
      · simp only [mul_zero,zero_add,odd_zero]
      · simpa only [mul_zero,zero_add,show (2:V)*1+1=3 by ring] using hfirst
    case succ t ih =>
      have h2 := transport_equal c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*t) b) (linear_rec (2*t)) ih.1 ih.2
      have h3 := transport_opposite c (4*(b+2)*(b+2)) 4
        _ _ _ _ _ _ hc hcoef (odd_rec (2*t+1) b) (linear_rec (2*t+1)) ih.2
        (by simpa only [add_assoc,one_add_one_eq_two] using h2)
      constructor
      · simpa only [show 2*(t+1)=2*t+2 by ring] using h2
      · simpa only [show 2*(t+1)+1=(2*t+1)+2 by ring] using h3
  simpa only [show 2*(2*t)+1=4*t+1 by ring,
    show 2*(2*t+1)+1=4*t+3 by ring] using pair t

theorem phase_indices (R : V) (hphase : R%4=3) :
    0<R ∧ R=2*((R-1)/2)+1 ∧ (R-1)/2=2*(R/4)+1 := by
  have he : R=4*(R/4)+3 := by simpa only [hphase] using (div_add_mod R 4).symm
  have ho : R=2*(2*(R/4)+1)+1 := he.trans (by ring)
  have hh : (R-1)/2=2*(R/4)+1 := by
    calc
      (R-1)/2=(2*(2*(R/4)+1)+1-1)/2 := congrArg (fun r : V => (r-1)/2) ho
      _=2*(R/4)+1 := by simp
  exact ⟨by rw [he]; simp,by rw [hh]; exact ho,hh⟩

/-- Positive literal T from the two actual residues. No CRT or coprimality
premise is needed; f²=1+c*H supplies the exact divisible-summand removal. -/
theorem positive_quotient (c f R u H : V) (hc : 0<c) (hu : 0<u)
    (hfc : f*f=1+c*H) (huf : (u+c)%(f*f)=0) (huc : (u+R)%c=0) :
    ∃ T : V, 0<T ∧ f*f*c*T=u+c+f*f*R ∧
      u=absdiff (f*f*c*T) (f*f*R+c) := by
  obtain ⟨o,ho⟩ := mod_eq_zero_iff_dvd.mp huf
  have ho0 : 0<o := by
    apply pos_of_mul_pos_right (a := f*f) _ (by simp)
    rw [←ho]
    exact add_pos hu hc
  have hsum : (u+c+R)%c=0 := by
    simpa only [show u+c+R=u+R+c by ring, mod_add_remove_right hc] using huc
  have hco : (o+R)%c=0 := by
    have he : u+c+R=(o+R)+c*(H*o) := by rw [ho,hfc]; ring
    rw [he,mod_add_mul' _ _ hc] at hsum
    exact hsum
  let T:V := (o+R)/c
  have hT : c*T=o+R := mul_div_self_of_dvd.mpr (mod_eq_zero_iff_dvd.mp hco)
  have hTp : 0<T := by
    apply pos_of_mul_pos_right (a := c) _ (by simp)
    rw [hT]
    exact lt_of_lt_of_le ho0 (by simp)
  have hliteral : f*f*c*T=u+c+f*f*R := by
    calc
      f*f*c*T=(f*f)*(c*T) := by ring
      _=(f*f)*(o+R) := by rw [hT]
      _=(f*f)*o+f*f*R := by ring
      _=u+c+f*f*R := by rw [←ho]
  have horder : f*f*R+c≤f*f*c*T := by rw [hliteral]; simpa only [add_comm,add_left_comm,add_assoc] using (show c+f*f*R≤u+(c+f*f*R) by simp)
  refine ⟨T,hTp,hliteral,?_⟩
  rw [absdiff,tsub_eq_zero_of_le horder,add_zero,
    show f*f*c*T=(f*f*R+c)+u by rw [hliteral]; ring]
  simp

/-- Complete positive auxiliary witnesses, from only the actual rank phase.
The squared seed, both residues and the literal auxiliary norm are derived. -/
theorem auxiliary_seed (a R : V) (hphase : R%4=3) :
    let c:=ycoord R a
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
      f*f=1+delta a*(i*c*c)*(i*c*c) ∧
      let I:=delta a*i*c*c
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      u=oddQuotient ((R-1)/2) (I-2) ∧
      (u+c)%(f*f)=0 ∧ (u+R)%c=0 ∧
      f*f*c*T=u+c+f*f*R ∧ u=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let c:=ycoord R a
  obtain ⟨hR,hodd,hhalf⟩ := phase_indices R hphase
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
  obtain ⟨f,i,hf,hi,hfx,hyic,hn⟩ := strong_seed R a hR
  change ycoord (R*c) a=i*c*c at hyic
  change f*f=1+delta a*(i*c*c)*(i*c*c) at hn
  let I:=delta a*i*c*c
  have hd : 2≤delta a := by
    unfold delta
    calc
      (2:V)≤a+3 := le_trans (le_of_lt (by
        simpa only [show (2:V)+1=3 by ring] using lt_add_one (2:V))) (by simp)
      _≤(a+1)*(a+3) := le_mul_of_one_le_left (by simp) (by simp)
  have hi1 : 1≤i*c*c := one_le_mul (one_le_mul (pos_iff_one_le.mp hi)
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
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hfx,hyic,hn,rfl,hux,rfl,huf,huc,hliteral,habsolute,haux⟩

end DiophantineConsistency.ArithmeticPellAuxiliarySeed

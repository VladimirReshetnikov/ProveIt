import DiophantineConsistency.ArithmeticPellCommonUnit
import DiophantineConsistency.ArithmeticPellStrongDivisibility

/-! A positive relaxed norm and the actual large-ordinate bound force an
integral Pell solution at the original parameter. The common-unit index
multiple is derived before the original-base index is constructed.
The further c-divides-index/cubic-congruence step is not asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellIntegralSolution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization
open ArithmeticPellCommonUnit ArithmeticPellStrongDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual norm also gives the strict inequality at index zero. -/
theorem y_lt_x (b j : V) : ycoord j b<xcoord j b :=
  ArithmeticPellRecurrence.ordinate_lt_abscissa b j

theorem doubled_y_growth (b g : V) (hg : 0<g) :
    2*ycoord g b*ycoord g b<ycoord (2*g) b := by
  have hyp : 0<ycoord g b := lt_of_lt_of_le hg (time_le_y g b)
  have hprod := mul_lt_mul_of_pos_right (y_lt_x b g) hyp
  calc
    2*ycoord g b*ycoord g b=2*(ycoord g b*ycoord g b) := by ring
    _<2*(xcoord g b*ycoord g b) := mul_lt_mul_of_pos_left hprod (by simp)
    _=xcoord g b*ycoord g b+ycoord g b*xcoord g b := by ring
    _=ycoord (g+g) b := (addition g g b).2.symm
    _=ycoord (2*g) b := by congr 1; ring

/-- A proper gcd index contradicts the supplied large-c bound. Every
positivity needed for the doubling and cancellation is derived explicitly. -/
theorem large_index_multiple (b n M S T A D c : V)
    (hn : 0<n) (hM : 0<M) (hS : 0<S) (hT : 0<T)
    (hSA : S<A) (hD : D=T*S)
    (hYM : ycoord M b=S*c) (hcN : c∣T*ycoord n b)
    (hbig : A*D*D<c) : M∣n := by
  have hc : 0<c := lt_of_le_of_lt (Arithmetic.zero_le _) hbig
  have hDp : 0<D := by rw [hD]; exact mul_pos hT hS
  let g := gcdValue n M
  have hgn : g∣n := (gcd_spec n M).1
  have hgM : g∣M := (gcd_spec n M).2.1
  have hgp : 0<g := by
    obtain ⟨k, hk⟩ := hgn
    exact pos_of_mul_pos_left (by rw [← hk]; exact hn) (by simp)
  have hygp : 0<ycoord g b := lt_of_lt_of_le hgp (time_le_y g b)
  have hcM : c∣T*ycoord M b := ⟨T*S,by rw [hYM]; ring⟩
  have hcg : c∣T*ycoord g b := scaled_common_divisor b n M T c hcN hcM
  have hcle : c≤T*ycoord g b := le_of_dvd (mul_pos hT hygp) hcg
  by_contra hnd
  have hgne : g≠M := by
    intro he
    exact hnd (by simpa only [he] using hgn)
  obtain ⟨k,hk⟩ := hgM
  have hk0 : k≠0 := by
    intro hz
    simp [hz] at hk
    exact (ne_of_gt hM) hk
  have hk1 : k≠1 := by
    intro he
    apply hgne
    simpa only [he,mul_one] using hk.symm
  have hklt : 1<k := lt_of_le_of_ne (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hk0)) (Ne.symm hk1)
  have hk2 : 2≤k := by simpa only [one_add_one_eq_two] using lt_iff_succ_le.mp hklt
  have h2g : 2*g≤M := by
    rw [hk,mul_comm 2 g]
    exact Arithmetic.mul_le_mul_left hk2
  have hdouble : 2*ycoord g b*ycoord g b<S*c :=
    lt_of_lt_of_le (doubled_y_growth b g hgp)
      (by rw [←hYM]; exact (y_strictMono b).monotone h2g)
  have hTD : T≤D := by rw [hD]; exact Arithmetic.le_mul_of_pos_right hS
  have hcD : c≤D*ycoord g b := le_trans hcle (Arithmetic.mul_le_mul_right hTD)
  have hsq : c*c≤(D*ycoord g b)*(D*ycoord g b) :=
    mul_le_mul hcD hcD (Arithmetic.zero_le _) (Arithmetic.zero_le _)
  have key : (2*c)*c<(A*D*D)*c := by
    calc
      (2*c)*c≤2*((D*ycoord g b)*(D*ycoord g b)) := by
        simpa only [mul_assoc] using Arithmetic.mul_le_mul_left (a := (2:V)) hsq
      _=(D*D)*(2*ycoord g b*ycoord g b) := by ring
      _<(D*D)*(S*c) := mul_lt_mul_of_pos_left hdouble (mul_pos hDp hDp)
      _≤(D*D)*(A*c) := Arithmetic.mul_le_mul_left
        (Arithmetic.mul_le_mul_right (le_of_lt hSA))
      _=(A*D*D)*c := by ring
  have hcancel : 2*c<A*D*D := Arithmetic.lt_of_mul_lt_mul_right key
  exact (not_lt_of_ge (show c≤2*c from by simp)) (lt_trans hcancel hbig)

/-- Actual positive relaxed norm, with no supplied common-unit index,
produces an integral solution at the original parameter. -/
theorem integral_solution (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f) (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧
      i*c*c=delta a*ycoord m a := by
  have hc : 0<c := by rw [hcp]; exact lt_of_lt_of_le hp (time_le_y p a)
  have hR : 0<i*c*c := mul_pos (mul_pos hi hc) hc
  obtain ⟨b,e,n,S,hep,hnp,hSp,hSA,hS,he,hf',hD,hR',hcomp⟩ :=
    common_unit_composition a (i*c*c) f hR hf hnorm
  let T := delta b*S
  have hTp : 0<T := mul_pos (by simp [delta]) hSp
  have hDTS : delta a=T*S := hD
  have hYM : ycoord (e*p) b=S*c := by
    rw [←(hcomp p).2,←hcp]
    ring
  have hcN : c∣T*ycoord n b := by
    change c∣delta b*S*ycoord n b
    rw [←hR']
    exact ⟨i*c,by ring⟩
  have hepN : e*p∣n := large_index_multiple b n (e*p) S T (a+2) (delta a) c
    hnp (mul_pos hep hp) hSp hTp hSA hDTS hYM hcN hbig
  obtain ⟨k,hk⟩ := hepN
  let m := p*k
  have hnm : n=e*m := by rw [hk]; dsimp [m]; ring
  have hmp : 0<m :=
    pos_of_mul_pos_right (by rw [← hnm]; exact hnp) (by simp)
  refine ⟨m,hmp,⟨k,rfl⟩,?_,?_⟩
  · rw [hf',hnm,←(hcomp m).1]
  · calc
      i*c*c=delta b*S*ycoord n b := hR'
      _=delta b*S*(ycoord m a*S) := by rw [hnm,←(hcomp m).2]
      _=delta a*ycoord m a := by rw [hD]; ring

/-- Positivity of f justifies the literal truncated subtraction. -/
theorem integral_solution_tsub (a c p i f : V)
    (hp : 0<p) (hi : 0<i) (hf : 0<f) (hcp : c=ycoord p a)
    (hnorm : (i*c*c)*(i*c*c)=delta a*(f*f-1))
    (hbig : (a+2)*delta a*delta a<c) :
    ∃ m : V, 0<m ∧ p∣m ∧ f=xcoord m a ∧
      i*c*c=delta a*ycoord m a := by
  exact integral_solution a c p i f hp hi hf hcp
    (norm_tsub_to_add (delta a) f (i*c*c) hf hnorm) hbig
end DiophantineConsistency.ArithmeticPellIntegralSolution

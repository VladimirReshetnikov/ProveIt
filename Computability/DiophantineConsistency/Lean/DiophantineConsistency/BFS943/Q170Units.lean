import DiophantineConsistency.BFS943.ScaledSquare
import DiophantineConsistency.ArithmeticSquareDivisibility
import DiophantineConsistency.ArithmeticOddOrdinateResidue

/-! # Generic unit, square and residue steps of package 170's carriers

Abstract model arithmetic in every model of `𝗜𝚺₁` (and its ring of
differences), with no graph binding:

* `units_four`: in a discretely ordered ring, four factors with product one,
  three of them `≠ -1`, are all one; `three_mul_add_one_ne`: `3 B + 1 ≠ -1`;
* `square_extraction`: if `A ∣ S`, `S ≥ 2`, `|V| ≥ 1` and
  `(S² - 1) t² = A (S² V² - 1)` (`FIXED_CARRIER_PROOF.md` (5)), then
  `A = τ²`, `τ ∣ t` and `(S² - 1) y² = S² V² - 1` for `y = t / τ`
  (coprimality by explicit Bézout certificates, the square by
  `TenPositiveScaledSquare.scaled_product_factor_square`);
* `aux_residue`: the auxiliary ordinate of `S² V² - (S² - 1) y² = 1` is
  `±1 (mod 4 S²)` (internal Pell classification, odd index,
  `ArithmeticOddOrdinateResidue.odd_ordinate_pm`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Q170Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing DiscreteOrderedRingFacts ArithmeticGcdNormalization
  ArithmeticPellRecurrence ArithmeticOddOrdinateResidue

section Ring
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Four integer factors with product one, three of them not `-1`, are all one. -/
theorem units_four (hd : Discrete R) {a b c e : R} (h : a*b*c*e=1)
    (ha : a≠-1) (hb : b≠-1) (he : e≠-1) : a=1 ∧ b=1 ∧ c=1 ∧ e=1 := by
  have ha1 : a=1 := by
    rcases eq_one_or_neg_one_of_mul_eq_one hd (show a*(b*c*e)=1 by rw [←h]; ring) with h1|h1
    · exact h1
    · exact absurd h1 ha
  subst ha1
  have hb1 : b=1 := by
    rcases eq_one_or_neg_one_of_mul_eq_one hd (show b*(c*e)=1 by rw [←h]; ring) with h1|h1
    · exact h1
    · exact absurd h1 hb
  subst hb1
  have he1 : e=1 := by
    rcases eq_one_or_neg_one_of_mul_eq_one hd (show e*c=1 by rw [←h]; ring) with h1|h1
    · exact h1
    · exact absurd h1 he
  subst he1
  exact ⟨rfl,rfl,by simpa using h,rfl⟩

theorem three_mul_add_one_ne (hd : Discrete R) (B : R) : 3*B+1≠-1 := by
  intro h
  rcases lt_trichotomy B 0 with hB|hB|hB
  · have := hd (-B) (by linarith)
    linarith
  · subst hB
    norm_num at h
  · have := hd B hB
    linarith

end Ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b≤a) : ι (a-b)=ι a-ι b := by
  rw [eq_sub_iff_add_eq,←map_add,tsub_add_cancel_of_le h]

theorem ι_absdiff (a b : V) : ι (ArithmeticPellHalfIndex.absdiff a b)=|ι a-ι b| := by
  unfold ArithmeticPellHalfIndex.absdiff
  rcases le_total b a with h|h
  · rw [tsub_eq_zero_of_le h,add_zero,ι_tsub h,
      abs_of_nonneg (sub_nonneg.mpr (ι_le_ι.mpr h))]
  · rw [tsub_eq_zero_of_le h,zero_add,ι_tsub h,
      abs_of_nonpos (sub_nonpos.mpr (ι_le_ι.mpr h)),neg_sub]

/-- **Square extraction** (`FIXED_CARRIER_PROOF.md` §3). -/
theorem square_extraction (S A Vb T0 : V) (hS : 2≤S) (hA : 0<A) (hAS : A∣S) (hV : 1≤Vb)
    (h : (S*S-1)*(T0*T0)=A*(S*S*Vb*Vb-1)) :
    ∃ tau y : V, 0<tau ∧ A=tau*tau ∧ T0=tau*y ∧ (S*S-1)*(y*y)=S*S*Vb*Vb-1 := by
  obtain ⟨s1,rfl⟩ := hAS
  have hS1 : 1≤A*s1*(A*s1) := le_trans (by norm_num) (le_trans hS
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans (by norm_num) hS)))
  have hVV : 1≤Vb*Vb := one_le_mul hV hV
  have hS4 : 4≤A*s1*(A*s1) := by
    simpa only [show (2:V)*2=4 by norm_num] using mul_le_mul hS hS (by simp) (by simp)
  have hSV : 1+Vb*Vb≤A*s1*(A*s1)*Vb*Vb := by
    calc
      1+Vb*Vb≤Vb*Vb+Vb*Vb := add_le_add hVV le_rfl
      _≤4*(Vb*Vb) := by
          rw [show (4:V)*(Vb*Vb)=Vb*Vb+Vb*Vb+(Vb*Vb+Vb*Vb) by ring]
          exact le_add_of_nonneg_right (Arithmetic.zero_le _)
      _≤A*s1*(A*s1)*(Vb*Vb) := mul_le_mul_of_nonneg_right hS4 (Arithmetic.zero_le _)
      _=A*s1*(A*s1)*Vb*Vb := by ring
  have hDy1 : 1≤A*s1*(A*s1)*Vb*Vb := le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) hSV
  -- the coprimality certificate `(S² - 1)(S² V² - 1) = 1 + A K`
  let K : V := A*s1*s1*(A*s1*(A*s1)*Vb*Vb-(1+Vb*Vb))
  have hK : (A*s1*(A*s1)-1)*(A*s1*(A*s1)*Vb*Vb-1)=1+A*K := by
    apply ι_injective
    simp only [K,map_mul,map_add,map_one,ι_tsub hS1,ι_tsub hDy1,ι_tsub hSV]
    ring
  have hu : Bez A ((A*s1*(A*s1)-1)*(A*s1*(A*s1)*Vb*Vb-1)) 1 :=
    ⟨K,0,0,1,by rw [hK]; ring⟩
  obtain ⟨g,hg⟩ := TenPositiveScaledSquare.scaled_product_factor_square (A*s1*(A*s1)-1) T0 1 A
    (A*s1*(A*s1)*Vb*Vb-1) (by simp) hu (by rw [h]; ring)
  have hg0 : 0<g := by
    rcases eq_zero_or_pos g with h0|h0
    · rw [h0,mul_zero] at hg; exact absurd hg (ne_of_gt hA)
    · exact h0
  have hbez : Bez (A*s1*(A*s1)-1) A 1 := by
    refine ⟨1,0,0,A*s1*s1,?_⟩
    rw [mul_one,mul_zero,add_zero,mul_zero,zero_add,add_tsub_cancel_of_le hS1]
    ring
  have hA2 : A∣T0*T0 := unit_certificate_cancel hbez ⟨_,h⟩
  have hgg : g*g∣T0*T0 := hg ▸ hA2
  obtain ⟨y,hy⟩ := ArithmeticSquareDivisibility.dvd_of_square_dvd g T0 hg0 hgg
  refine ⟨g,y,hg0,hg,hy,?_⟩
  apply mul_left_cancel₀ (ne_of_gt (mul_pos hg0 hg0))
  calc
    g*g*((A*s1*(A*s1)-1)*(y*y))=(A*s1*(A*s1)-1)*(T0*T0) := by rw [hy]; ring
    _=A*(A*s1*(A*s1)*Vb*Vb-1) := h
    _=g*g*(A*s1*(A*s1)*Vb*Vb-1) := by rw [hg]

/-- **The auxiliary ordinate is `±1` modulo `4 S²`.** -/
theorem aux_residue (S Vb y : V) (hS : 2≤S) (h : (S*S-1)*(y*y)=S*S*Vb*Vb-1)
    (hV : 1≤S*S*Vb*Vb) :
    Cong (4*S*S) y 1 ∨ Cong (4*S*S) y (-1) := by
  obtain ⟨b,rfl⟩ : ∃ b, S=b+2 := ⟨S-2,(tsub_add_cancel_of_le hS).symm⟩
  have hdelta : (b+2)*(b+2)-1=delta b := by
    unfold delta
    rw [show (b+2)*(b+2)=(b+1)*(b+3)+1 by ring,add_tsub_cancel_right]
  have hn : ((b+2)*Vb)*((b+2)*Vb)=1+delta b*y*y := by
    rw [←hdelta,mul_assoc (_-1),h,show (b+2)*Vb*((b+2)*Vb)=(b+2)*(b+2)*Vb*Vb by ring]
    exact (add_tsub_cancel_of_le hV).symm
  obtain ⟨n,_,hx,hyn⟩ := ArithmeticPellClassification.solution_index b _ _ hn
  obtain ⟨k,rfl⟩ := ArithmeticPellResidueClasses.odd_index_witness b n
    (by rw [hx]; exact dvd_mul_right _ _)
  have hm := odd_ordinate_pm b k
  rw [hyn] at hm
  exact hm

#print axioms Q170Units.units_four
#print axioms Q170Units.three_mul_add_one_ne
#print axioms Q170Units.square_extraction
#print axioms Q170Units.aux_residue
end Q170Units

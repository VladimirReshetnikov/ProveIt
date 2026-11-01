import DiophantineConsistency.AdaptiveGap85NegativeModular
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85NegativeSmallCases
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85NegativeModular
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The bounded negative-template cases reduce to q=2, Y=8t, 1≤t≤6,
or q=3, Y=27, uniformly in arbitrary IΣ₁ models. -/
theorem bounded_cube_cases (q Y : V) (hq : 2≤q) (hY : 8≤Y)
    (hYlt : Y<54) (hq3 : q*q*q∣Y) :
    (q=2 ∧ ∃ t : V, 1≤t ∧ t≤6 ∧ Y=8*t) ∨ (q=3 ∧ Y=27) := by
  have hYpos : 0<Y := lt_of_lt_of_le (by simp) hY
  have hcube : q*q*q≤Y := Arithmetic.le_of_dvd hYpos hq3
  have hq3le : q≤3 := by
    by_contra hn
    have hq3lt : 3<q := lt_of_not_ge hn
    have hq4 : 4≤q := by simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp hq3lt
    have h64 : (64:V)≤q*q*q := by
      have h16 : (16:V)≤q*q := by
        have hh := mul_le_mul hq4 hq4 (by simp) (by simp)
        calc
          _ = 4*4 := by ring
          _ ≤ _ := hh
      have hh := mul_le_mul h16 hq4 (by simp) (by simp)
      calc
        _ = 16*4 := by ring
        _ ≤ _ := hh
    have h54 : (54:V)<64 := by
      have hh : (54:V)<54+10 := lt_add_of_pos_right _ (by simp)
      simpa only [show (54:V)+10=64 by ring] using hh
    exact (lt_asymm (lt_of_le_of_lt hcube hYlt) (lt_of_lt_of_le h54 h64)).elim
  have hcases : q=2 ∨ q=3 := by
    by_cases he : q=2
    · exact Or.inl he
    · right
      have hlt : 2<q := lt_of_le_of_ne hq (Ne.symm he)
      have h3 : 3≤q := by simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp hlt
      exact le_antisymm hq3le h3
  obtain ⟨t,ht⟩ := hq3
  have htpos : 0<t := by
    apply pos_iff_ne_zero.mpr
    intro he
    have : Y=0 := by rw [ht,he]; simp
    exact (ne_of_gt hYpos) this
  have ht1 : 1≤t := by simpa using lt_iff_succ_le.mp htpos
  rcases hcases with hq2 | hq3'
  · left
    refine ⟨hq2,t,ht1,?_,?_⟩
    · by_contra hn
      have hlt : 6<t := lt_of_not_ge hn
      have h7 : 7≤t := by simpa only [show (6:V)+1=7 by ring] using lt_iff_succ_le.mp hlt
      have hy8 : Y=8*t := by rw [ht,hq2]; ring
      have h56 : (56:V)≤Y := by
        rw [hy8]
        have hh := Arithmetic.mul_le_mul_left (a:=(8:V)) h7
        calc
          _ = 8*7 := by ring
          _ ≤ _ := hh
      have h54 : (54:V)<56 := by
        have hh : (54:V)<54+2 := lt_add_of_pos_right _ (by simp)
        simpa only [show (54:V)+2=56 by ring] using hh
      exact (lt_asymm (lt_of_le_of_lt h56 hYlt) h54).elim
    · rw [ht,hq2]; ring
  · right
    refine ⟨hq3',?_⟩
    have ht2not : ¬2≤t := by
      intro ht2
      have hy27 : Y=27*t := by rw [ht,hq3']; ring
      have h54 : (54:V)≤Y := by
        rw [hy27]
        have hh := Arithmetic.mul_le_mul_left (a:=(27:V)) ht2
        calc
          _ = 27*2 := by ring
          _ ≤ _ := hh
      exact (not_lt_of_ge h54) hYlt
    have htlt : t<2 := lt_of_not_ge ht2not
    have ht1' : t≤1 := by
      apply (add_le_add_iff_right (1:V)).mp
      simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp htlt
    have hteq : t=1 := le_antisymm ht1' ht1
    rw [ht,hq3',hteq]; ring

/-- Under the balanced negative-root equation and q³∣Y, only these small
parameter cases remain in any IΣ₁ model. -/
theorem negative_template_cases (X Y q L : V) (hq : 2≤q) (hY : 8≤Y)
    (hq3 : q*q*q∣Y)
    (hneg : (Y*q*q)*(4*(Y*(X+1))*(Y*(X+1))*(Y*(X+1))+
      24*(Y*(X+1))*(Y*(X+1))+45*(Y*(X+1))+26)+
      (Y*q*q)*(X+(Y*(X+1))*(4*((Y*(X+1))*(Y*(X+1))+4*(Y*(X+1))+3)+3)) =
      (4*(Y*(X+1))+3)*L) :
    (q=2 ∧ ∃ t : V, 1≤t ∧ t≤6 ∧ Y=8*t) ∨ (q=3 ∧ Y=27) := by
  have hqY : q∣Y := by
    obtain ⟨v,hv⟩ := hq3
    refine ⟨q*q*v, ?_⟩
    calc
      Y = q*q*q*v := hv
      _ = q*(q*q*v) := by ring
  have hY1 : 1≤Y := le_trans (by simpa only [show (1:V)+7=8 by ring] using (show (1:V)≤1+7 by simp)) hY
  exact bounded_cube_cases q Y hq hY (negative_template_Y_lt_54 X Y q L hY1 hqY hneg) hq3
end DiophantineConsistency.AdaptiveGap85NegativeSmallCases

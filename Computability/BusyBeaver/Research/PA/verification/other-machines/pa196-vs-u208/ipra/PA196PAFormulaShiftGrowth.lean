import PA196PATermShiftGrowth

/-! Numeric growth of arithmetic formula shifting in every IΣ₁ model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PAFormulaShiftGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem lift_shift {p P y : V} (hp : p + 2 ≤ P)
    (hy : y ≤ tau (3*p + 8) (22*p + 30)) :
    y ≤ tau (3*P + 8) (22*P + 24) := by
  have hp' : p ≤ P := le_trans le_self_add hp
  apply le_trans hy
  apply tau_mono (add_le_add (mul_le_mul' le_rfl hp') le_rfl)
  calc 22*p + 30 ≤ 22*p + 44 := add_le_add le_rfl (by norm_num)
    _ = 22*(p+2) := by ring
    _ ≤ 22*P := mul_le_mul' le_rfl hp
    _ ≤ 22*P + 24 := le_self_add

private theorem rel_bound {tag k r v P : V} (ht : tag ≤ 1)
    (hk : k ≤ P) (hr : r ≤ P) (hv : v ≤ P) :
    ⟪tag,k,r,termShiftVec ℒₒᵣ k v⟫ + 1 ≤ tau (3*P+8) (22*P+30) := by
  apply le_trans (PA196PATermShiftGrowth.relation_le tag k r v ht)
  apply tau_mono
  · calc v + k + r + 8 ≤ P + P + P + 8 := add_le_add (add_le_add (add_le_add hv hk) hr) le_rfl
      _ = 3*P+8 := by ring
  · calc 20*v + 2*k + 26 ≤ 20*P + 2*P + 26 :=
          add_le_add (add_le_add (mul_le_mul' le_rfl hv) (mul_le_mul' le_rfl hk)) le_rfl
      _ ≤ 22*P+30 := by
        have h : (26 : V) ≤ 30 := by norm_num
        simpa [show 20*P + 2*P = 22*P by ring] using add_le_add (le_refl (22*P)) h

private theorem const_bound (tag P : V) (ht : tag ≤ 8) :
    ⟪tag, (0 : V)⟫+1 ≤ tau (3*P+8) (22*P+30) := by
  have hc := code2_le_tau
    (le_trans (le_trans ht le_add_self) (le_tau (3*P+8) 0))
    (le_trans (show (0:V) ≤ 3*P+8 from zero_le) (le_tau (3*P+8) 0))
  apply le_trans hc
  apply tau_mono le_rfl
  have h : (2 : V) ≤ 30 := by norm_num
  simpa using (le_trans h (le_add_self (a := (30:V)) (b := 22*P)))

theorem shift_le : ∀ p : V, IsUFormula ℒₒᵣ p →
    shift ℒₒᵣ p ≤ tau (3*p+8) (22*p+30) := by
  refine IsUFormula.ISigma1.sigma1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k r v hr hv
    rw [shift_rel hr hv]
    simpa [qqRel, numeral_eq_natCast] using
      (rel_bound (tag := (0:V)) (P := ^rel k r v) (by simp)
        (arity_lt_rel k r v).le (r_lt_rel k r v).le (v_lt_rel k r v).le)
  · intro k r v hr hv
    rw [shift_nrel hr hv]
    simpa [qqNRel, numeral_eq_natCast] using
      (rel_bound (tag := (1:V)) (P := ^nrel k r v) (by simp)
        (arity_lt_nrel k r v).le (r_lt_nrel k r v).le (v_lt_nrel k r v).le)
  · rw [shift_verum]
    simpa [qqVerum, numeral_eq_natCast] using const_bound (2:V) (^⊤ : V) (by norm_num)
  · rw [shift_falsum]
    simpa [qqFalsum, numeral_eq_natCast] using const_bound (3:V) (^⊥ : V) (by norm_num)
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq]
    set P := p ^⋏ q
    have hnp := lift_shift (add_two_le_and_left p q) ihp
    have hnq := lift_shift (add_two_le_and_right p q) ihq
    have h := code3_le_tau (le_tau_of' 4 hnp) hnp hnq
    apply le_trans (by simpa [qqAnd] using h)
    apply tau_mono le_rfl
    exact le_trans (le_of_eq (by ring : 22*P+24+2+2 = 22*P+28)) (add_le_add le_rfl (by norm_num))
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq]
    set P := p ^⋎ q
    have hnp := lift_shift (add_two_le_or_left p q) ihp
    have hnq := lift_shift (add_two_le_or_right p q) ihq
    have h := code3_le_tau (le_tau_of' 5 hnp) hnp hnq
    apply le_trans (by simpa [qqOr] using h)
    apply tau_mono le_rfl
    exact le_trans (le_of_eq (by ring : 22*P+24+2+2 = 22*P+28)) (add_le_add le_rfl (by norm_num))
  · intro p hp ihp
    rw [shift_all hp]
    set P := ^∀ p
    have hnp := lift_shift (add_two_le_all p) ihp
    have h := code2_le_tau (le_tau_of' 6 hnp) hnp
    apply le_trans (by simpa [qqAll] using h)
    apply tau_mono le_rfl
    exact le_trans (le_of_eq (by ring : 22*P+24+2 = 22*P+26)) (add_le_add le_rfl (by norm_num))
  · intro p hp ihp
    rw [shift_exs hp]
    set P := ^∃ p
    have hnp := lift_shift (add_two_le_exs p) ihp
    have h := code2_le_tau (le_tau_of' 7 hnp) hnp
    apply le_trans (by simpa [qqExs] using h)
    apply tau_mono le_rfl
    exact le_trans (le_of_eq (by ring : 22*P+24+2 = 22*P+26)) (add_le_add le_rfl (by norm_num))

#print axioms shift_le
end PA196PAFormulaShiftGrowth

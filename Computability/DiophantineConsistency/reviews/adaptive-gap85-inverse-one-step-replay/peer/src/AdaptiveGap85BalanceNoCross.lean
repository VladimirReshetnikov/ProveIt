import DiophantineConsistency.AdaptiveGap85BalanceModel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceNoCross
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85BalanceModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A nonzero forward balance shift cannot land in the positive reverse gap. -/
theorem gap_forces_t_zero (p : Fin 4 → ℕ) (v : Fin 13 → V) (t : V)
    (_hb : 0<v 0*(p 0:V)) (hF : 0<v 1)
    (hg : shift p v t 1+shift p v t 2<1+v 0*(p 0:V)) : t=0 := by
  let b : V := v 0*(p 0:V)
  have hfirst : shift p v t 1<1+b := lt_of_le_of_lt (by simp) hg
  by_contra hn
  have ht : 1≤t := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hn)
  have hbt : b≤b*t := le_mul_of_one_le_right (by simp) ht
  have hf : 1≤v 1 := pos_iff_one_le.mp hF
  have hge : 1+b≤shift p v t 1 := by
    change 1+b≤v 1+b*t
    exact add_le_add hf hbt
  exact (not_le_of_gt hfirst) hge

/-- One forward balance shift reaches a positive gap tuple exactly when the
starting positive tuple already has the gap; the only such shift is zero. -/
theorem single_balance_gap_iff_start (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<v 0*(p 0:V)) (hv : ∀j,0<v j) :
    (∃ t, (∀j,0<shift p v t j) ∧
      shift p v t 1+shift p v t 2<1+v 0*(p 0:V)) ↔
    v 1+v 2<1+v 0*(p 0:V) := by
  constructor
  · rintro ⟨t,_,hg⟩
    have ht := gap_forces_t_zero p v t hb (hv 1) hg
    subst t
    simpa [shift] using hg
  · intro hg
    refine ⟨0,?_,?_⟩
    · intro i
      fin_cases i <;> simpa [shift] using hv _
    · simpa [shift] using hg
end DiophantineConsistency.AdaptiveGap85BalanceNoCross

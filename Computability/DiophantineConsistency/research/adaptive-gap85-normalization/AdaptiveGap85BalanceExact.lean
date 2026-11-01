import DiophantineConsistency.AdaptiveGap85BalanceModel
import DiophantineConsistency.AdaptiveGap85Exists
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85BalanceExact
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85BalanceModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An exact test for reaching a positive gap tuple with one forward balance
shift. It does not assert that the right-hand conditions hold at a zero. -/
theorem single_balance_gap_iff (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<v 0*(p 0:V)) (hv : ∀j,0<v j) :
    let b := v 0*(p 0:V)
    let q := 1+b
    let A := v 6+(p 1:V)*q
    let k := v 9+v 10
    let t := v 2/(q*b)
    let C := v 2%(q*b)
    (∃ t, (∀j,0<shift p v t j) ∧ shift p v t 1+shift p v t 2<q) ↔
      0<C ∧ v 1+b*t+C<q ∧ q*t*(A+1)*(b*k+1)<v 8 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let k : V := v 9+v 10
  let B : V := q*b
  let t : V := v 2/B
  let C : V := v 2%B
  have hq : 0<q := by dsimp [q]; simp
  have hB : 0<B := mul_pos hq hb
  have hb1 : 1≤b := pos_iff_one_le.mp hb
  have hqB : q≤B := le_mul_of_one_le_right (by simp) hb1
  have he : B*t+C=v 2 := div_add_mod (v 2) B
  change (∃ t, (∀j,0<shift p v t j) ∧ shift p v t 1+shift p v t 2<q) ↔
    0<C ∧ v 1+b*t+C<q ∧ q*t*(A+1)*(b*k+1)<v 8
  constructor
  · rintro ⟨s,hws,hgap⟩
    have hcpos : 0<v 2-B*s := by simpa [shift,b,q,B] using hws 2
    have hrpos : 0<v 8-q*s*(A+1)*(b*k+1) := by simpa [shift,b,q,A,k] using hws 8
    have hcsmall : v 2-B*s<q := by
      have hh : shift p v s 2≤shift p v s 1+shift p v s 2 := by simp
      change v 2-B*s≤shift p v s 1+shift p v s 2 at hh
      exact lt_of_le_of_lt hh hgap
    have hCeq : v 2-B*s=C := by
      have hdec := tsub_add_cancel_of_le (le_of_lt (tsub_pos_iff_lt.mp hcpos))
      change (v 2-B*s)+B*s=v 2 at hdec
      have hm := congrArg (fun x : V => x%B) hdec
      rw [mod_add_mul' _ _ hB,mod_eq_self_of_lt (lt_of_lt_of_le hcsmall hqB)] at hm
      exact hm
    have hs : s=t := by
      have hdec := tsub_add_cancel_of_le (le_of_lt (tsub_pos_iff_lt.mp hcpos))
      change (v 2-B*s)+B*s=v 2 at hdec
      rw [hCeq] at hdec
      have hprod : B*s=B*t := by
        apply add_left_cancel (a:=C)
        calc
          C+B*s=v 2 := hdec
          _=C+B*t := by rw [←he]; ring
      exact mul_left_cancel₀ (ne_of_gt hB) hprod
    subst s
    refine ⟨by rw [←hCeq]; exact hcpos,?_,tsub_pos_iff_lt.mp hrpos⟩
    simpa [shift,b,q,B,hCeq] using hgap
  · rintro ⟨hc,hgap,hr⟩
    have hlt : B*t<v 2 := by rw [←he]; exact lt_add_of_pos_right _ hc
    have hcsub : v 2-B*t=C := by rw [←he]; simp
    have hC : q*b*t<v 2 := hlt
    have hpos := shift_positive p v t hv hC hr
    refine ⟨t,hpos,?_⟩
    change v 1+b*t+(v 2-B*t)<q
    rw [hcsub]
    exact hgap

/-- The test gives an explicit positive bounded full zero whenever it holds. -/
theorem single_balance_normalizes_zero (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (h : let b := v 0*(p 0:V); let q := 1+b
      let A := v 6+(p 1:V)*q; let k := v 9+v 10
      let t := v 2/(q*b); let C := v 2%(q*b)
      0<C ∧ v 1+b*t+C<q ∧ q*t*(A+1)*(b*k+1)<v 8) :
    ∃ w : Fin 13 → V, (∀j,0<w j) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) w ∧
      w 1+w 2<1+w 0*(p 0:V) := by
  obtain ⟨t,ht,hgap⟩ := (single_balance_gap_iff p v hb hv).mpr h
  have hC : (1+v 0*(p 0:V))*(v 0*(p 0:V))*t<v 2 := by
    have h2 := ht 2
    change 0<v 2-(1+v 0*(p 0:V))*(v 0*(p 0:V))*t at h2
    exact tsub_pos_iff_lt.mp h2
  have hr : (1+v 0*(p 0:V))*t*
      (v 6+(p 1:V)*(1+v 0*(p 0:V))+1)*((v 0*(p 0:V))*(v 9+v 10)+1)<v 8 := by
    have h8 := ht 8
    change 0<v 8-(1+v 0*(p 0:V))*t*
      (v 6+(p 1:V)*(1+v 0*(p 0:V))+1)*((v 0*(p 0:V))*(v 9+v 10)+1) at h8
    exact tsub_pos_iff_lt.mp h8
  obtain ⟨_,hz',_⟩ := positive_zero_shift p v t hv hC hr hz
  refine ⟨shift p v t,ht,hz',?_⟩
  exact hgap
/-- Direct 85-to-86 witness construction under the explicit one-step test. -/
theorem single_balance_zero_to_86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (h : let b := v 0*(p 0:V); let q := 1+b
      let A := v 6+(p 1:V)*q; let k := v 9+v 10
      let t := v 2/(q*b); let C := v 2%(q*b)
      0<C ∧ v 1+b*t+C<q ∧ q*t*(A+1)*(b*k+1)<v 8) :
    ∃ u : Fin 13 → V, InternalZero
      (positiveShift (AdaptiveDirectOrdinate86Literal.expressionAt86 (fun j => (p j:ℤ)))) u := by
  obtain ⟨w,hw,hwz,hgap⟩ := single_balance_normalizes_zero p v hb hv hz h
  let u : Fin 13 → V := fun i => w i-1
  have hu : ∀ i, u i+1=w i := by
    intro i
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hw i))
  have huz : InternalZero (positiveShift (expressionAt85 (fun j => (p j:ℤ)))) u :=
    AdaptiveDirectOrdinate86Witness.shifted_zero_of_positive hw hwz
  have hub : (u 1+1)+(u 2+1)<1+(u 0+1)*(p 0:V) := by
    rw [hu 1,hu 2,hu 0]
    exact hgap
  exact AdaptiveGap85Exists.new_natural_zero_to_old_of_bound p u hub huz
end DiophantineConsistency.AdaptiveGap85BalanceExact

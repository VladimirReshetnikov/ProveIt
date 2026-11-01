import DiophantineConsistency.AdaptiveGap85ThirdModel

/-! The third shift at positive ports and positive coordinates. Its decrement
bounds remain explicit; this does not assert that any given zero can move. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ThirdCurrent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal AdaptiveGap85ThirdModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive port and coordinates discharge the b*A≥1 side condition. -/
theorem positive_zero_shift (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hp : 0<(p 0:V)) (hv : ∀ i,0<v i)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)<v 1)
    (hg : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let c := v 9+v 7*(v 9+v 10);
      (q*q-1)*(A+1)*c*s<v 12)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    (∀ i,0<shift p v s i) ∧
      InternalZero (expressionAt85 (fun j => (p j:ℤ))) (shift p v s) := by
  have hb : 0<v 0*(p 0:V) := mul_pos (hv 0) hp
  have hA : 0<v 6+(p 1:V)*(1+v 0*(p 0:V)) :=
    add_pos_of_pos_of_nonneg (hv 6) (by simp)
  have hBA : 1≤(v 0*(p 0:V))*(v 6+(p 1:V)*(1+v 0*(p 0:V))) :=
    pos_iff_one_le.mp (mul_pos hb hA)
  exact AdaptiveGap85ThirdModel.positive_zero_shift p v s hv hBA hF hg hz

/-- When the step parameter is positive, the F coordinate strictly decreases. -/
theorem first_strictly_decreases (p : Fin 4 → ℕ) (v : Fin 13 → V) (s : V)
    (hv : ∀ i,0<v i) (hs : 0<s)
    (hF : let b := v 0*(p 0:V); let q := 1+b;
      let A := v 6+(p 1:V)*q; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); A*(c*U*s)≤v 1) :
    shift p v s 1 < v 1 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  let U : V := v 7*(q*q)
  let c : V := v 9+v 7*(v 9+v 10)
  have hq : 0<q := by dsimp [q]; simp
  have hA : 0<A := add_pos_of_pos_of_nonneg (hv 6) (by simp)
  have hU : 0<U := mul_pos (hv 7) (mul_pos hq hq)
  have hc : 0<c := add_pos_of_pos_of_nonneg (hv 9) (by simp)
  have hd : 0<A*(c*U*s) := mul_pos hA (mul_pos (mul_pos hc hU) hs)
  have he := shifted_F_sum p v s hF
  change shift p v s 1+A*(c*U*s)=v 1 at he
  rw [←he]
  exact lt_add_of_pos_right _ hd
end DiophantineConsistency.AdaptiveGap85ThirdCurrent

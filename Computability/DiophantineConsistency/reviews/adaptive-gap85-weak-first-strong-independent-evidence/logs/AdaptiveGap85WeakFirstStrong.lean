import DiophantineConsistency.AdaptiveGap85StrongSeed

/-! A generic arithmetic family satisfying first and strong norm equations.
It is not yet a factor-literal binding or a full 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85WeakFirstStrong
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence AdaptiveGap85StrongSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Positive beta and K yield the desired first/strong arithmetic system while
violating the proposed reverse bound. -/
theorem first_strong_family (b k : V) (hb : 0<b) (hk : 0<k) :
    let q := b+1
    let F := 1+k%b
    let Y := q^3
    let a := 2*Y
    let c := a+1
    let m := q*(k+k/b)
    let B := b*m
    let r := 2*B+m-2
    let ell := 2*Y*Y
    let M := Y*b
    let Z := M*(ell+1)
    ∃ f i : V, 0<F ∧ 0<q ∧ 0<Y ∧ 0<r ∧ 0<f ∧ 0<i ∧
      q<F+q ∧ B+F*q=q*(1+k*q) ∧
      M*(ell+2+r)+Y*b=M*(2*B)+B*(q^3)+Z ∧
      Z*Z=M*M*(1+ell*(ell+2)) ∧
      (c*c*i)*(c*c*i)+delta a=delta a*(f*f) := by
  let q : V := b+1
  let F : V := 1+k%b
  let Y : V := q^3
  let a : V := 2*Y
  let c : V := a+1
  let m : V := q*(k+k/b)
  let B : V := b*m
  let r : V := 2*B+m-2
  let ell : V := 2*Y*Y
  let M : V := Y*b
  let Z : V := M*(ell+1)
  have hq : 0<q := by dsimp [q]; simp
  have hF : 0<F := by dsimp [F]; simp
  have hY : 0<Y := by dsimp [Y]; exact pow_pos hq _
  have hm : 0<m := by
    dsimp [m]
    exact mul_pos hq (lt_of_lt_of_le hk (by simp))
  have hB : 0<B := by dsimp [B]; exact mul_pos hb hm
  have hB1 : 1≤B := pos_iff_one_le.mp hB
  have h2B : (2:V)≤2*B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hB1 (by simp : (0:V)≤2)
  have hlt : (2:V)<2*B+m := lt_of_le_of_lt h2B (lt_add_of_pos_right _ hm)
  have hr : 0<r := tsub_pos_iff_lt.mpr hlt
  have hr2 : r+2=2*B+m := tsub_add_cancel_of_le (le_of_lt hlt)
  have hdiv := div_add_mod k b
  have htransport : B+F*q=q*(1+k*q) := by
    calc
      B+F*q = q+b*q*k+q*(b*(k/b)+k%b) := by dsimp [B,m,F]; ring
      _ = q+b*q*k+q*k := by rw [hdiv]
      _ = q*(1+k*q) := by dsimp [q]; ring
  obtain ⟨f,i,hf,hi,hs⟩ := strong_seed_at_successor a
  refine ⟨f,i,hF,hq,hY,hr,hf,hi,?_,htransport,?_,?_,?_⟩
  · exact lt_add_of_pos_left q hF
  · change M*(ell+2+r)+Y*b=M*(2*B)+B*(q^3)+Z
    calc
      _ = M*(ell+(r+2))+Y*b := by ring
      _ = M*(ell+(2*B+m))+Y*b := by rw [hr2]
      _ = M*(2*B)+B*(q^3)+Z := by dsimp [Z,M,B,Y]; ring
  · change Z*Z=M*M*(1+ell*(ell+2))
    dsimp [Z]
    ring
  · exact hs
end DiophantineConsistency.AdaptiveGap85WeakFirstStrong

import DiophantineConsistency.AdaptiveGap85Factors
import DiophantineConsistency.AdaptiveGap85WeakFamily

/-! Exact actual-factor binding for the weaker first-plus-auxiliary family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FamilyBinding
open AdaptiveGap85Factors AdaptiveGap85WeakFamily

def ports (b k mu nu : ℤ) : Fin 4 → ℤ := ![b,k,mu,nu]
def witness (b k a t : ℤ) : Fin 13 → ℤ :=
  let q := b+1
  let B := q*(1+k*q)-(1+a)*q
  let m := q*(k+t)
  let r := 2*B+m-2
  ![1,1+a,q,1,1,1,1,q^3,r,1,1,1,1]

/-- The first projection of the actual 85 circuit is one throughout the
quotient/remainder family, for arbitrary remaining fixed ports. -/
theorem first_factor_actual (b k a t mu nu : ℤ) (h : k=b*t+a) :
    ((factors (ports b k mu nu)).1).eval (witness b k a t)=1 := by
  rw [h]
  simp [factors,Expr.eval,ports,witness]
  ring

/-- The actual auxiliary and strong projections have the claimed values. -/
theorem auxiliary_strong_actual (b k a t mu nu : ℤ) :
    let w := witness b k a t
    let c := 1+2*(b+1)^3
    ((factors (ports b k mu nu)).2.2.1).eval w=1 ∧
      ((factors (ports b k mu nu)).2.2.2).eval w=1+c^4 := by
  dsimp
  constructor
  · simp [factors,Expr.eval,ports,witness]
  · simp [factors,Expr.eval,ports,witness]
    ring
/-- At any positive b and k and arbitrary other ports, the actual first and
auxiliary factors are one, all witnesses are positive, and the reverse bound
fails. The actual complete literal is nonzero. -/
theorem actual_family_properties (b k mu nu : ℤ) (hb : 1≤b) (hk : 1≤k) :
    let p := ports b k mu nu
    let w := witness b k (k%b) (k/b)
    (∀ i,0<w i) ∧ ¬(w 1+w 2 < 1+w 0*b) ∧
    ((factors p).1).eval w=1 ∧ ((factors p).2.2.1).eval w=1 ∧
    (AdaptiveGap85Literal.expressionAt85 p).eval w ≠ 0 := by
  dsimp
  have hdec : k=b*(k/b)+k%b := by
    have h := Int.emod_add_mul_ediv k b
    omega
  have hp := positive_family b k hb hk
  dsimp at hp
  obtain ⟨hF,hq,hY,hr,hbound,hB⟩ := hp
  have hfirst := first_factor_actual b k (k%b) (k/b) mu nu hdec
  have haux := auxiliary_strong_actual b k (k%b) (k/b) mu nu
  dsimp at haux
  have hw : ∀ i,0<witness b k (k%b) (k/b) i := by
    intro i
    fin_cases i <;> simp [witness] <;> omega
  have hnot : ¬(witness b k (k%b) (k/b) 1 + witness b k (k%b) (k/b) 2 <
      1+witness b k (k%b) (k/b) 0*b) := by
    simp [witness]
    omega
  have hc : 0<1+2*(b+1)^3 := by nlinarith
  have hc4 : 0<(1+2*(b+1)^3)^4 := pow_pos hc _
  have hs : 1<1+(1+2*(b+1)^3)^4 := by omega
  have hfull : (AdaptiveGap85Literal.expressionAt85 (ports b k mu nu)).eval
      (witness b k (k%b) (k/b)) ≠ 0 := by
    intro hz
    have he : (1+(1+2*(b+1)^3)^4) *
        (((factors (ports b k mu nu)).2.1).eval (witness b k (k%b) (k/b))) = 1 := by
      have heval := hz
      rw [expression_factors] at heval
      change ((factors (ports b k mu nu)).2.2.2).eval (witness b k (k%b) (k/b)) *
        (((factors (ports b k mu nu)).2.2.1).eval (witness b k (k%b) (k/b)) *
          (((factors (ports b k mu nu)).1).eval (witness b k (k%b) (k/b)) *
            ((factors (ports b k mu nu)).2.1).eval (witness b k (k%b) (k/b)))) - 1 = 0 at heval
      rw [hfirst,haux.1,haux.2] at heval
      simp only [one_mul] at heval
      omega
    have hd : (1+(1+2*(b+1)^3)^4) ∣ (1:ℤ) := ⟨_,he.symm⟩
    have hu : IsUnit (1+(1+2*(b+1)^3)^4 : ℤ) := isUnit_iff_dvd_one.mpr hd
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  exact ⟨hw,hnot,hfirst,haux.1,hfull⟩
end DiophantineConsistency.AdaptiveGap85FamilyBinding

import DiophantineConsistency.AdaptiveGap85FamilyGeneral
import Mathlib.Data.Int.ModEq

/-! An arbitrary-ports first/auxiliary partial family obstructs a rank-preserving
quotient/remainder normalization. It does not produce a full 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85PartialRankRemainder
open AdaptiveGap85Factors AdaptiveGap85FamilyBinding

def rankPlus (q F C J mu nu : ℤ) : ℤ :=
  let q2 := q*q
  let neg := q*F+C
  q2*q2+neg+J*(mu+nu*q)

def rankMinus (q F C : ℤ) : ℤ :=
  let q2 := q*q
  let neg := q*F+C
  q2+neg*q2

theorem rankMinus_mod (q F C : ℤ) : rankMinus q F C % q = 0 := by
  have he : rankMinus q F C=q*(q+(q*F+C)*q) := by dsimp [rankMinus]; ring
  rw [he,Int.mul_emod_right]

theorem rankPlus_mod (q F C J mu nu : ℤ) :
    rankPlus q F C J mu nu % q = (C+J*mu)%q := by
  have he : rankPlus q F C J mu nu=(C+J*mu)+q*(q*q*q+F+J*nu) := by
    dsimp [rankPlus]; ring
  rw [he,Int.add_emod,Int.mul_emod_right,add_zero,Int.emod_emod]

/-- Exact signed rank modulo q cannot be retained by any normalized positive
pair if the original C is divisible by q. -/
theorem no_normalized_same_rank_residue (q F C F' C' J mu nu : ℤ)
    (_hq : 0<q) (hC : q∣C) (hC' : 0<C') (hgap : F'+C'<q)
    (hF' : 0≤F') :
    ¬((rankPlus q F C J mu nu+rankMinus q F' C')%q =
      (rankMinus q F C+rankPlus q F' C' J mu nu)%q) := by
  have hcsmall : C'<q := by omega
  intro he
  have hl : (rankPlus q F C J mu nu+rankMinus q F' C')%q =
      rankPlus q F C J mu nu%q := by
    rw [Int.add_emod,rankMinus_mod,add_zero,Int.emod_emod]
  have hr : (rankMinus q F C+rankPlus q F' C' J mu nu)%q =
      rankPlus q F' C' J mu nu%q := by
    rw [Int.add_emod,rankMinus_mod,zero_add,Int.emod_emod]
  rw [hl,hr,rankPlus_mod,rankPlus_mod] at he
  have hmod : Int.ModEq q (C+J*mu) (C'+J*mu) := he
  have hcancel : Int.ModEq q C C' := (Int.ModEq.refl (J*mu)).add_right_cancel hmod
  change C%q=C'%q at hcancel
  rw [Int.emod_eq_zero_of_dvd hC,Int.emod_eq_of_lt (le_of_lt hC') hcsmall] at hcancel
  omega

/-- A variant of the weak fixed-port family whose first transport stays
positive even when the nonnegative kernel parameter is zero. -/
def witness (b k a t : ℤ) : Fin 13 → ℤ :=
  let q := b+1
  let B := q*(q+k*q)-(1+a)*q
  let m := q*(k+t+1)
  let r := 2*B+m-2
  ![1,1+a,q,1,1,1,q,q^3,r,1,1,1,1]

theorem first_factor_partial (b k a t mu nu : ℤ) (h : k=b*t+a) :
    ((factors (ports b k mu nu)).1).eval (witness b k a t)=1 := by
  rw [h]
  simp [factors,Expr.eval,ports,witness]
  ring

theorem auxiliary_strong_partial (b k a t mu nu : ℤ) :
    let w := witness b k a t
    let c := 1+2*(b+1)^3
    ((factors (ports b k mu nu)).2.2.1).eval w=1 ∧
      ((factors (ports b k mu nu)).2.2.2).eval w=1+c^4 := by
  dsimp
  constructor
  · simp [factors,Expr.eval,ports,witness]
  · simp [factors,Expr.eval,ports,witness]
    ring

theorem transport_eq (b k a t : ℤ) (h : k=b*t+a) :
    (b+1)*((b+1)+k*(b+1))-(1+a)*(b+1) =
      b*((b+1)*(k+t+1)) := by
  rw [h]
  ring

/-- A positive partial tuple; its full expression is provably nonzero. -/
theorem actual_partial_family (b k mu nu : ℤ) (hb : 1≤b) (hk : 0≤k) :
    let w := witness b k (k%b) (k/b)
    (∀ i,0<w i) ∧ ((factors (ports b k mu nu)).1).eval w=1 ∧
    ((factors (ports b k mu nu)).2.2.1).eval w=1 ∧
    (AdaptiveGap85Literal.expressionAt85 (ports b k mu nu)).eval w ≠ 0 := by
  dsimp
  have hbpos : 0<b := by omega
  have hdec : k=b*(k/b)+k%b := by
    have he := Int.emod_add_mul_ediv k b
    omega
  have ha : 0≤k%b := Int.emod_nonneg k (ne_of_gt hbpos)
  have ht : 0≤k/b := Int.ediv_nonneg hk (by omega)
  have hq : 0 < b+1 := by omega
  have hm : 0 < (b+1)*(k+k/b+1) := mul_pos hq (by omega)
  have hBeq := transport_eq b k (k%b) (k/b) hdec
  have hB : 0 < (b+1)*((b+1)+k*(b+1))-(1+k%b)*(b+1) := by
    rw [hBeq]
    exact mul_pos hbpos hm
  have hY : 0<(b+1)^3 := pow_pos hq _
  have hr : 0<2*((b+1)*((b+1)+k*(b+1))-(1+k%b)*(b+1))+
      (b+1)*(k+k/b+1)-2 := by omega
  have hw : ∀ i,0<witness b k (k%b) (k/b) i := by
    intro i
    fin_cases i <;> simp [witness] <;> omega
  have hfirst := first_factor_partial b k (k%b) (k/b) mu nu hdec
  have haux := auxiliary_strong_partial b k (k%b) (k/b) mu nu
  dsimp at haux
  have hc : 0<1+2*(b+1)^3 := by omega
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
  exact ⟨hw,hfirst,haux.1,hfull⟩

/-- The partial tuple for any positive b and nonnegative k cannot be
normalized while preserving q, J, and signed rank modulo q. It is not a full zero. -/
theorem partial_family_blocks_rank_normalization (b k mu nu : ℤ)
    (hb : 1≤b) (hk : 0≤k) :
    ∃ w : Fin 13 → ℤ, (∀ i,0<w i) ∧
      ((factors (ports b k mu nu)).1).eval w=1 ∧
      ((factors (ports b k mu nu)).2.2.1).eval w=1 ∧
      (AdaptiveGap85Literal.expressionAt85 (ports b k mu nu)).eval w ≠ 0 ∧
      let q := 1+w 0*b
      ∀ F' C' : ℤ, 0<F' → 0<C' → F'+C'<q →
        ¬((rankPlus q (w 1) (w 2) (w 0) mu nu+rankMinus q F' C')%q =
          (rankMinus q (w 1) (w 2)+rankPlus q F' C' (w 0) mu nu)%q) := by
  let w := witness b k (k%b) (k/b)
  have hw := actual_partial_family b k mu nu hb hk
  dsimp at hw
  refine ⟨w,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2,?_⟩
  dsimp only
  intro F' C' hF' hC' hgap
  have hq : 0<1+w 0*b := by dsimp [w,witness]; omega
  have hdiv : (1+w 0*b) ∣ w 2 := by
    dsimp [w,witness]
    have he : 1+1*b=b+1 := by ring
    rw [he]
  exact no_normalized_same_rank_residue _ _ _ F' C' _ _ _ hq hdiv hC' hgap (le_of_lt hF')
end DiophantineConsistency.AdaptiveGap85PartialRankRemainder

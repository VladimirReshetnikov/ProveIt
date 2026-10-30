import DiophantineConsistency.AdaptiveGap85Literal
import Mathlib.Tactic.Ring

/-! Symbolic identities for a family satisfying only two factor-unit equations.
    They do not exhibit a zero of the complete candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85WeakFamily

/-- If `k = b*t+a`, the selected first-factor transport is divisible by b. -/
theorem transport_factorization (b k a t : ℤ) (h : k=b*t+a) :
    let q := b+1
    let F := 1+a
    let B := q*(1+k*q)-F*q
    B=b*q*(k+t) := by
  dsimp
  rw [h]
  ring

/-- Given a transport `B=b*t`, the selected first root is exactly the
positive Pell root; hence the first factor is one. -/
theorem first_factor_family (b t : ℤ) :
    let q := b+1
    let Y := q^3
    let ell := 2*Y^2
    let M := Y*b
    let B := b*t
    let r := 2*B+t-2
    let Z := M*(ell+2+r-2*B)+Y*b-B*q^3
    1+Z^2-M^2*(1+ell*(ell+2))=1 := by
  dsimp
  ring

/-- With f=i=y=1, the auxiliary factor is one and the strong factor is
`1+c⁴`, regardless of the rank and signed ordinate. -/
theorem auxiliary_and_strong_family (Delta c V : ℤ) :
    (1-Delta*(1^2-1)*(1-V^2)=1) ∧
    (1+(c^2*1)^2-Delta*(1^2-1)=1+c^4) := by
  constructor <;> ring
/-- For positive b and k, the remainder-based family has positive coordinates,
violates the reverse bound, and has the claimed divisible transport. -/
theorem positive_family (b k : ℤ) (hb : 1≤b) (hk : 1≤k) :
    let a := k%b
    let t := k/b
    let q := b+1
    let F := 1+a
    let B := q*(1+k*q)-F*q
    let m := q*(k+t)
    let r := 2*B+m-2
    0<F ∧ 0<q ∧ 0<q^3 ∧ 0<r ∧ q<F+q ∧ B=b*m := by
  dsimp
  have hbpos : 0<b := by omega
  have ha0 : 0≤k%b := Int.emod_nonneg k (ne_of_gt hbpos)
  have ht0 : 0≤k/b := Int.ediv_nonneg (by omega) (by omega)
  have hkdec : k=b*(k/b)+k%b := by
    have h := Int.emod_add_mul_ediv k b
    omega
  have hB := transport_factorization b k (k%b) (k/b) hkdec
  dsimp at hB
  have hq : 0<b+1 := by omega
  have hm : 0<(b+1)*(k+k/b) := mul_pos hq (by omega)
  have hBpos : 0<b*(b+1)*(k+k/b) := by
    simpa only [mul_assoc] using mul_pos hbpos hm
  constructor
  · omega
  · constructor
    · exact hq
    · constructor
      · exact pow_pos hq _
      · constructor
        · rw [hB]
          omega
        · constructor
          · omega
          · rw [hB]
            ring
end DiophantineConsistency.AdaptiveGap85WeakFamily

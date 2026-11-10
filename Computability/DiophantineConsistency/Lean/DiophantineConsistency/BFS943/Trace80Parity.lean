import DiophantineConsistency.BFS943.SignedBezout
import DiophantineConsistency.ArithmeticGcdNormalization
import Foundation.FirstOrder.Arithmetic.Exponential.Log

/-! # Cancelling an odd factor against a power of two

`Pow2 P`, `¬ 2 ∣ a` and `P ∣ a e` (in the difference ring) give `P ∣ e`: the
gcd certificate `g` of `a` and `P` divides the power of two `P`, so it is a
power of two; it divides the odd `a`, so `g = 1`, and the Bezout certificate
cancels `a` (`TenPositiveSignedBezout.cancel_signed_factor`). Used for
`q² ∣ s (4 w s σ - 1)` once `q` is known to be a power of two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace80Parity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pow2_cancel_odd (P a : V) (e : DiffRing V) (hP : Pow2 P) (ha : ¬ (2:V)∣a)
    (hd : (ι P:DiffRing V)∣ι a*e) : (ι P:DiffRing V)∣e := by
  obtain ⟨g,hga,hgP,hbez⟩ := gcd_certificate_exists a P
  have hg : Pow2 g := Pow2.of_dvd hgP hP
  have hg1 : g=1 := by
    by_contra hne
    exact ha (dvd_trans (Pow2.two_dvd' hg hne) hga)
  rw [hg1] at hbez
  exact TenPositiveSignedBezout.cancel_signed_factor a P e hbez hd

/-- `u + m - 1` is odd when `u` and `m` are even and `u + m ≥ 1`. -/
theorem odd_pred (u m : V) (hu : (2:V)∣u) (hm : (2:V)∣m) (h1 : 1≤u+m) :
    ¬ (2:V)∣u+m-1 := by
  intro h2
  have hsub : u+m-1+1=u+m := tsub_add_cancel_of_le h1
  have hR : (ι (2:V):DiffRing V)∣ι (u+m-1)+1 := by
    rw [←map_one (ι : V →+* DiffRing V),←map_add,hsub]
    exact map_dvd ι (dvd_add hu hm)
  have h1R : (ι (2:V):DiffRing V)∣1 := (dvd_add_right (map_dvd ι h2)).mp hR
  obtain ⟨c,hc⟩ := h1R
  rw [map_ofNat] at hc
  have hdisc : ∀ x : DiffRing V, 0<x → 1≤x := fun x hx =>
    one_le_of_pos (fun z hz => pos_iff_one_le.mp hz) hx
  rcases le_or_gt c 0 with h|h
  · linarith
  · have := hdisc c h; linarith

#print axioms Trace80Parity.pow2_cancel_odd
#print axioms Trace80Parity.odd_pred
end Trace80Parity

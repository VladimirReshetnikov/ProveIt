import DiophantineConsistency.ArithmeticPellFirstNorm
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only proposed fact-level bounds for the auxiliary-root route.
Neither graph norms nor the hypotheses below are derived from a graph zero.
No elaboration or compilation has been performed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AuxRootBoundsModelDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPellFirstNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The existing internal first-norm descent gives the second-unit lower
bound once k>2 has been proved separately. -/
theorem first_ordinate_large (m tau k : V) (hm : 0<m) (hk : 2<k)
    (hn : tau*tau=1+m*(m+1)*k*k) : 8*m+4≤k := by
  let q : V := m-1
  have hm1 : m-1+1=m := tsub_add_cancel_of_le (pos_iff_one_le.mp hm)
  have hdisc : discriminant q=m*(m+1) := by
    unfold discriminant
    dsimp only [q]
    rw [show m-1+2=(m-1+1)+1 by ring,hm1]
  have hn' : tau*tau=1+discriminant q*k*k := by rwa [hdisc]
  obtain ⟨u,v,hu,hvk,hun,hut,hkdecomp⟩ := descent q tau k (lt_trans (by norm_num) hk) hn'
  have hvpos : 0<v := by
    apply pos_iff_ne_zero.mpr
    intro hv0
    have husq : u*u=1 := by simpa only [hv0,mul_zero,add_zero] using hun
    have huupper : u≤1 := by
      apply nonneg_le_nonneg_of_sq_le_sq (by simp)
      simpa only [one_mul] using le_of_eq husq
    have huone : u=1 := le_antisymm huupper (pos_iff_one_le.mp hu)
    have hk2 : k=2 := by simpa only [hv0,mul_zero,add_zero,huone,mul_one] using hkdecomp
    exact (ne_of_gt hk) hk2
  have hv2 : 2≤v := two_le_ordinate q u v hvpos hun
  have hugt : m*v<u := by
    apply lt_of_mul_self_lt_mul_self₀ (by simp)
    have he : u*u=(m*v)*(m*v)+(1+m*v*v) := by rw [hun,hdisc]; ring
    rw [he]
    exact lt_add_of_pos_right _ (by simp)
  have hu2 : 2*m+1≤u := by
    have hmv : 2*m≤m*v := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hv2 (Arithmetic.zero_le m)
    exact lt_iff_succ_le.mp (lt_of_le_of_lt hmv hugt)
  have hbase : 2*q+3=2*m+1 := by
    dsimp only [q]
    calc
      2*(m-1)+3=2*(m-1+1)+1 := by ring
      _=2*m+1 := by rw [hm1]
  calc
    8*m+4=2*(2*m+1)+(2*m+1)*2 := by ring
    _≤2*u+(2*m+1)*v := add_le_add
      (mul_le_mul_of_nonneg_left hu2 (by simp))
      (mul_le_mul_of_nonneg_left hv2 (by simp))
    _=k := by simpa only [hbase] using hkdecomp.symm

/-- Given the explicit strong norm and Δ<c³, the strong scale is larger
than c+1. Parameters live in the ordered difference ring. -/
theorem strong_f_square_large (c i Delta f : DiffRing V)
    (hc : 0<c) (hi : 1≤i) (hDelta : 0<Delta) (hDeltaSmall : Delta<c*c*c)
    (hstrong : (i*c*c)*(i*c*c)+Delta=Delta*(f*f)) : c+1<f*f := by
  have hc2 : 0<c*c := mul_pos hc hc
  have hI : c*c≤i*c*c := by
    have h := le_mul_of_one_le_left (le_of_lt hc2) hi
    simpa only [mul_assoc] using h
  have hI2 : (c*c)*(c*c)≤(i*c*c)*(i*c*c) := mul_self_le_mul_self (le_of_lt hc2) hI
  have hDeltaProduct : Delta*c<(c*c*c)*c := mul_lt_mul_of_pos_right hDeltaSmall hc
  by_contra hnot
  have hf : f*f≤c+1 := le_of_not_gt hnot
  have hbound : Delta*(f*f)≤Delta*(c+1) := mul_le_mul_of_nonneg_left hf (le_of_lt hDelta)
  nlinarith [hstrong,hI2,hDeltaProduct,hbound]

/-- A strong coefficient equal to (i*c²)² exceeds one when c>1 and i≥1. -/
theorem strong_Q_gt_one (c i Q : DiffRing V) (hc : 1<c) (hi : 1≤i)
    (hQ : Q=(i*c*c)*(i*c*c)) : 1<Q := by
  have hc0 : 0<c := lt_trans (by norm_num) hc
  have hc2 : 1<c*c := by nlinarith [sq_nonneg (c-1)]
  have hI : c*c≤i*c*c := by
    have h := le_mul_of_one_le_left (le_of_lt (mul_pos hc0 hc0)) hi
    simpa only [mul_assoc] using h
  have hIgt : 1<i*c*c := lt_of_lt_of_le hc2 hI
  rw [hQ]
  have hs := mul_self_lt_mul_self (by norm_num : (0 : DiffRing V)≤1) hIgt
  simpa only [one_mul] using hs

/-- Discreteness rules out z²≤1 when z+c is a multiple of f² strictly
between zero and f². This is a fact-level result, with the gap assumed. -/
theorem signed_square_gt_one (c f t z : DiffRing V) (hc : 1<c)
    (hf : c+1<f*f) (he : z+c=f*f*t) : 1<z*z := by
  by_contra hnot
  have hsq : z*z≤1 := le_of_not_gt hnot
  have hzlo : -(1 : DiffRing V)≤z := by
    by_contra hn
    have hneg : z < -(1 : DiffRing V) := lt_of_not_ge hn
    have hp : 0<(z-1)*(z+1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith
  have hzhi : z≤1 := by
    by_contra hn
    have hpos : (1 : DiffRing V)<z := lt_of_not_ge hn
    have hp : 0<(z-1)*(z+1) := mul_pos (by linarith) (by linarith)
    nlinarith
  have hsumpos : 0<z+c := by linarith
  have hsumlt : z+c<f*f := by linarith
  have hfpos : 0<f*f := by linarith
  have htpos : 0<t := (mul_pos_iff_of_pos_left hfpos).mp (by rw [← he]; exact hsumpos)
  have htone : 1≤t := ModelDifferenceRing.one_le_of_pos
    (fun a ha => pos_iff_one_le.mp ha) htpos
  have hle : f*f≤f*f*t := le_mul_of_one_le_right (le_of_lt hfpos) htone
  rw [← he] at hle
  exact (not_le_of_gt hsumlt) hle

end DiophantineConsistency.AuxRootBoundsModelDraft

#print axioms DiophantineConsistency.AuxRootBoundsModelDraft.first_ordinate_large
#print axioms DiophantineConsistency.AuxRootBoundsModelDraft.strong_f_square_large
#print axioms DiophantineConsistency.AuxRootBoundsModelDraft.strong_Q_gt_one
#print axioms DiophantineConsistency.AuxRootBoundsModelDraft.signed_square_gt_one

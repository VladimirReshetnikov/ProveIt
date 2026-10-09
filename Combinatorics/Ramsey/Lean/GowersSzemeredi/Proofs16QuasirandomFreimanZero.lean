import GowersSzemeredi.Proofs16BoxEmptyRectangle
import GowersSzemeredi.Proofs16FreimanNonvanishing
import GowersSzemeredi.Proofs16DenseBohrGraphProfiles

/-! Quasirandom coverage forces a Freiman map to vanish on a half-radius
Bohr set. No frequency-removal loss or prime-target assumption is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem quasirandom_freiman_zero {N ell M : Nat} [NeZero N] [NeZero M]
    (B T C Z : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (f : ZMod N → ZMod N) {r delta epsilon kappa : Real}
    (hr : 0 ≤ r) (hBT : B ⊆ T) (hZ : Z ⊆ C) (hk : 0 < kappa)
    (hmass : kappa*N ≤ (Z.card : Real)) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hf : IsFreimanLinearOn (bohr T r) f) (hf0 : f 0 = 0)
    (hcell : 1 ≤ (r/2)*M)
    (hbox : boxSum (fun (w : ↥(bohr B r)) (z : ↥C) =>
      (if (w : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i z) r
        then (1 : Real) else 0)-delta) ≤
      epsilon^4*((bohr B r).card : Real)^2*(C.card : Real)^2)
    (hvanish : ∀ w ∈ bohr T r, ∀ z ∈ Z,
      w ∈ bohr (Finset.univ.image fun i => theta i z) r → f w = 0)
    (hsmall : 2*(M : Real)^T.card*epsilon < delta*kappa) :
    ∀ w ∈ bohr T (r/2), f w = 0 := by
  intro w hw
  by_contra hfw
  let U := (bohr T r).filter (fun v => f v ≠ 0)
  have hU : U ⊆ bohr B r := fun v hv => bohr_anti hBT r (Finset.mem_filter.mp hv).1
  have hrect := box_empty_finset_rectangle_card
    (fun v z => if v ∈ bohr (Finset.univ.image fun i => theta i z) r then (1 : Real) else 0)
    (bohr B r) U C Z hU hZ hd he hbox (by
      intro v hv z hz
      apply if_neg
      intro hez
      exact (Finset.mem_filter.mp hv).2 (hvanish v (Finset.mem_filter.mp hv).1 z hz hez))
  have hBC : ((bohr B r).card : Real) ≤ N := by exact_mod_cast (show (bohr B r).card ≤ N by simpa only [ZMod.card] using Finset.card_le_univ (bohr B r))
  have hCC : (C.card : Real) ≤ N := by exact_mod_cast (show C.card ≤ N by simpa only [ZMod.card] using Finset.card_le_univ C)
  have hrectN : delta*(U.card : Real)*(kappa*N) ≤ epsilon*(N : Real)^2 := by
    calc delta*(U.card : Real)*(kappa*N) ≤ delta*U.card*Z.card :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ epsilon*(bohr B r).card*C.card := hrect
      _ ≤ epsilon*(N : Real)*N := by gcongr
      _ = _ := by ring
  have hhalf := freiman_nonzero_card_half T hr f hf hf0 hw hfw
  have hlower : (N : Real) ≤ 2*(M : Real)^T.card*U.card := by
    have h := (bohr_card_lower T M hcell).trans (Nat.mul_le_mul_left (M^T.card) hhalf)
    have hc : (N : Real) ≤ (M : Real)^T.card*(2*(U.card : Real)) := by exact_mod_cast h
    nlinarith only [hc]
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hlow : delta*kappa*(N : Real)^2 ≤
      (2*(M : Real)^T.card)*(delta*(U.card : Real)*(kappa*N)) := by
    have h := mul_le_mul_of_nonneg_left hlower (show 0 ≤ delta*kappa*N by positivity)
    nlinarith only [h]
  have hup := mul_le_mul_of_nonneg_left hrectN (show 0 ≤ 2*(M : Real)^T.card by positivity)
  have hle : delta*kappa ≤ 2*(M : Real)^T.card*epsilon := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
    nlinarith only [hlow,hup]
  exact (not_le_of_gt hsmall) hle

theorem DenseBohrGraphProfiles.freiman_zero {N ell H m : Nat} [NeZero N] [NeZero H]
    {B C : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N} {epsilon : Real}
    (h : DenseBohrGraphProfiles B C theta H m epsilon)
    (T Z : Finset (ZMod N)) (f : ZMod N → ZMod N) {r kappa : Real}
    (hr : 0 < r) (hrMax : r < 1/4) (hH : 1 ≤ r*H)
    (hBT : B ⊆ T) (hZ : Z ⊆ C) (hk : 0 < kappa) (hmass : kappa*N ≤ (Z.card : Real))
    (he : 0 ≤ epsilon) (hf : IsFreimanLinearOn (bohr T r) f) (hf0 : f 0 = 0)
    (hvanish : ∀ w ∈ bohr T r, ∀ z ∈ Z,
      w ∈ bohr (Finset.univ.image fun i => theta i z) r → f w = 0)
    (hsmall : 4*((2*H : Nat) : Real)^T.card*epsilon < (1/(H : Real)^m)*kappa) :
    ∀ w ∈ bohr T (r/2), f w = 0 := by
  obtain ⟨delta,hd,hd1,hbox⟩ := h r r hr le_rfl hrMax hH
  have hHpos : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  have hdelta : 0 ≤ delta := (by positivity : (0 : Real) ≤ (1/(H : Real)^m)/2).trans hd
  apply quasirandom_freiman_zero (M := 2*H) B T C Z theta f hr.le hBT hZ hk hmass hdelta he hf hf0
    (by push_cast; nlinarith only [hH]) hbox hvanish
  have h := mul_le_mul_of_nonneg_right hd hk.le
  nlinarith only [hsmall,h]

end LeanProofs.GowersSzemeredi

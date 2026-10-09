import GowersSzemeredi.Proofs16QuasirandomFreimanZero
import GowersSzemeredi.Proofs16FrequencyBohrCompletion
import GowersSzemeredi.Proofs16ColumnPairComposition

/-! Many coherent bridges imply a direct column-pair identity after a
constant radius shrink. The graph profile supplies the required coverage. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherent_pair_weak_transitivity {N ell H m : Nat} [NeZero N] [NeZero H]
    (B C X Z : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) {r epsilon kappa : Real}
    (hr : 0 < r) (hrMax : r < 1/4) (he : 0 ≤ epsilon) (hk : 0 < kappa)
    (hH : 3 ≤ r*H) (hX : X ⊆ C) (hZ : Z ⊆ X)
    (htheta : ∀ i, IsFreimanLinearOn C (theta i))
    (hlocal : ∀ u ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta r u) (F u) ∧ F u 0 = 0)
    (hprofile : DenseBohrGraphProfiles B C theta H m epsilon)
    (hmass : kappa*N ≤ (Z.card : Real))
    (hsmall : 4*((2*H : Nat) : Real)^(4*(B.card+ell))*epsilon < (1/(H : Real)^m)*kappa)
    (x y a : ZMod N) (hx : x ∈ X) (hxa : x+a ∈ X) (hy : y ∈ X) (hya : y+a ∈ X)
    (hza : ∀ z ∈ Z, z+a ∈ X)
    (hbridge : ∀ z ∈ Z,
      ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun i => theta i u)) F r (x+a,x) (z+a,z) ∧
      ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun i => theta i u)) F r (z+a,z) (y+a,y)) :
    ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun i => theta i u)) F (r/6) (x+a,x) (y+a,y) := by
  let U := fun u => B ∪ Finset.univ.image (fun i => theta i u)
  let t := columnPairTuple (x+a,x) (y+a,y)
  let T := columnQuadrupleSpectrum U t
  let f := columnQuadrupleDefect F t
  have ht : ∀ i, t i ∈ X := by
    intro i; fin_cases i
    · exact hxa
    · exact hy
    · exact hx
    · exact hya
  have hT : T.card ≤ 4*(B.card+ell) := by
    apply Finset.card_biUnion_le.trans
    calc (∑ i : Fin 4, (U (t i)).card) ≤ ∑ _i : Fin 4, (B.card+ell) :=
        Finset.sum_le_sum fun i _ => (Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_image_le.trans (by simp)) _)
      _ = _ := by simp
  have hBT : B ⊆ T := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,Finset.mem_union_left _ hv⟩
  have hf : IsFreimanLinearOn (bohr T (r/3)) f :=
    (columnQuadrupleDefect_freiman U F t (fun i => (hlocal _ (ht i)).1)).mono
      (bohr_mono_radius T (by linarith : r/3 ≤ r))
  have hf0 : f 0 = 0 := by
    simp only [f,columnQuadrupleDefect,(hlocal _ (ht _)).2,add_zero,sub_zero]
  have hvanish : ∀ w ∈ bohr T (r/3), ∀ z ∈ Z,
      w ∈ bohr (Finset.univ.image fun i => theta i z) (r/3) → f w = 0 := by
    intro w hw z hz hwz
    obtain ⟨hwxa,hwx,hwya,hwy⟩ := (mem_columnPairTuple_bohr U (x+a,x) (y+a,y) (r/3) w).mp hw
    have hwB := bohr_anti hBT (r/3) hw
    have hwz' : w ∈ freimanFrequencyBohr B theta (r/3) z := by
      change w ∈ bohr (B ∪ Finset.univ.image (fun i => theta i z)) (r/3)
      rw [bohr_union]
      exact Finset.mem_inter.mpr ⟨hwB,hwz⟩
    have hfreq : ∀ i, theta i z+theta i (x+a) = theta i x+theta i (z+a) := by
      intro i
      exact htheta i z (x+a) x (z+a) (hX (hZ hz)) (hX hxa) (hX hx) (hX (hza z hz)) (by abel)
    have hwza := freiman_frequency_bohr_complete B theta hfreq hwz' hwxa hwx
    have hmono (u : ZMod N) : bohr (U u) (r/3) ⊆ bohr (U u) r := bohr_mono_radius _ (by linarith)
    have h₁ := (hbridge z hz).1 w (hmono _ hwxa) (hmono _ hwx) hwza (hmono _ hwz')
    have h₂ := (hbridge z hz).2 w hwza (hmono _ hwz') (hmono _ hwya) (hmono _ hwy)
    change F (x+a) w+F y w-F x w-F (y+a) w = 0
    linear_combination h₁+h₂
  have hbase : (1 : Real) ≤ (2*H : Nat) := by exact_mod_cast (show 1 ≤ 2*H by have := NeZero.pos H; omega)
  have hsmall' : 4*((2*H : Nat) : Real)^T.card*epsilon < (1/(H : Real)^m)*kappa :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hT) (by norm_num)) he).trans_lt hsmall
  have hzero := hprofile.freiman_zero T Z f (by positivity : 0 < r/3) (by linarith : r/3 < 1/4)
    (by nlinarith only [hH] : 1 ≤ (r/3)*H) hBT (hZ.trans hX) hk hmass he hf hf0 hvanish hsmall'
  intro w hwxa hwx hwya hwy
  have hw : w ∈ bohr T ((r/3)/2) := by
    rw [show (r/3)/2 = r/6 by ring]
    exact (mem_columnPairTuple_bohr U (x+a,x) (y+a,y) (r/6) w).mpr ⟨hwxa,hwx,hwya,hwy⟩
  have h := hzero w hw
  change F (x+a) w+F y w-F x w-F (y+a) w = 0 at h
  change F (x+a) w-F x w = F (y+a) w-F y w
  linear_combination h

end LeanProofs.GowersSzemeredi

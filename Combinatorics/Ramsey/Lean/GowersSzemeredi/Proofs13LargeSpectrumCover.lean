import GowersSzemeredi.Proofs13Basic
import GowersSzemeredi.Proofs07AdditiveRestriction

/-!
# Covering large vertical Fourier coefficients

This file proves Corollary 13.3.  At each greedy stage the residual height
projection has its actual density `delta`; using parameters `theta^2 * delta`
in Corollary 13.2 and `theta^8 * delta` in Corollary 7.6 avoids the paper's
implicit assumption that the projection has exactly `theta * N` elements.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private noncomputable def cor133LargePairs {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (theta : Real) : Finset (Pair N) :=
  Finset.univ.filter fun z =>
    theta * (N : Real) ^ 2 ≤
      ‖fourier (verticalEdgeFiberFunction A z.1) z.2‖

private structure Cor133CoverData (N : Nat) [NeZero N]
    (theta : Real) (Gamma : Finset (Pair N)) where
  q : Nat
  B : Fin q → Finset (ZMod N)
  sigma : Fin q → ZMod N → ZMod N
  G : Finset (ZMod N)
  G_large : (1 - theta) * N ≤ G.card
  freiman : ∀ i, FreimanHom 8 (B i) (sigma i)
  piece_large : ∀ i,
    (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N ≤ (B i).card
  budget :
    (q : Real) *
      ((2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) ≤ Gamma.card
  covers : ∀ p, p ∈ Gamma → p.1 ∈ G →
    ∃ i, p.1 ∈ B i ∧ p.2 = sigma i p.1

private lemma cor133_fiber_norm_le {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (h x : ZMod N) :
    ‖verticalEdgeFiberFunction A h x‖ ≤ (N : Real) := by
  let F := (verticalEdgeDomain A h).filter fun z => z.1 = x
  have hmaps : Set.MapsTo (fun p : Pair N => p.2) (↑F)
      (↑(Finset.univ : Finset (ZMod N))) := by norm_num
  have hinj : Set.InjOn (fun p : Pair N => p.2) (↑F) := by
    intro p hp q hq hsnd
    have hpfirst : p.1 = x := (Finset.mem_filter.mp hp).2
    have hqfirst : q.1 = x := (Finset.mem_filter.mp hq).2
    exact Prod.ext (hpfirst.trans hqfirst.symm) hsnd
  have hcard : F.card ≤ N := by
    simpa [ZMod.card] using
      (Finset.card_le_card_of_injOn (fun p : Pair N => p.2) hmaps hinj)
  change ‖((F.card : Nat) : Complex)‖ ≤ (N : Real)
  simpa using hcard

private lemma cor133_fourier_mass_le {N : Nat} [NeZero N]
    (A : Finset (Pair N)) :
    ∑ h : ZMod N, ∑ r : ZMod N,
        ‖fourier (verticalEdgeFiberFunction A h) r‖ ^ 2 ≤
      (N : Real) ^ 5 := by
  calc
    ∑ h : ZMod N, ∑ r : ZMod N,
        ‖fourier (verticalEdgeFiberFunction A h) r‖ ^ 2 =
        ∑ h : ZMod N, (N : Real) *
          ∑ x : ZMod N, ‖verticalEdgeFiberFunction A h x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro h _
      exact identity_2_3_holds N (verticalEdgeFiberFunction A h)
    _ ≤ ∑ _h : ZMod N, (N : Real) *
          ∑ _x : ZMod N, (N : Real) ^ 2 := by
      gcongr with h _
      exact cor133_fiber_norm_le A h x
    _ = (N : Real) ^ 5 := by
      simp [ZMod.card]
      ring

private lemma cor133_largePairs_card_le {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (theta : Real) (htheta : 0 < theta) :
    ((cor133LargePairs A theta).card : Real) ≤
      theta ^ (-(2 : Int)) * N := by
  let Gamma := cor133LargePairs A theta
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hpoint (z : Pair N) (hz : z ∈ Gamma) :
      (theta * (N : Real) ^ 2) ^ 2 ≤
        ‖fourier (verticalEdgeFiberFunction A z.1) z.2‖ ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) ?_ 2
    simpa [Gamma, cor133LargePairs] using hz
  have hsum :
      (Gamma.card : Real) * (theta * (N : Real) ^ 2) ^ 2 ≤
        ∑ z : Pair N,
          ‖fourier (verticalEdgeFiberFunction A z.1) z.2‖ ^ 2 := by
    calc
      (Gamma.card : Real) * (theta * (N : Real) ^ 2) ^ 2 =
          ∑ z ∈ Gamma, (theta * (N : Real) ^ 2) ^ 2 := by simp
      _ ≤ ∑ z ∈ Gamma,
          ‖fourier (verticalEdgeFiberFunction A z.1) z.2‖ ^ 2 := by
        exact Finset.sum_le_sum fun z hz => hpoint z hz
      _ ≤ ∑ z : Pair N,
          ‖fourier (verticalEdgeFiberFunction A z.1) z.2‖ ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  rw [Fintype.sum_prod_type] at hsum
  have hmass := cor133_fourier_mass_le A
  have hmain :
      (Gamma.card : Real) * (theta * (N : Real) ^ 2) ^ 2 ≤
        (N : Real) ^ 5 := hsum.trans hmass
  rw [zpow_neg, zpow_ofNat, mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ (sq_pos_of_pos htheta)).2
  apply le_of_mul_le_mul_right (a := (N : Real) ^ 4) ?_ (pow_pos hN 4)
  calc
    ((cor133LargePairs A theta).card : Real) * theta ^ 2 * (N : Real) ^ 4 =
        (Gamma.card : Real) * (theta * (N : Real) ^ 2) ^ 2 := by linarith
    _ ≤ (N : Real) ^ 5 := hmain
    _ = (N : Real) * (N : Real) ^ 4 := by ring

private lemma cor133_extract_piece {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (theta : Real) (hprime : Nat.Prime N)
    (htheta : 0 < theta) (Gamma : Finset (Pair N))
    (hGamma : Gamma ⊆ cor133LargePairs A theta)
    (hproj : theta * N ≤ (Gamma.image Prod.fst).card) :
    ∃ B : Finset (ZMod N), ∃ sigma : ZMod N → ZMod N,
      functionGraph B sigma ⊆ Gamma ∧
      FreimanHom 8 B sigma ∧
      (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N ≤ B.card := by
  let D : Finset (ZMod N) := Gamma.image Prod.fst
  let delta : Real := (D.card : Real) / N
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdeltaCard : (D.card : Real) = delta * N := (div_mul_cancel₀ _ hN.ne').symm
  have hthetaDelta : theta ≤ delta := (le_div_iff₀ hN).2 hproj
  have hdelta : 0 < delta := htheta.trans_le hthetaDelta
  have hex : ∀ h ∈ D, ∃ r, (h, r) ∈ Gamma := fun h hh => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact ⟨p.2, hp⟩
  choose! sigma hsigma using hex
  have hsum : theta ^ 2 * delta * (N : Real) ^ 5 ≤
      ∑ h ∈ D, ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 :=
    calc theta ^ 2 * delta * (N : Real) ^ 5 = ∑ _h ∈ D, (theta * (N : Real) ^ 2) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hdeltaCard]; ring
      _ ≤ _ := Finset.sum_le_sum fun h hh => pow_le_pow_left₀ (by positivity)
          (by simpa [cor133LargePairs] using hGamma (hsigma h hh)) 2
  have hquad : theta ^ 8 * delta * (delta * N) ^ 3 ≤ phiAdditiveCount D sigma := by
    linarith [corollary_13_2_holds N A D sigma _ (mul_pos (pow_pos htheta 2) hdelta) hsum]
  obtain ⟨B, hBD, hBsize, hFreiman⟩ := corollary_7_6_holds N D sigma delta _ hprime hdelta
    (mul_pos (pow_pos htheta 8) hdelta) hdeltaCard hquad
  refine ⟨B, sigma, Finset.image_subset_iff.2 fun x hx => hsigma x (hBD hx), hFreiman, ?_⟩
  have htwo : (2 : Real) ^ (-(1882 : Int)) = (2 : Real) ^ (-(1882 : Real)) := by norm_num
  calc (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N
      = (2 : Real) ^ (-(1882 : Real)) * theta ^ 9312 * theta ^ 1165 * N := by rw [htwo]; ring
    _ ≤ (2 : Real) ^ (-(1882 : Real)) * theta ^ 9312 * delta ^ 1165 * N := by gcongr
    _ = (2 : Real) ^ (-(1882 : Real)) * (theta ^ 8 * delta) ^ 1164 * delta * N := by ring
    _ ≤ B.card := hBsize

/-- Gowers's Corollary 13.3, with the prime-modulus convention explicit. -/
theorem corollary_13_3_holds : corollary_13_3 := by
  intro N _ A theta hprime htheta
  let Gamma := cor133LargePairs A theta
  have hscalePos : 0 < (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N :=
    mul_pos (by positivity) (by exact_mod_cast NeZero.pos N)
  let cover := (by
       intro Gamma
       refine Finset.strongInductionOn Gamma ?_
       intro Gamma ih hGamma
       let D : Finset (ZMod N) := Gamma.image Prod.fst
       by_cases hsmall : (D.card : Real) < theta * N
       · refine
           { q := 0
             B := Fin.elim0
             sigma := Fin.elim0
             G := Finset.univ \ D
             G_large := ?_
             freiman := fun i => i.elim0
             piece_large := fun i => i.elim0
             budget := by simp
             covers := fun p hp hpG =>
               absurd (Finset.mem_image_of_mem Prod.fst hp) (Finset.mem_sdiff.mp hpG).2 }
         have hGD : ((Finset.univ \ D).card : Real) + D.card = N := by
           exact_mod_cast (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)).trans
             (ZMod.card N)
         linarith
       · have hextract :=
           cor133_extract_piece A theta hprime htheta Gamma hGamma (not_lt.mp hsmall)
         let B0 := Classical.choose hextract
         have hextractB := Classical.choose_spec hextract
         let sigma0 := Classical.choose hextractB
         have hspec : functionGraph B0 sigma0 ⊆ Gamma ∧ FreimanHom 8 B0 sigma0 ∧
             (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N ≤ B0.card :=
           Classical.choose_spec hextractB
         let P := functionGraph B0 sigma0
         have hPnonempty : P.Nonempty := by
           rw [← Finset.card_pos, cor75_card_functionGraph]
           exact_mod_cast hscalePos.trans_le hspec.2.2
         let tail := ih (Gamma \ P) (Finset.sdiff_ssubset hspec.1 hPnonempty)
           (Finset.sdiff_subset.trans hGamma)
         let B : Fin (tail.q + 1) → Finset (ZMod N) := Fin.cases B0 tail.B
         let sigma : Fin (tail.q + 1) → ZMod N → ZMod N := Fin.cases sigma0 tail.sigma
         refine
           { q := tail.q + 1
             B := B
             sigma := sigma
             G := tail.G
             G_large := tail.G_large
             freiman := fun i => Fin.cases hspec.2.1 tail.freiman i
             piece_large := fun i => Fin.cases hspec.2.2 tail.piece_large i
             budget := ?_
             covers := ?_ }
         · have hcards : ((Gamma \ P).card : Real) + B0.card = Gamma.card := by
             rw [← cor75_card_functionGraph B0 sigma0]
             exact_mod_cast Finset.card_sdiff_add_card_eq_card hspec.1
           push_cast
           linarith [tail.budget, hspec.2.2]
         · intro p hp hpG
           by_cases hpP : p ∈ P
           · exact ⟨0, (cor75_mem_functionGraph B0 sigma0 p).1 hpP⟩
           · obtain ⟨j, hj⟩ := tail.covers p (Finset.mem_sdiff.2 ⟨hp, hpP⟩) hpG
             exact ⟨j.succ, hj⟩ : ∀ Gamma : Finset (Pair N), Gamma ⊆ cor133LargePairs A theta →
      Cor133CoverData N theta Gamma) Gamma
    (show Gamma ⊆ cor133LargePairs A theta by rfl)
  refine ⟨cover.q, cover.B, cover.sigma, cover.G, cover.G_large,
    cover.freiman, cover.piece_large, ?_, fun h hh r hr =>
      cover.covers (h, r) (by simpa [Gamma, cor133LargePairs] using hr) hh⟩
  refine le_of_mul_le_mul_right ((cover.budget.trans
    (cor133_largePairs_card_le A theta htheta)).trans_eq ?_) hscalePos
  field_simp

end LeanProofs.GowersSzemeredi

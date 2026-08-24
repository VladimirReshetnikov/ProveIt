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

private lemma cor133_card_functionGraph {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (sigma : ZMod N → ZMod N) :
    (functionGraph B sigma).card = B.card := by
  classical
  unfold functionGraph
  rw [Finset.card_image_iff.mpr]
  intro x _ y _ h
  exact congrArg Prod.fst h

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
  classical
  let F := (verticalEdgeDomain A h).filter fun z => z.1 = x
  have hmaps : Set.MapsTo (fun p : Pair N => p.2) (↑F)
      (↑(Finset.univ : Finset (ZMod N))) := by
    intro p hp
    simp
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
      gcongr with h x
      exact cor133_fiber_norm_le A h x
    _ = (N : Real) ^ 5 := by
      simp [ZMod.card]
      ring

private lemma cor133_largePairs_card_le {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (theta : Real) (htheta : 0 < theta) :
    ((cor133LargePairs A theta).card : Real) ≤
      theta ^ (-(2 : Int)) * N := by
  classical
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
  rw [zpow_neg, zpow_ofNat]
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ (sq_pos_of_pos htheta)).2
  apply le_of_mul_le_mul_right (a := (N : Real) ^ 4) ?_ (pow_pos hN 4)
  calc
    ((cor133LargePairs A theta).card : Real) * theta ^ 2 * (N : Real) ^ 4 =
        (Gamma.card : Real) * (theta * (N : Real) ^ 2) ^ 2 := by
      dsimp only [Gamma]
      ring
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
  classical
  let D : Finset (ZMod N) := Gamma.image Prod.fst
  let delta : Real := (D.card : Real) / N
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdeltaCard : (D.card : Real) = delta * N := by
    dsimp only [delta]
    field_simp
  have hthetaDelta : theta ≤ delta := by
    apply (le_div_iff₀ hN).2
    simpa only [D] using hproj
  have hdelta : 0 < delta := htheta.trans_le hthetaDelta
  let pairOf (h : ↥D) : Pair N :=
    Classical.choose (Finset.mem_image.mp h.property)
  have hpairOf (h : ↥D) :
      pairOf h ∈ Gamma ∧ (pairOf h).1 = h := by
    exact Classical.choose_spec (Finset.mem_image.mp h.property)
  let sigma : ZMod N → ZMod N := fun h =>
    if hh : h ∈ D then (pairOf ⟨h, hh⟩).2 else 0
  have hsigma (h : ZMod N) (hh : h ∈ D) : (h, sigma h) ∈ Gamma := by
    have hp := hpairOf ⟨h, hh⟩
    have heq : (h, sigma h) = pairOf ⟨h, hh⟩ := by
      apply Prod.ext
      · exact hp.2.symm
      · simp only [sigma, dif_pos hh]
    rw [heq]
    exact hp.1
  have hlarge (h : ZMod N) (hh : h ∈ D) :
      theta * (N : Real) ^ 2 ≤
        ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ := by
    have hm := hGamma (hsigma h hh)
    simpa [cor133LargePairs] using hm
  let alpha13 : Real := theta ^ 2 * delta
  have halpha13 : 0 < alpha13 := by
    dsimp only [alpha13]
    exact mul_pos (pow_pos htheta 2) hdelta
  have hsum :
      alpha13 * (N : Real) ^ 5 ≤
        ∑ h ∈ D,
          ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 := by
    calc
      alpha13 * (N : Real) ^ 5 =
          (D.card : Real) * (theta * (N : Real) ^ 2) ^ 2 := by
        dsimp only [alpha13]
        rw [hdeltaCard]
        ring
      _ = ∑ _h ∈ D, (theta * (N : Real) ^ 2) ^ 2 := by simp
      _ ≤ ∑ h ∈ D,
          ‖fourier (verticalEdgeFiberFunction A h) (sigma h)‖ ^ 2 := by
        exact Finset.sum_le_sum fun h hh =>
          pow_le_pow_left₀ (by positivity) (hlarge h hh) 2
  have hadd := corollary_13_2_holds N A D sigma alpha13 halpha13 hsum
  let gamma7 : Real := theta ^ 8 * delta
  have hgamma7 : 0 < gamma7 := by
    dsimp only [gamma7]
    exact mul_pos (pow_pos htheta 8) hdelta
  have hquad :
      gamma7 * (delta * N) ^ 3 ≤ phiAdditiveCount D sigma := by
    calc
      gamma7 * (delta * N) ^ 3 =
          alpha13 ^ 4 * (N : Real) ^ 3 := by
        dsimp only [gamma7, alpha13]
        ring
      _ ≤ (phiAdditiveCount D sigma : Real) := hadd
  obtain ⟨B, hBD, hBsize, hFreiman⟩ :=
    corollary_7_6_holds N D sigma delta gamma7 hprime hdelta hgamma7
      hdeltaCard hquad
  refine ⟨B, sigma, ?_, hFreiman, ?_⟩
  · intro p hp
    have hp' := (show p.1 ∈ B ∧ p.2 = sigma p.1 by
      simpa [functionGraph, Prod.ext_iff, eq_comm] using hp)
    have hm := hsigma p.1 (hBD hp'.1)
    change (p.1, p.2) ∈ Gamma
    rw [hp'.2]
    exact hm
  · have hdeltaPow : theta ^ 1165 ≤ delta ^ 1165 :=
      pow_le_pow_left₀ htheta.le hthetaDelta 1165
    have hpow :
        theta ^ 10477 ≤ (theta ^ 8 * delta) ^ 1164 * delta := by
      calc
        theta ^ 10477 = theta ^ 9312 * theta ^ 1165 := by ring
        _ ≤ theta ^ 9312 * delta ^ 1165 := by
          gcongr
        _ = (theta ^ 8 * delta) ^ 1164 * delta := by ring
    have htwo : (2 : Real) ^ (-(1882 : Int)) =
        (2 : Real) ^ (-(1882 : Real)) := by
      rw [← Real.rpow_intCast]
      norm_num
    calc
      (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N ≤
          (2 : Real) ^ (-(1882 : Int)) *
            ((theta ^ 8 * delta) ^ 1164 * delta) * N := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
      _ = (2 : Real) ^ (-(1882 : Int)) * gamma7 ^ 1164 * delta * N := by
        dsimp only [gamma7]
        ring
      _ = (2 : Real) ^ (-(1882 : Real)) * gamma7 ^ 1164 * delta * N := by
        rw [htwo]
      _ ≤ B.card := hBsize

private noncomputable def cor133_build_cover {N : Nat} [NeZero N]
    (A : Finset (Pair N)) (theta : Real) (hprime : Nat.Prime N)
    (htheta : 0 < theta) :
    ∀ Gamma : Finset (Pair N), Gamma ⊆ cor133LargePairs A theta →
      Cor133CoverData N theta Gamma := by
  classical
  intro Gamma
  refine Finset.strongInductionOn Gamma ?_
  intro Gamma ih hGamma
  let D : Finset (ZMod N) := Gamma.image Prod.fst
  by_cases hsmall : (D.card : Real) < theta * N
  · let G : Finset (ZMod N) := Finset.univ \ D
    have hDcard : D.card ≤ N := by
      calc
        D.card ≤ (Finset.univ : Finset (ZMod N)).card :=
          Finset.card_le_card (Finset.subset_univ D)
        _ = N := by simp [ZMod.card]
    have hGcard : (G.card : Real) = N - D.card := by
      rw [show G = Finset.univ \ D by rfl]
      rw [Finset.card_sdiff]
      simp [ZMod.card, Nat.cast_sub hDcard]
    let B : Fin 0 → Finset (ZMod N) := Fin.elim0
    let sigma : Fin 0 → ZMod N → ZMod N := Fin.elim0
    refine
      { q := 0
        B := B
        sigma := sigma
        G := G
        G_large := ?_
        freiman := ?_
        piece_large := ?_
        budget := ?_
        covers := ?_ }
    · rw [hGcard]
      nlinarith
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · simp
    · intro p hp hpG
      exfalso
      have hpD : p.1 ∈ D := Finset.mem_image.2 ⟨p, hp, rfl⟩
      exact (Finset.mem_sdiff.mp hpG).2 hpD
  · have hproj : theta * N ≤ (Gamma.image Prod.fst).card := by
      simpa only [D] using le_of_not_gt hsmall
    have hextract :=
      cor133_extract_piece A theta hprime htheta Gamma hGamma hproj
    let B0 := Classical.choose hextract
    have hextractB := Classical.choose_spec hextract
    let sigma0 := Classical.choose hextractB
    have hextractSpec := Classical.choose_spec hextractB
    have hPsub := hextractSpec.1
    have hFreiman0 := hextractSpec.2.1
    have hB0size := hextractSpec.2.2
    let P := functionGraph B0 sigma0
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hscalePos :
        0 < (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N := by
      exact mul_pos
        (mul_pos (zpow_pos (by norm_num : (0 : Real) < 2) _)
          (pow_pos htheta 10477))
        (by exact_mod_cast NeZero.pos N)
    have hB0nonempty : B0.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast hscalePos.trans_le hB0size
    have hPnonempty : P.Nonempty := by
      obtain ⟨b, hb⟩ := hB0nonempty
      refine ⟨(b, sigma0 b), ?_⟩
      simp [P, functionGraph, hb]
    have hremain_lt : Gamma \ P ⊂ Gamma :=
      Finset.sdiff_ssubset hPsub hPnonempty
    have hremainSub : Gamma \ P ⊆ cor133LargePairs A theta :=
      Finset.sdiff_subset.trans hGamma
    let tail := ih (Gamma \ P) hremain_lt hremainSub
    let B : Fin (tail.q + 1) → Finset (ZMod N) :=
      Fin.cases B0 tail.B
    let sigma : Fin (tail.q + 1) → ZMod N → ZMod N :=
      Fin.cases sigma0 tail.sigma
    refine
      { q := tail.q + 1
        B := B
        sigma := sigma
        G := tail.G
        G_large := tail.G_large
        freiman := ?_
        piece_large := ?_
        budget := ?_
        covers := ?_ }
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hFreiman0
      · exact tail.freiman j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hB0size
      · exact tail.piece_large j
    · have hPcard : P.card = B0.card := cor133_card_functionGraph B0 sigma0
      have hcards : (Gamma \ P).card + P.card = Gamma.card := by
        rw [Finset.card_sdiff_add_card]
        rw [Finset.union_eq_left.mpr hPsub]
      have hcardsR :
          ((Gamma \ P).card : Real) + B0.card = Gamma.card := by
        exact_mod_cast (by simpa [hPcard] using hcards)
      have hqcast : ((tail.q + 1 : Nat) : Real) = tail.q + 1 := by norm_num
      rw [hqcast]
      nlinarith [tail.budget, hB0size]
    · intro p hp hpG
      by_cases hpP : p ∈ P
      · have hp' : p.1 ∈ B0 ∧ p.2 = sigma0 p.1 := by
          simpa [P, functionGraph, Prod.ext_iff, eq_comm] using hpP
        refine ⟨0, ?_, ?_⟩
        · exact hp'.1
        · exact hp'.2
      · obtain ⟨j, hjB, hjSigma⟩ :=
          tail.covers p (Finset.mem_sdiff.2 ⟨hp, hpP⟩) hpG
        exact ⟨j.succ, hjB, hjSigma⟩

/-- Gowers's Corollary 13.3, with the prime-modulus convention explicit. -/
theorem corollary_13_3_holds : corollary_13_3 := by
  intro N _ A theta hprime htheta
  classical
  let Gamma := cor133LargePairs A theta
  let cover := cor133_build_cover A theta hprime htheta Gamma
    (show Gamma ⊆ cor133LargePairs A theta by rfl)
  refine ⟨cover.q, cover.B, cover.sigma, cover.G, cover.G_large,
    cover.freiman, cover.piece_large, ?_, ?_⟩
  · have hGammaCard := cor133_largePairs_card_le A theta htheta
    have hproduct :
        (cover.q : Real) *
            ((2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) ≤
          theta ^ (-(2 : Int)) * N := cover.budget.trans hGammaCard
    have hscalePos :
        0 < (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N := by
      exact mul_pos
        (mul_pos (zpow_pos (by norm_num : (0 : Real) < 2) _)
          (pow_pos htheta 10477))
        (by exact_mod_cast NeZero.pos N)
    have htwo :
        (2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int)) = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
      norm_num
    have hthetaPow :
        theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat) =
          theta ^ (-(2 : Int)) := by
      rw [← zpow_natCast, ← zpow_add₀ htheta.ne']
      norm_num
    apply le_of_mul_le_mul_right (a :=
      (2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) ?_ hscalePos
    calc
      (cover.q : Real) *
          ((2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) ≤
          theta ^ (-(2 : Int)) * N := hproduct
      _ = ((2 : Real) ^ (1882 : Nat) * theta ^ (-(10479 : Int))) *
          ((2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) := by
        rw [show
          ((2 : Real) ^ (1882 : Nat) * theta ^ (-(10479 : Int))) *
              ((2 : Real) ^ (-(1882 : Int)) * theta ^ 10477 * N) =
            ((2 : Real) ^ (1882 : Nat) * (2 : Real) ^ (-(1882 : Int))) *
              (theta ^ (-(10479 : Int)) * theta ^ (10477 : Nat)) * N by ac_rfl]
        rw [htwo, hthetaPow]
        ring
  · intro h hh r hr
    have hp : (h, r) ∈ Gamma := by
      simpa [Gamma, cor133LargePairs] using hr
    exact cover.covers (h, r) hp hh

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Proofs00Basics

/-!
# Extracting a local difference model in Section 10

This module proves the corrected Lemma 10.6 (`lemma_10_6_holds`). The audit of
the live statement, a finite model of its hypotheses in which no local
difference model exists (`lemma_10_6_counterexample`), is in
`Proofs10ExtractionSide`, outside the final route. -/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Companion proof for the corrected statement -/

private lemma extraction_almostEvery_bad_card_le {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P] (hP : AlmostEvery (1 - a) U P) :
    ((U.filter fun y => ¬ P y).card : Real) ≤ a * U.card := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  linarith

private lemma extraction_bad_card_lt_of_not_almostEvery {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P] (hP : ¬ AlmostEvery (1 - a) U P) :
    a * U.card < ((U.filter fun y => ¬ P y).card : Real) := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  push Not at hP
  linarith

private lemma extraction_almostEvery_of_bad_card_le {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P]
    (hbad : ((U.filter fun y => ¬ P y).card : Real) ≤ a * U.card) :
    AlmostEvery (1 - a) U P := by
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable]
  linarith

private noncomputable def extractionBadPairs {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x w : X) (d : ZMod N) : Finset (X × X) :=
  ((D.fibre (D.index x + d)).product
      (D.fibre (D.index w + d))).filter fun yz =>
    phi yz.1 - phi x ≠ phi yz.2 - phi w

private def extractionDirectionGood {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x w : X) (d : ZMod N) (t : Real) : Prop :=
  AlmostEvery (1 - 35 * t ^ 2)
    ((D.fibre (D.index x + d)).product (D.fibre (D.index w + d)))
    (fun yz => phi yz.1 - phi x = phi yz.2 - phi w)

private lemma extraction_restricted_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N)) (x w : X)
    (uv : X × X) :
    (if D.index uv.1 - D.index x = D.index uv.2 - D.index w ∧
        D.index uv.1 - D.index x ∈ B then 1 else 0) =
      ∑ d ∈ B, if D.index uv.1 = D.index x + d ∧
        D.index uv.2 = D.index w + d then 1 else 0 := by
  by_cases hrel : D.index uv.1 - D.index x =
      D.index uv.2 - D.index w ∧ D.index uv.1 - D.index x ∈ B
  · rw [if_pos hrel]
    let d₀ : ZMod N := D.index uv.1 - D.index x
    have hd₀ : d₀ ∈ B := hrel.2
    rw [Finset.sum_eq_single d₀]
    · have hu : D.index uv.1 = D.index x + d₀ := by ring
      have hv : D.index uv.2 = D.index w + d₀ := by
        dsimp only [d₀]
        linear_combination hrel.1.symm
      simp [hu, hv]
    · intro d _ hdne
      rw [if_neg]
      intro huv
      apply hdne
      dsimp only [d₀]
      linear_combination huv.1.symm
    · exact fun hd₀not => (hd₀not hd₀).elim
  · rw [if_neg hrel]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro huv
    apply hrel
    constructor
    · rw [huv.1, huv.2]
      abel
    · have hu : D.index uv.1 - D.index x = d := by
        rw [huv.1]
        abel
      rw [hu]
      exact hd

private lemma extraction_error_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (x w : X) (uv : X × X) :
    (if D.index uv.1 - D.index x = D.index uv.2 - D.index w ∧
        D.index uv.1 - D.index x ∈ B ∧
        (phi uv.1 - phi x != phi uv.2 - phi w) = true then 1 else 0) =
      ∑ d ∈ B, if D.index uv.1 = D.index x + d ∧
        D.index uv.2 = D.index w + d ∧
        (phi uv.1 - phi x != phi uv.2 - phi w) = true then 1 else 0 := by
  by_cases hphi : (phi uv.1 - phi x != phi uv.2 - phi w) = true
  · simp only [hphi, and_true]
    exact extraction_restricted_ite_eq_sum D B x w uv
  · simp [hphi]

private lemma extraction_restrictedWeight_eq_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x w : X) :
    domainRestrictedDifferenceWeight D B x w =
      ∑ d ∈ B, (D.fibre (D.index x + d)).card *
        (D.fibre (D.index w + d)).card := by
  unfold domainRestrictedDifferenceWeight
  rw [countWhere_eq_sum_ite]
  simp_rw [extraction_restricted_ite_eq_sum D B x w]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← countWhere_eq_sum_ite]
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.univ.filter fun uv : X × X =>
      D.index uv.1 = D.index x + d ∧ D.index uv.2 = D.index w + d) =
      (D.fibre (D.index x + d)).product
        (D.fibre (D.index w + d)) by
    ext uv
    simp [MultifunctionDomain.fibre]]
  simp

private lemma extraction_errorCount_eq_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x w : X) :
    domainDifferenceErrorCount D phi B x w =
      ∑ d ∈ B, (extractionBadPairs D phi x w d).card := by
  unfold domainDifferenceErrorCount
  rw [countWhere_eq_sum_ite]
  simp_rw [extraction_error_ite_eq_sum D phi B x w]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← countWhere_eq_sum_ite]
  unfold countWhere extractionBadPairs
  rw [Finset.filter_congr_decidable]
  congr 1
  ext uv
  simp [MultifunctionDomain.fibre, and_assoc]

private lemma extraction_sigma_le_alpha_sq_div_64 {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M : Nat) (sigma eta : Real)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16) :
    sigma ≤ alpha ^ 2 / 64 := by
  rcases hsetup with ⟨⟨halpha, halphaOne, _hM, _hcard, _hfibre⟩,
    hsigmaPos, heta, hetaOne, _hsym, _hinv, _happrox⟩
  have hmulPositive : 0 < eta * rho * alpha ^ 2 := by linarith
  have hetaRhoPositive : 0 < eta * rho := by
    rcases (mul_pos_iff.mp hmulPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg alpha) h.2).elim
  have hrhoPositive : 0 < rho := by
    rcases (mul_pos_iff.mp hetaRhoPositive) with h | h
    · exact h.2
    · exact (not_lt_of_ge heta h.1).elim
  have hetaRhoUpper : eta * rho ≤ alpha ^ 2 / 32 :=
    (mul_le_of_le_one_left hrhoPositive.le hetaOne).trans hrho
  have halphaSqOne : alpha ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr halphaOne)
      (show 0 ≤ 1 + alpha by linarith)]
  have halphaFourth : alpha ^ 2 * alpha ^ 2 ≤ alpha ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg alpha) halphaSqOne
  calc
    sigma ≤ eta * rho * alpha ^ 2 / 16 := hsigma
    _ ≤ (alpha ^ 2 / 32) * alpha ^ 2 / 16 := by
      gcongr
    _ ≤ alpha ^ 2 / 64 := by
      nlinarith

private lemma extraction_sigmaM_le_anchor_quarter {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M : Nat) (sigma eta : Real) (x : X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hanchor : IsSection10Anchor D phi B alpha M N eta x)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16) :
    sigma * M ≤ (D.fibreSize x : Real) / 4 := by
  have hs := extraction_sigma_le_alpha_sq_div_64 D phi B alpha rho M
    sigma eta hsetup hrho hsigma
  have hMnonneg : (0 : Real) ≤ M := by positivity
  have hsM : sigma * M ≤ alpha ^ 2 / 64 * M :=
    mul_le_mul_of_nonneg_right hs hMnonneg
  have hx := hanchor.1
  nlinarith

private lemma extraction_sigmaM_le_regular_quarter {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M N0 : Nat) (sigma eta : Real) (x w : X)
    (W : Finset X) (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N0 W)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16)
    (hw : w ∈ W) :
    sigma * M ≤ (D.fibreSize w : Real) / 4 := by
  have hs := extraction_sigma_le_alpha_sq_div_64 D phi B alpha rho M
    sigma eta hsetup hrho hsigma
  have hMnonneg : (0 : Real) ≤ M := by positivity
  have hsM : sigma * M ≤ alpha ^ 2 / 64 * M :=
    mul_le_mul_of_nonneg_right hs hMnonneg
  have hwLower := hregular.2.2.2.2.2.1 w hw
  nlinarith

private lemma extraction_shifted_fibre_bounds {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (sigma : Real) (M : Nat) (u : X)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hquarter : sigma * M ≤ (D.fibreSize u : Real) / 4)
    (d : ZMod N) (hd : d ∈ B) :
    (3 : Real) / 4 * D.fibreSize u ≤
        (D.fibre (D.index u + d)).card ∧
      ((D.fibre (D.index u + d)).card : Real) ≤
        (5 : Real) / 4 * D.fibreSize u := by
  have h := abs_le.mp (hinvariant (D.index u) d hd)
  unfold MultifunctionDomain.fibreSize at hquarter ⊢
  constructor <;> linarith

private lemma extraction_fibre_product_le_four {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (sigma : Real) (M : Nat) (x w : X)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hxQuarter : sigma * M ≤ (D.fibreSize x : Real) / 4)
    (hwQuarter : sigma * M ≤ (D.fibreSize w : Real) / 4)
    (d : ZMod N) (hd : d ∈ B) (e : ZMod N) (he : e ∈ B) :
    ((D.fibre (D.index x + d)).card : Real) *
        (D.fibre (D.index w + d)).card ≤
      4 * (((D.fibre (D.index x + e)).card : Real) *
        (D.fibre (D.index w + e)).card) := by
  have hxd := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter d hd
  have hxe := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter e he
  have hwd := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter d hd
  have hwe := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter e he
  have hxCompare : ((D.fibre (D.index x + d)).card : Real) ≤
      2 * (D.fibre (D.index x + e)).card := by linarith
  have hwCompare : ((D.fibre (D.index w + d)).card : Real) ≤
      2 * (D.fibre (D.index w + e)).card := by linarith
  calc
    ((D.fibre (D.index x + d)).card : Real) *
          (D.fibre (D.index w + d)).card ≤
        (2 * (D.fibre (D.index x + e)).card) *
          (D.fibre (D.index w + d)).card := by gcongr
    _ ≤ (2 * (D.fibre (D.index x + e)).card) *
          (2 * (D.fibre (D.index w + e)).card) := by gcongr
    _ = 4 * (((D.fibre (D.index x + e)).card : Real) *
          (D.fibre (D.index w + e)).card) := by ring

private lemma extraction_direction_good_almostEvery {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat)
    (sigma eta t : Real) (x w : X) (W : Finset X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hanchor : IsSection10Anchor D phi B alpha M N eta x)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N W)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16)
    (ht : 0 < t) (hw : w ∈ W)
    (hwError : domainProportionateError D phi B x w ≤ 300 * t ^ 4) :
    AlmostEvery (1 - 35 * t ^ 2) B
      (fun d => extractionDirectionGood D phi x w d t) := by
  classical
  by_cases hBempty : B = ∅
  · subst B
    unfold AlmostEvery
    simp
  have hBnonempty : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBempty
  let P : ZMod N → Real := fun d =>
    ((D.fibre (D.index x + d)).card : Real) *
      (D.fibre (D.index w + d)).card
  let BadD : Finset (ZMod N) :=
    B.filter fun d => ¬ extractionDirectionGood D phi x w d t
  apply extraction_almostEvery_of_bad_card_le
  change (BadD.card : Real) ≤ 35 * t ^ 2 * B.card
  by_contra hBadBound
  have hBadGt : 35 * t ^ 2 * (B.card : Real) < BadD.card :=
    lt_of_not_ge hBadBound
  have hBadPositiveReal : 0 < (BadD.card : Real) :=
    (mul_nonneg (by positivity) (by positivity)).trans_lt hBadGt
  have hBadNonempty : BadD.Nonempty := Finset.card_pos.mp (by exact_mod_cast hBadPositiveReal)
  obtain ⟨d₀, hd₀B, hd₀min⟩ := B.exists_min_image P hBnonempty
  have hxQuarter := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hwQuarter := extraction_sigmaM_le_regular_quarter D phi B alpha rho M N
    sigma eta x w W hsetup hregular hrho hsigma hw
  have hinvariant := hsetup.2.2.2.2.2.1
  have hprodCompare (d : ZMod N) (hd : d ∈ B) : P d ≤ 4 * P d₀ := by
    exact extraction_fibre_product_le_four D B sigma M x w hinvariant
      hxQuarter hwQuarter d hd d₀ hd₀B
  have hxBasePos : 0 < (D.fibreSize x : Real) := by
    have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
    have halpha := hsetup.1.1
    exact (show 0 < alpha ^ 2 * M / 2 by positivity).trans_le hanchor.1
  have hwBasePos : 0 < (D.fibreSize w : Real) := by
    have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
    have halpha := hsetup.1.1
    exact (show 0 < alpha ^ 2 * M / 16 by positivity).trans_le
      (hregular.2.2.2.2.2.1 w hw)
  have hxd₀ := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter d₀ hd₀B
  have hwd₀ := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter d₀ hd₀B
  have hxd₀Pos : 0 < ((D.fibre (D.index x + d₀)).card : Real) := by
    linarith
  have hwd₀Pos : 0 < ((D.fibre (D.index w + d₀)).card : Real) := by
    linarith
  have hP₀Pos : 0 < P d₀ := by positivity
  have hbEq : (domainRestrictedDifferenceWeight D B x w : Real) =
      ∑ d ∈ B, P d := by
    rw [extraction_restrictedWeight_eq_sum]
    push_cast
    rfl
  have hbUpper : (domainRestrictedDifferenceWeight D B x w : Real) ≤
      4 * (B.card : Real) * P d₀ := by
    rw [hbEq]
    calc
      (∑ d ∈ B, P d) ≤ ∑ _d ∈ B, 4 * P d₀ := by
        apply Finset.sum_le_sum
        intro d hd
        exact hprodCompare d hd
      _ = 4 * (B.card : Real) * P d₀ := by
        simp
        ring
  have hbLower : P d₀ ≤
      (domainRestrictedDifferenceWeight D B x w : Real) := by
    rw [hbEq]
    exact Finset.single_le_sum
      (fun d (_hd : d ∈ B) => by dsimp only [P]; positivity) hd₀B
  have hbPos : 0 < (domainRestrictedDifferenceWeight D B x w : Real) :=
    hP₀Pos.trans_le hbLower
  have hdirBad (d : ZMod N) (hd : d ∈ BadD) :
      35 * t ^ 2 * P d < ((extractionBadPairs D phi x w d).card : Real) := by
    have hdNot := (Finset.mem_filter.mp hd).2
    have hbad := extraction_bad_card_lt_of_not_almostEvery
      (35 * t ^ 2)
      ((D.fibre (D.index x + d)).product (D.fibre (D.index w + d)))
      (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) hdNot
    simpa [extractionDirectionGood, extractionBadPairs, P] using hbad
  have hsumStrict :
      (∑ _d ∈ BadD, 35 * t ^ 2 * P d₀) <
        ∑ d ∈ BadD, ((extractionBadPairs D phi x w d).card : Real) := by
    apply Finset.sum_lt_sum_of_nonempty hBadNonempty
    intro d hd
    calc
      35 * t ^ 2 * P d₀ ≤ 35 * t ^ 2 * P d := by
        gcongr
        exact hd₀min d (Finset.filter_subset _ _ hd)
      _ < ((extractionBadPairs D phi x w d).card : Real) := hdirBad d hd
  have hsumBadLe :
      (∑ d ∈ BadD, ((extractionBadPairs D phi x w d).card : Real)) ≤
        domainDifferenceErrorCount D phi B x w := by
    rw [extraction_errorCount_eq_sum]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro d hdB _hdBad
      positivity
  have hfactorPos : 0 < 35 * t ^ 2 * P d₀ := by positivity
  have hscaled := mul_lt_mul_of_pos_left hBadGt hfactorPos
  have herrorLower :
      1225 * t ^ 4 * (B.card : Real) * P d₀ <
        domainDifferenceErrorCount D phi B x w := by
    calc
      1225 * t ^ 4 * (B.card : Real) * P d₀ =
          (35 * t ^ 2 * P d₀) * (35 * t ^ 2 * B.card) := by ring
      _ < (35 * t ^ 2 * P d₀) * BadD.card := hscaled
      _ = ∑ _d ∈ BadD, 35 * t ^ 2 * P d₀ := by simp; ring
      _ < ∑ d ∈ BadD,
          ((extractionBadPairs D phi x w d).card : Real) := hsumStrict
      _ ≤ domainDifferenceErrorCount D phi B x w := hsumBadLe
  have herrorUpper :
      (domainDifferenceErrorCount D phi B x w : Real) ≤
        300 * t ^ 4 * domainRestrictedDifferenceWeight D B x w := by
    unfold domainProportionateError at hwError
    exact (div_le_iff₀ hbPos).mp hwError
  have hupperFinal :
      (domainDifferenceErrorCount D phi B x w : Real) ≤
        1200 * t ^ 4 * (B.card : Real) * P d₀ := by
    calc
      (domainDifferenceErrorCount D phi B x w : Real) ≤
          300 * t ^ 4 * domainRestrictedDifferenceWeight D B x w := herrorUpper
      _ ≤ 300 * t ^ 4 * (4 * (B.card : Real) * P d₀) := by
        gcongr
      _ = 1200 * t ^ 4 * (B.card : Real) * P d₀ := by ring
  have hBcardPos : (0 : Real) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hBnonempty
  have : 0 < t ^ 4 * (B.card : Real) * P d₀ := by positivity
  nlinarith

private lemma extraction_agreement_card_eq_sum {Y Z L : Type*}
    [DecidableEq Y] [DecidableEq Z] [DecidableEq L]
    (A : Finset Y) (C : Finset Z) (f : Y → L) (g : Z → L) :
    ((A.product C).filter fun yz => f yz.1 = g yz.2).card =
      ∑ z ∈ C, (A.filter fun y => f y = g z).card := by
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ A ×ˢ C, if f yz.1 = g yz.2 then 1 else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp_rw [Finset.card_filter]

private noncomputable def extractionMode {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x : X) (d : ZMod N) : ZMod N :=
  Classical.choose (Finite.exists_max fun a : ZMod N =>
    ((D.fibre (D.index x + d)).filter fun y => phi y - phi x = a).card)

private lemma extractionMode_max {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x : X) (d a : ZMod N) :
    ((D.fibre (D.index x + d)).filter fun y =>
        phi y - phi x = a).card ≤
      ((D.fibre (D.index x + d)).filter fun y =>
        phi y - phi x = extractionMode D phi x d).card :=
  Classical.choose_spec (Finite.exists_max fun a : ZMod N =>
    ((D.fibre (D.index x + d)).filter fun y => phi y - phi x = a).card) a

private lemma extraction_directionGood_gives_mode {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (x w : X) (d : ZMod N) (t : Real)
    (ht : 0 < t) (htUpper : t < 1 / 10)
    (hanchorFibre : 0 < ((D.fibre (D.index x + d)).card : Real))
    (hgood : extractionDirectionGood D phi x w d t) :
    AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d))
      (fun z => phi z - phi w = extractionMode D phi x d) := by
  let A : Finset X := D.fibre (D.index x + d)
  let C : Finset X := D.fibre (D.index w + d)
  let m : ZMod N := extractionMode D phi x d
  let Am : Finset X := A.filter fun y => phi y - phi x = m
  let Cm : Finset X := C.filter fun z => phi z - phi w = m
  let E : Finset (X × X) := (A.product C).filter fun yz =>
    phi yz.1 - phi x = phi yz.2 - phi w
  let Ebad : Finset (X × X) := (A.product C).filter fun yz =>
    phi yz.1 - phi x ≠ phi yz.2 - phi w
  by_cases hCempty : C = ∅
  · unfold AlmostEvery
    simp [C, hCempty]
  have hCpos : (0 : Real) < C.card := by
    exact_mod_cast Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hCempty)
  have hEdgeLower :
      (1 - 35 * t ^ 2) * (A.card : Real) * C.card ≤ E.card := by
    have hgood' := hgood
    unfold extractionDirectionGood AlmostEvery at hgood'
    rw [Finset.filter_congr_decidable] at hgood'
    rw [mul_assoc, ← Nat.cast_mul, ← Finset.card_product]
    simpa only [A, C, E, Finset.product_eq_sprod] using hgood'
  have hEdgeUpperNat : E.card ≤ Am.card * C.card := by
    calc
      E.card = ∑ z ∈ C,
          (A.filter fun y => phi y - phi x = phi z - phi w).card := by
        exact extraction_agreement_card_eq_sum A C
          (fun y => phi y - phi x) (fun z => phi z - phi w)
      _ ≤ ∑ _z ∈ C, Am.card := by
        apply Finset.sum_le_sum
        intro z _
        dsimp only [Am, m, A]
        exact extractionMode_max D phi x d (phi z - phi w)
      _ = Am.card * C.card := by simp [mul_comm]
  have hEdgeUpper : (E.card : Real) ≤ Am.card * C.card := by
    exact_mod_cast hEdgeUpperNat
  have hModeLower :
      (1 - 35 * t ^ 2) * (A.card : Real) ≤ Am.card := by
    apply le_of_mul_le_mul_right _ hCpos
    calc
      (1 - 35 * t ^ 2) * (A.card : Real) * C.card ≤ E.card := hEdgeLower
      _ ≤ (Am.card : Real) * C.card := hEdgeUpper
  have hBadEdgeUpper : (Ebad.card : Real) ≤
      35 * t ^ 2 * (A.card : Real) * C.card := by
    have hbad := extraction_almostEvery_bad_card_le (35 * t ^ 2)
      (A.product C)
      (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) hgood
    simpa [Ebad, Finset.card_product, mul_assoc] using hbad
  have hrectangleSubset : Am.product (C \ Cm) ⊆ Ebad := by
    intro yz hyz
    have hyzParts := Finset.mem_product.mp hyz
    have hyAm := Finset.mem_filter.mp hyzParts.1
    have hzBad := Finset.mem_sdiff.mp hyzParts.2
    have hzC := hzBad.1
    have hzNot := hzBad.2
    have hzNe : phi yz.2 - phi w ≠ m := by
      exact fun hzEq => hzNot (Finset.mem_filter.mpr ⟨hzC, hzEq⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hyAm.1, hzC⟩,
      fun heq => hzNe (heq ▸ hyAm.2)⟩
  have hrectangle : (Am.card : Real) * (C \ Cm).card ≤ Ebad.card := by
    exact_mod_cast (Finset.card_product Am (C \ Cm)).symm.trans_le
      (Finset.card_le_card hrectangleSubset)
  have hModeBad : (Am.card : Real) * (C \ Cm).card ≤
      35 * t ^ 2 * (A.card : Real) * C.card :=
    hrectangle.trans hBadEdgeUpper
  have hp : 0 < 1 - 35 * t ^ 2 := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le)]
  have hcancelA :
      (1 - 35 * t ^ 2) * ((C \ Cm).card : Real) ≤
        35 * t ^ 2 * C.card := by
    refine le_of_mul_le_mul_left ?_ hanchorFibre
    linarith [hModeBad, mul_le_mul_of_nonneg_right hModeLower (Nat.cast_nonneg (C \ Cm).card)]
  have hnumeric : 35 * t ^ 2 ≤ 10 * t * (1 - 35 * t ^ 2) := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le),
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htUpper.le)]
  have htargetBad : ((C \ Cm).card : Real) ≤ 10 * t * C.card := by
    refine le_of_mul_le_mul_left ?_ hp
    linarith [hcancelA, mul_le_mul_of_nonneg_right hnumeric (Nat.cast_nonneg C.card)]
  have hdiff : C \ Cm = C.filter fun z =>
      ¬ (phi z - phi w = extractionMode D phi x d) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    dsimp only [Cm, m]
    simp only [Finset.mem_filter]
    tauto
  apply extraction_almostEvery_of_bad_card_le
  rw [← hdiff]
  simpa only [C] using htargetBad

private lemma extraction_product_filter_card_first {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (P : Y → Z → Prop) [DecidableRel P] :
    ((U.product V).filter fun yz : Y × Z => P yz.1 yz.2).card =
      ∑ y ∈ U, (V.filter fun z : Z => P y z).card := by
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ U ×ˢ V, if P yz.1 yz.2 then 1 else 0) = _
  rw [Finset.sum_product]
  simp_rw [Finset.card_filter]

private lemma extraction_product_filter_card_second {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (P : Y → Z → Prop) [DecidableRel P] :
    ((U.product V).filter fun yz : Y × Z => P yz.1 yz.2).card =
      ∑ z ∈ V, (U.filter fun y : Y => P y z).card := by
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ U ×ˢ V, if P yz.1 yz.2 then 1 else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp_rw [Finset.card_filter]

private lemma extraction_select_directions {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (Q : Y → Z → Prop) (t : Real) (ht : 0 < t)
    (hrow : ∀ y, y ∈ U →
      AlmostEvery (1 - 35 * t ^ 2) V (Q y)) :
    AlmostEvery (1 - 7 * t) V fun z =>
      AlmostEvery (1 - 5 * t) U fun y => Q y z := by
  classical
  by_cases hUempty : U = ∅
  · subst U
    unfold AlmostEvery
    rw [Finset.filter_eq_self.2]
    · have _ : (0 : Real) ≤ V.card := by positivity
      nlinarith
    · intro z _
      simp
  have hUnonempty : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
  let BadPair : Finset (Y × Z) :=
    (U.product V).filter fun yz => ¬ Q yz.1 yz.2
  let H : Finset Z := V.filter fun z =>
    ¬ AlmostEvery (1 - 5 * t) U (fun y => Q y z)
  apply extraction_almostEvery_of_bad_card_le
  change (H.card : Real) ≤ 7 * t * V.card
  by_contra hHBound
  have hHGt : 7 * t * (V.card : Real) < H.card := lt_of_not_ge hHBound
  have hHPosReal : 0 < (H.card : Real) := (mul_nonneg (by positivity) (by positivity)).trans_lt hHGt
  have hHnonempty : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hHPosReal)
  have hBadRows : BadPair.card =
      ∑ y ∈ U, (V.filter fun z => ¬ Q y z).card := by
    exact extraction_product_filter_card_first U V (fun y z => ¬ Q y z)
  have hBadUpper : (BadPair.card : Real) ≤
      35 * t ^ 2 * (V.card : Real) * U.card := by
    rw [hBadRows]
    push_cast
    calc
      (∑ y ∈ U, ((V.filter fun z => ¬ Q y z).card : Real)) ≤
          ∑ _y ∈ U, 35 * t ^ 2 * V.card := by
        apply Finset.sum_le_sum
        intro y hy
        exact extraction_almostEvery_bad_card_le (35 * t ^ 2) V (Q y)
          (hrow y hy)
      _ = 35 * t ^ 2 * (V.card : Real) * U.card := by
        simp
        ring
  have hcolumnBad (z : Z) (hz : z ∈ H) :
      5 * t * (U.card : Real) <
        ((U.filter fun y => ¬ Q y z).card : Real) := by
    have hzNot := (Finset.mem_filter.mp hz).2
    exact extraction_bad_card_lt_of_not_almostEvery (5 * t) U
      (fun y => Q y z) hzNot
  have hsumColumnsStrict :
      (∑ _z ∈ H, 5 * t * (U.card : Real)) <
        ∑ z ∈ H, ((U.filter fun y => ¬ Q y z).card : Real) := by
    exact Finset.sum_lt_sum_of_nonempty hHnonempty hcolumnBad
  have hBadColumns : BadPair.card =
      ∑ z ∈ V, (U.filter fun y => ¬ Q y z).card := by
    exact extraction_product_filter_card_second U V (fun y z => ¬ Q y z)
  have hsumColumnsLe :
      (∑ z ∈ H, ((U.filter fun y => ¬ Q y z).card : Real)) ≤
        BadPair.card := by
    rw [hBadColumns]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro z hzV _hzH
      positivity
  have hfactorPos : 0 < 5 * t * (U.card : Real) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hHGt hfactorPos
  have : 35 * t ^ 2 * (V.card : Real) * U.card < BadPair.card := by
    calc
      35 * t ^ 2 * (V.card : Real) * U.card =
          (5 * t * U.card) * (7 * t * V.card) := by ring
      _ < (5 * t * U.card) * H.card := hscaled
      _ = ∑ _z ∈ H, 5 * t * (U.card : Real) := by simp; ring
      _ < ∑ z ∈ H,
          ((U.filter fun y => ¬ Q y z).card : Real) := hsumColumnsStrict
      _ ≤ (BadPair.card : Real) := hsumColumnsLe
  linarith

private lemma extraction_lift_almostEvery {Y : Type*} [DecidableEq Y]
    (W U : Finset Y) (P : Y → Prop) (a b : Real)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hUW : U ⊆ W)
    (hU : AlmostEvery (1 - a) W (fun y => y ∈ U))
    (hP : AlmostEvery (1 - b) U P) :
    AlmostEvery (1 - (a + b)) W P := by
  classical
  have hbadU := extraction_almostEvery_bad_card_le a W
    (fun y => y ∈ U) hU
  have hbadP := extraction_almostEvery_bad_card_le b U P hP
  have hsubset : (W.filter fun y => ¬ P y) ⊆
      (W.filter fun y => y ∉ U) ∪ (U.filter fun y => ¬ P y) := by
    intro y hy
    have hyParts := Finset.mem_filter.mp hy
    by_cases hyU : y ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyU, hyParts.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyParts.1, hyU⟩)
  have hcardNat : (W.filter fun y => ¬ P y).card ≤
      (W.filter fun y => y ∉ U).card + (U.filter fun y => ¬ P y).card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hcard : ((W.filter fun y => ¬ P y).card : Real) ≤
      ((W.filter fun y => y ∉ U).card : Real) +
        (U.filter fun y => ¬ P y).card := by
    exact_mod_cast hcardNat
  have hUcard : (U.card : Real) ≤ W.card := by
    exact_mod_cast Finset.card_le_card hUW
  apply extraction_almostEvery_of_bad_card_le
  calc
    ((W.filter fun y => ¬ P y).card : Real) ≤
        ((W.filter fun y => y ∉ U).card : Real) +
          (U.filter fun y => ¬ P y).card := hcard
    _ ≤ a * W.card + b * U.card := add_le_add hbadU hbadP
    _ ≤ (a + b) * W.card := by
      have := mul_le_mul_of_nonneg_left hUcard hb
      nlinarith

private lemma extraction_almostEvery_mono {Y : Type*} [DecidableEq Y]
    (p : Real) (U : Finset Y) (P Q : Y → Prop)
    (hP : AlmostEvery p U P) (hPQ : ∀ y, y ∈ U → P y → Q y) :
    AlmostEvery p U Q := by
  classical
  unfold AlmostEvery at hP ⊢
  rw [Finset.filter_congr_decidable] at hP ⊢
  exact hP.trans (by
    exact_mod_cast Finset.card_le_card (fun y hy =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
        hPQ y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩))

/-- **Gowers, Lemma 10.6.**  The proof uses the inherited smallness bound on
`rho` made explicit in the corrected statement. -/
theorem lemma_10_6_holds : lemma_10_6 := by
  classical
  intro N _ X _ _ D phi B alpha rho M sigma eta x W
    hsetup hanchor hregular hrho hsigma
  let t : Real := eta ^ ((1 : Real) / 5)
  have hpositive : 0 < eta * rho * alpha ^ 2 / 16 :=
    hsetup.2.1.trans_le hsigma
  have hmulPositive : 0 < eta * rho * alpha ^ 2 := by linarith
  have hetaRhoPositive : 0 < eta * rho := by
    rcases (mul_pos_iff.mp hmulPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg alpha) h.2).elim
  have heta : 0 ≤ eta := hsetup.2.2.1
  have hetaPos : 0 < eta := by
    rcases (mul_pos_iff.mp hetaRhoPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge heta h.1).elim
  have ht : 0 < t := by positivity
  by_cases htLarge : 1 ≤ 10 * t
  · refine ⟨∅, fun _ => 0, ?_⟩
    refine ⟨Finset.empty_subset _, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      dsimp only [t] at htLarge
      nlinarith
    · intro d hd
      simp at hd
  have htUpper : t < 1 / 10 := by nlinarith
  have htFour : eta ^ ((4 : Real) / 5) = t ^ 4 := by
    dsimp only [t]
    have h := Real.rpow_mul_natCast heta ((1 : Real) / 5) 4
    convert h using 1
    norm_num
  let Low : Finset X := W.filter fun w =>
    domainProportionateError D phi B x w ≤ 300 * t ^ 4
  have hLowAE : AlmostEvery (1 - 5 * t) W (fun w => w ∈ Low) := by
    have h := hregular.2.2.1
    rw [htFour] at h
    change AlmostEvery (1 - 5 * t) W
      (fun w => domainProportionateError D phi B x w ≤ 300 * t ^ 4) at h
    exact extraction_almostEvery_mono (1 - 5 * t) W
      (fun w => domainProportionateError D phi B x w ≤ 300 * t ^ 4)
      (fun w => w ∈ Low) h (fun w hwW hwError =>
        Finset.mem_filter.mpr ⟨hwW, hwError⟩)
  have hrows : ∀ w, w ∈ Low →
      AlmostEvery (1 - 35 * t ^ 2) B
        (fun d => extractionDirectionGood D phi x w d t) := by
    intro w hwLow
    have hwParts := Finset.mem_filter.mp hwLow
    exact extraction_direction_good_almostEvery D phi B alpha rho M sigma eta t
      x w W hsetup hanchor hregular hrho hsigma ht hwParts.1 hwParts.2
  have hselected := extraction_select_directions Low B
    (fun w d => extractionDirectionGood D phi x w d t) t ht hrows
  let Selected : ZMod N → Prop := fun d =>
    AlmostEvery (1 - 5 * t) Low fun w =>
      extractionDirectionGood D phi x w d t
  let B' : Finset (ZMod N) := B.filter Selected
  let psi : ZMod N → ZMod N := fun d => extractionMode D phi x d
  have hB'largeSeven : (1 - 7 * t) * B.card ≤ (B'.card : Real) := by
    change AlmostEvery (1 - 7 * t) B Selected at hselected
    unfold AlmostEvery at hselected
    change (1 - 7 * t) * B.card ≤ (B'.card : Real) at hselected
    exact hselected
  have hB'largeTen : (1 - 10 * t) * B.card ≤ (B'.card : Real) := by
    nlinarith
  have hxQuarter := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hinvariant := hsetup.2.2.2.2.2.1
  refine ⟨B', psi, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [t] using hB'largeTen
  · intro d hdB'
    have hdParts := Finset.mem_filter.mp hdB'
    have hdB := hdParts.1
    have hdSelected := hdParts.2
    dsimp only [Selected] at hdSelected
    have hdirWbase := extraction_lift_almostEvery W Low
      (fun w => extractionDirectionGood D phi x w d t)
      (5 * t) (5 * t) (by positivity) (by positivity)
      (Finset.filter_subset _ _) hLowAE hdSelected
    have hdirW : AlmostEvery (1 - 10 * t) W
        (fun w => extractionDirectionGood D phi x w d t) := by
      convert hdirWbase using 1
      ring
    have hxd := extraction_shifted_fibre_bounds D B sigma M x hinvariant
      hxQuarter d hdB
    have hxBasePos : 0 < (D.fibreSize x : Real) := by
      have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
      have halpha := hsetup.1.1
      exact (show 0 < alpha ^ 2 * M / 2 by positivity).trans_le hanchor.1
    have hxdPos : 0 < ((D.fibre (D.index x + d)).card : Real) := by
      linarith
    have hlocalT : AlmostEvery (1 - 10 * t) W fun w =>
        AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d)) fun z =>
          phi z - phi w = psi d := by
      apply extraction_almostEvery_mono (1 - 10 * t) W
        (fun w => extractionDirectionGood D phi x w d t)
        (fun w => AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d))
          (fun z => phi z - phi w = psi d)) hdirW
      intro w _ hwDirection
      simpa only [psi] using extraction_directionGood_gives_mode D phi x w d t
        ht htUpper hxdPos hwDirection
    simpa only [t] using hlocalT

end LeanProofs.GowersSzemeredi

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
  simp_rw [← sub_eq_iff_eq_add', ite_and, Finset.sum_ite_eq]
  by_cases h : D.index uv.1 - D.index x ∈ B <;> simp [h, eq_comm]

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
  obtain ⟨⟨halpha, halphaOne, -⟩, -, heta, hetaOne, -⟩ := hsetup
  have h : eta * rho ≤ 1 / 32 := by
    rcases le_total rho 0 with h | h
    · nlinarith
    · linarith [mul_le_of_le_one_left h hetaOne, pow_le_one₀ (n := 2) halpha.le halphaOne]
  linarith [mul_le_mul_of_nonneg_right h (sq_nonneg alpha), sq_nonneg alpha]

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
  have hx := extraction_shifted_fibre_bounds D B sigma M x hinvariant hxQuarter
  have hw := extraction_shifted_fibre_bounds D B sigma M w hinvariant hwQuarter
  calc ((D.fibre (D.index x + d)).card : Real) * (D.fibre (D.index w + d)).card
      ≤ (2 * (D.fibre (D.index x + e)).card) * (2 * (D.fibre (D.index w + e)).card) := by
        gcongr ?_ * ?_
        · linarith [(hx d hd).2, (hx e he).1]
        · linarith [(hw d hd).2, (hw e he).1]
    _ = _ := by ring

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
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [AlmostEvery]
  -- `P d` pairs lie in direction `d`; each `P d` is at most four times the least one, `P d₀`
  let P : ZMod N → Real := fun d =>
    ((D.fibre (D.index x + d)).card : Real) * (D.fibre (D.index w + d)).card
  obtain ⟨d₀, hd₀B, hd₀min⟩ := B.exists_min_image P hB
  have hxQ := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hwQ := extraction_sigmaM_le_regular_quarter D phi B alpha rho M N
    sigma eta x w W hsetup hregular hrho hsigma hw
  have hinv := hsetup.2.2.2.2.2.1
  have hσM : 0 < sigma * M := mul_pos hsetup.2.1 (by exact_mod_cast hsetup.1.2.2.1)
  have hP₀ : 0 < P d₀ := mul_pos
    (by linarith [(extraction_shifted_fibre_bounds D B sigma M x hinv hxQ d₀ hd₀B).1])
    (by linarith [(extraction_shifted_fibre_bounds D B sigma M w hinv hwQ d₀ hd₀B).1])
  have hb : (domainRestrictedDifferenceWeight D B x w : Real) = ∑ d ∈ B, P d := by
    rw [extraction_restrictedWeight_eq_sum]
    push_cast
    rfl
  have hbB : (domainRestrictedDifferenceWeight D B x w : Real) ≤ B.card * (4 * P d₀) := by
    rw [hb, ← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun d hd =>
      extraction_fibre_product_le_four D B sigma M x w hinv hxQ hwQ d hd d₀ hd₀B
  have hbpos : 0 < (domainRestrictedDifferenceWeight D B x w : Real) := by
    rw [hb]
    exact hP₀.trans_le (single_le_sum (fun d _ => by positivity) hd₀B)
  have he := (div_le_iff₀ hbpos).mp hwError
  -- a bad direction `d` carries more than `35 t² P d ≥ 35 t² P d₀` erroneous pairs
  have hcol : ∀ d ∈ B.filter fun d => ¬ extractionDirectionGood D phi x w d t,
      35 * t ^ 2 * P d₀ ≤ (extractionBadPairs D phi x w d).card := fun d hd => by
    have h : 35 * t ^ 2 * P d < (extractionBadPairs D phi x w d).card := by
      simpa [extractionBadPairs, P] using extraction_bad_card_lt_of_not_almostEvery (35 * t ^ 2)
        ((D.fibre (D.index x + d)).product (D.fibre (D.index w + d)))
        (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) (mem_filter.mp hd).2
    exact (mul_le_mul_of_nonneg_left (hd₀min d (mem_filter.mp hd).1) (by positivity)).trans h.le
  have hbad : ((B.filter fun d => ¬ extractionDirectionGood D phi x w d t).card : Real) *
      (35 * t ^ 2 * P d₀) ≤ domainDifferenceErrorCount D phi B x w := by
    rw [extraction_errorCount_eq_sum]
    push_cast
    rw [← nsmul_eq_mul]
    exact (card_nsmul_le_sum _ _ _ hcol).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
  apply extraction_almostEvery_of_bad_card_le
  refine le_of_mul_le_mul_right (hbad.trans ?_) (mul_pos (by positivity) hP₀)
  linarith [mul_le_mul_of_nonneg_left hbB (by positivity : (0 : Real) ≤ 300 * t ^ 4),
    mul_nonneg (mul_nonneg (pow_nonneg ht.le 4) (Nat.cast_nonneg B.card)) hP₀.le]

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
  rcases C.eq_empty_or_nonempty with hC | hC
  · unfold AlmostEvery
    simp [C, hC]
  -- at most `35 t² #A #C` pairs of `A × C` are bad, and grouped by `z` the good ones number at
  -- most `#C #Am`; so `#Am ≥ (1 - 35 t²) #A`
  have hpart : E.card + Ebad.card = A.card * C.card :=
    (card_filter_add_card_filter_not _).trans (card_product A C)
  have hBad : (Ebad.card : Real) ≤ 35 * t ^ 2 * (A.card * C.card) := by
    simpa [Ebad, mul_assoc] using extraction_almostEvery_bad_card_le (35 * t ^ 2)
      (A.product C) (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) hgood
  have hGood : E.card ≤ C.card * Am.card := by
    have h := (extraction_agreement_card_eq_sum A C (fun y => phi y - phi x)
      (fun z => phi z - phi w)).trans_le (sum_le_card_nsmul _ _ _ fun z _ =>
        extractionMode_max D phi x d (phi z - phi w))
    rwa [smul_eq_mul] at h
  have hModeLower : (1 - 35 * t ^ 2) * (A.card : Real) ≤ Am.card := by
    have h₁ : (E.card : Real) + Ebad.card = A.card * C.card := by exact_mod_cast hpart
    have h₂ : (E.card : Real) ≤ C.card * Am.card := by exact_mod_cast hGood
    refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < C.card)
    linarith
  -- the pairs of `Am × (C \ Cm)` are bad
  have hsub : Am.product (C \ Cm) ⊆ Ebad := fun yz hyz => by
    obtain ⟨hy, hz⟩ := mem_product.mp hyz
    obtain ⟨hzC, hzCm⟩ := mem_sdiff.mp hz
    exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_filter.mp hy).1, hzC⟩,
      fun h => hzCm (mem_filter.mpr ⟨hzC, h.symm.trans (mem_filter.mp hy).2⟩)⟩
  have hrect : (Am.card : Real) * (C \ Cm).card ≤ Ebad.card := by
    exact_mod_cast (card_product Am (C \ Cm)).symm.trans_le (card_le_card hsub)
  have hp : 0 < 1 - 35 * t ^ 2 := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le)]
  have hnumeric : 35 * t ^ 2 ≤ 10 * t * (1 - 35 * t ^ 2) := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le),
      mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htUpper.le)]
  have htargetBad : ((C \ Cm).card : Real) ≤ 10 * t * C.card := by
    refine le_of_mul_le_mul_left ?_ (mul_pos hp hanchorFibre)
    linarith [mul_le_mul_of_nonneg_right hModeLower (Nat.cast_nonneg (C \ Cm).card),
      mul_le_mul_of_nonneg_right hnumeric (by positivity : (0 : Real) ≤ A.card * C.card)]
  apply extraction_almostEvery_of_bad_card_le
  rw [filter_not]
  exact htargetBad

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
  apply extraction_almostEvery_of_bad_card_le
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp [AlmostEvery]
    positivity
  -- count the pairs `(y, z)` with `¬ Q y z` by columns and by rows
  have hcol : ∀ z ∈ V.filter (fun z => ¬ AlmostEvery (1 - 5 * t) U fun y => Q y z),
      5 * t * (U.card : Real) ≤ (U.filter fun y => ¬ Q y z).card := fun z hz =>
    (extraction_bad_card_lt_of_not_almostEvery _ U _ (mem_filter.mp hz).2).le
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : Real) < 5 * t * U.card)
  calc ((V.filter fun z => ¬ AlmostEvery (1 - 5 * t) U fun y => Q y z).card : Real) *
        (5 * t * U.card)
      ≤ ∑ z ∈ V, ((U.filter fun y => ¬ Q y z).card : Real) := by
        rw [← nsmul_eq_mul]
        exact (card_nsmul_le_sum _ _ _ hcol).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity)
    _ = ∑ y ∈ U, ((V.filter fun z => ¬ Q y z).card : Real) := by
        exact_mod_cast (extraction_product_filter_card_second U V fun y z => ¬ Q y z).symm.trans
          (extraction_product_filter_card_first U V fun y z => ¬ Q y z)
    _ ≤ U.card • (35 * t ^ 2 * V.card) := sum_le_card_nsmul _ _ _ fun y hy =>
        extraction_almostEvery_bad_card_le _ V _ (hrow y hy)
    _ = 7 * t * V.card * (5 * t * U.card) := by rw [nsmul_eq_mul]; ring

private lemma extraction_lift_almostEvery {Y : Type*} [DecidableEq Y]
    (W U : Finset Y) (P : Y → Prop) (a b : Real)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hUW : U ⊆ W)
    (hU : AlmostEvery (1 - a) W (fun y => y ∈ U))
    (hP : AlmostEvery (1 - b) U P) :
    AlmostEvery (1 - (a + b)) W P := by
  classical
  have hcard : ((W.filter fun y => ¬ P y).card : Real) ≤
      (W.filter fun y => y ∉ U).card + (U.filter fun y => ¬ P y).card := by
    exact_mod_cast (card_le_card fun y hy => by
      simp only [mem_union, mem_filter] at hy ⊢; tauto).trans (card_union_le _ _)
  have hUcard : (U.card : Real) ≤ W.card := by exact_mod_cast card_le_card hUW
  apply extraction_almostEvery_of_bad_card_le
  linarith [extraction_almostEvery_bad_card_le a W (fun y => y ∈ U) hU,
    extraction_almostEvery_bad_card_le b U P hP, mul_le_mul_of_nonneg_left hUcard hb]

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
  have heta := hsetup.2.2.1
  have hetaPos : 0 < eta := lt_of_le_of_ne heta fun h => by
    subst h
    linarith [hsetup.2.1]
  set t : Real := eta ^ ((1 : Real) / 5) with ht_def
  have ht : 0 < t := by positivity
  by_cases htLarge : 1 ≤ 10 * t
  · refine ⟨∅, fun _ => 0, empty_subset _, ?_, by simp⟩
    rw [card_empty, Nat.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _)
  have htFour : eta ^ ((4 : Real) / 5) = t ^ 4 := by
    rw [ht_def, ← Real.rpow_mul_natCast heta]
    norm_num
  -- `Low`: the points of `W` with small proportionate error
  let Low : Finset X := W.filter fun w =>
    domainProportionateError D phi B x w ≤ 300 * t ^ 4
  have hLow : AlmostEvery (1 - 5 * t) W (· ∈ Low) := by
    have h := hregular.2.2.1
    rw [htFour] at h
    exact extraction_almostEvery_mono _ _ _ _ h fun w hw hwE => mem_filter.mpr ⟨hw, hwE⟩
  -- `B'`: the directions that are good for most points of `Low`
  have hsel := extraction_select_directions Low B
    (fun w d => extractionDirectionGood D phi x w d t) t ht fun w hw =>
      extraction_direction_good_almostEvery D phi B alpha rho M sigma eta t x w W hsetup
        hanchor hregular hrho hsigma ht (mem_filter.mp hw).1 (mem_filter.mp hw).2
  let B' : Finset (ZMod N) := B.filter fun d =>
    AlmostEvery (1 - 5 * t) Low fun w => extractionDirectionGood D phi x w d t
  have hB' : (1 - 7 * t) * B.card ≤ (B'.card : Real) := hsel
  have hxQ := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hσM : 0 < sigma * M := mul_pos hsetup.2.1 (by exact_mod_cast hsetup.1.2.2.1)
  refine ⟨B', extractionMode D phi x, filter_subset _ _,
    by linarith [mul_nonneg ht.le (Nat.cast_nonneg B.card)], fun d hd => ?_⟩
  -- for `d ∈ B'` most `w ∈ W` are good for `d`, and then most `z` realize the mode difference
  have hxd := (extraction_shifted_fibre_bounds D B sigma M x hsetup.2.2.2.2.2.1 hxQ d
    (mem_filter.mp hd).1).1
  have hW := extraction_lift_almostEvery W Low _ (5 * t) (5 * t) (by positivity)
    (by positivity) (filter_subset _ _) hLow (mem_filter.mp hd).2
  rw [show 5 * t + 5 * t = 10 * t by ring] at hW
  exact extraction_almostEvery_mono _ _ _ _ hW fun w _ hw =>
    extraction_directionGood_gives_mode D phi x w d t ht (by linarith) (by linarith) hw

end LeanProofs.GowersSzemeredi

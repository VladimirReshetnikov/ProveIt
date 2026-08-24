import GowersSzemeredi.Proofs10Counting

/-!
# The weighted error estimate from Section 10

This file proves the global weighted-error bound of Lemma 10.2.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma countWhere_cast_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (countWhere P : Real) = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma countWhere_eq_card_filter {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    countWhere P = (Finset.univ.filter P).card := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]

private abbrev AltDomainAdditive {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (q : Fin 4 → X) : Prop :=
  D.index (q 3) - D.index (q 2) = D.index (q 1) - D.index (q 0)

private abbrev AltPhiAdditive {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N) (q : Fin 4 → X) : Prop :=
  AltDomainAdditive D q ∧
    phi (q 3) - phi (q 2) = phi (q 1) - phi (q 0)

private abbrev AltPhiBad {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N) (q : Fin 4 → X) : Prop :=
  AltDomainAdditive D q ∧
    phi (q 3) - phi (q 2) ≠ phi (q 1) - phi (q 0)

private def altQuadEquiv (X : Type*) : (Fin 4 → X) ≃ (Fin 4 → X) where
  toFun q := ![q 0, q 3, q 2, q 1]
  invFun q := ![q 0, q 3, q 2, q 1]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

private lemma hasEqualHalfSums_two {G : Type*} [AddCommMonoid G]
    (f : Fin (2 * 2) → G) :
    HasEqualHalfSums f ↔ f 0 + f 1 = f 2 + f 3 := by
  have hleft :
      (Finset.univ.filter (fun i : Fin (2 * 2) => (i : Nat) < 2)) = {0, 1} := by
    decide
  have hright :
      (Finset.univ.filter (fun i : Fin (2 * 2) => 2 ≤ (i : Nat))) = {2, 3} := by
    decide
  unfold HasEqualHalfSums
  rw [hleft, hright]
  simp

private lemma altDomainAdditive_count_eq {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) :
    countWhere (AltDomainAdditive D) = domainAdditiveTupleCount D 2 := by
  classical
  unfold countWhere domainAdditiveTupleCount
  apply Finset.card_equiv (altQuadEquiv X)
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [AltDomainAdditive, hasEqualHalfSums_two, altQuadEquiv]
  constructor <;> intro h
  · simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp h
  · exact sub_eq_sub_iff_add_eq_add.mpr (by
      simpa [add_comm] using h)

private lemma altPhiAdditive_count_eq {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) :
    countWhere (AltPhiAdditive D phi) = domainPhiAdditiveTupleCount D phi 2 := by
  classical
  unfold countWhere domainPhiAdditiveTupleCount
  apply Finset.card_equiv (altQuadEquiv X)
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [AltPhiAdditive, AltDomainAdditive, hasEqualHalfSums_two, altQuadEquiv]
  constructor
  · rintro ⟨hindex, hphi⟩
    exact ⟨
      by simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp hindex,
      by simpa [add_comm] using sub_eq_sub_iff_add_eq_add.mp hphi⟩
  · rintro ⟨hindex, hphi⟩
    exact ⟨
      sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hindex),
      sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hphi)⟩

private def finFourTupleEquiv (X : Type*) : (Fin 4 → X) ≃ X × X × X × X where
  toFun q := (q 0, q 1, q 2, q 3)
  invFun q := ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  left_inv q := by
    funext i
    fin_cases i <;> rfl
  right_inv q := by
    rcases q with ⟨a, b, c, d⟩
    rfl

private lemma sum_fin_four {X R : Type*} [Fintype X] [AddCommMonoid R]
    (F : (Fin 4 → X) → R) :
    ∑ q, F q = ∑ a : X, ∑ b : X, ∑ c : X, ∑ d : X, F ![a, b, c, d] := by
  have h := Fintype.sum_equiv (finFourTupleEquiv X) F
    (fun q : X × X × X × X => F ![q.1, q.2.1, q.2.2.1, q.2.2.2])
    (fun q => congrArg F ((finFourTupleEquiv X).left_inv q).symm)
  simpa only [Fintype.sum_prod_type] using h

private lemma total_differenceWeight_eq_alt_count {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) :
    (∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real)) =
      countWhere (AltDomainAdditive D) := by
  classical
  rw [countWhere_cast_eq_sum_ite, sum_fin_four]
  unfold domainDifferenceWeight
  simp_rw [countWhere_cast_eq_sum_ite]
  simp_rw [Fintype.sum_prod_type]
  rfl

private lemma alt_additive_partition {N : Nat} {X : Type*}
    [Fintype X] (D : MultifunctionDomain N X) (phi : X → ZMod N) :
    countWhere (AltDomainAdditive D) =
      countWhere (AltPhiAdditive D phi) + countWhere (AltPhiBad D phi) := by
  classical
  let A : Finset (Fin 4 → X) := Finset.univ.filter (AltDomainAdditive D)
  let P (q : Fin 4 → X) : Prop :=
    phi (q 3) - phi (q 2) = phi (q 1) - phi (q 0)
  have hGood : A.filter P = Finset.univ.filter (AltPhiAdditive D phi) := by
    ext q
    simp only [A, P, Finset.mem_filter, Finset.mem_univ, true_and,
      AltPhiAdditive]
  have hBad : A.filter (fun q => ¬ P q) =
      Finset.univ.filter (AltPhiBad D phi) := by
    ext q
    simp only [A, P, Finset.mem_filter, Finset.mem_univ, true_and, AltPhiBad]
  have hcard := Finset.card_filter_add_card_filter_not (s := A) P
  rw [countWhere_eq_card_filter, countWhere_eq_card_filter,
    countWhere_eq_card_filter]
  rw [← hGood, ← hBad]
  exact hcard.symm

private lemma bad_additive_count_le {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (eta : Real)
    (happrox : DomainApproxHomOfOrder D phi eta 2) :
    (countWhere (AltPhiBad D phi) : Real) ≤
      eta * ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real) := by
  have hpartNat := alt_additive_partition D phi
  have hpart : (countWhere (AltDomainAdditive D) : Real) =
      countWhere (AltPhiAdditive D phi) + countWhere (AltPhiBad D phi) := by
    exact_mod_cast hpartNat
  have happrox' :
      (1 - eta) * (countWhere (AltDomainAdditive D) : Real) ≤
        countWhere (AltPhiAdditive D phi) := by
    rw [altDomainAdditive_count_eq, altPhiAdditive_count_eq]
    exact happrox
  rw [total_differenceWeight_eq_alt_count]
  nlinarith

private abbrev DifferenceQuad {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (x y : X) (zw : X × X) : Prop :=
  D.index zw.2 - D.index zw.1 = D.index y - D.index x

private abbrev RestrictedError {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (x y : X) (uv : X × X) : Prop :=
  D.index uv.1 - D.index x = D.index uv.2 - D.index y ∧
    D.index uv.1 - D.index x ∈ B ∧
    (phi uv.1 - phi x != phi uv.2 - phi y) = true

private abbrev RestrictedPair {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N))
    (x y : X) (uv : X × X) : Prop :=
  D.index uv.1 - D.index x = D.index uv.2 - D.index y ∧
    D.index uv.1 - D.index x ∈ B

private lemma sum_mul_sum_mul {A C : Type*} [Fintype A] [Fintype C]
    (f : A → Real) (g : C → Real) (r : Real) :
    (∑ a, f a) * (∑ c, g c) * r =
      ∑ a, ∑ c, f a * g c * r := by
  rw [mul_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]

private lemma weightedTerm_eq_sextuple_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    domainProportionateError D phi B x y * domainDifferenceWeight D x y =
      ∑ zw : X × X, ∑ uv : X × X,
        if DifferenceQuad D x y zw ∧ RestrictedError D phi B x y uv
        then ((domainRestrictedDifferenceWeight D B x y : Real)⁻¹) else 0 := by
  classical
  unfold domainProportionateError domainDifferenceErrorCount domainDifferenceWeight
  change ((countWhere (RestrictedError D phi B x y) : Real) /
      (domainRestrictedDifferenceWeight D B x y : Real)) *
      (countWhere (DifferenceQuad D x y) : Real) = _
  rw [countWhere_cast_eq_sum_ite, countWhere_cast_eq_sum_ite]
  rw [div_eq_mul_inv]
  calc
    ((∑ uv : X × X, if RestrictedError D phi B x y uv then 1 else 0) *
          (domainRestrictedDifferenceWeight D B x y : Real)⁻¹) *
        (∑ zw : X × X, if DifferenceQuad D x y zw then 1 else 0) =
        (∑ zw : X × X, if DifferenceQuad D x y zw then 1 else 0) *
          (∑ uv : X × X, if RestrictedError D phi B x y uv then 1 else 0) *
            (domainRestrictedDifferenceWeight D B x y : Real)⁻¹ := by ring
    _ = ∑ zw : X × X, ∑ uv : X × X,
          (if DifferenceQuad D x y zw then 1 else 0) *
            (if RestrictedError D phi B x y uv then 1 else 0) *
              (domainRestrictedDifferenceWeight D B x y : Real)⁻¹ := by
      exact sum_mul_sum_mul _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro zw _
      apply Finset.sum_congr rfl
      intro uv _
      by_cases hq : DifferenceQuad D x y zw
      · by_cases he : RestrictedError D phi B x y uv
        · rw [if_pos (And.intro hq he), if_pos hq, if_pos he]
          norm_num
        · rw [if_neg (fun h : DifferenceQuad D x y zw ∧
            RestrictedError D phi B x y uv => he h.2), if_pos hq, if_neg he]
          norm_num
      · by_cases he : RestrictedError D phi B x y uv
        · rw [if_neg (fun h : DifferenceQuad D x y zw ∧
            RestrictedError D phi B x y uv => hq h.1), if_neg hq, if_pos he]
          norm_num
        · rw [if_neg (fun h : DifferenceQuad D x y zw ∧
            RestrictedError D phi B x y uv => hq h.1), if_neg hq, if_neg he]
          norm_num

private lemma fibre_card_cast_eq_sum_ite {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (s : ZMod N) :
    ((D.fibre s).card : Real) =
      ∑ x : X, if D.index x = s then 1 else 0 := by
  classical
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma restrictedPair_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N)) (x y u v : X) :
    (if RestrictedPair D B x y (u, v) then (1 : Real) else 0) =
      ∑ d ∈ B,
        if D.index u = D.index x + d ∧ D.index v = D.index y + d
        then 1 else 0 := by
  classical
  by_cases hrel : RestrictedPair D B x y (u, v)
  · rw [if_pos hrel]
    let d0 : ZMod N := D.index u - D.index x
    have hd0 : d0 ∈ B := hrel.2
    rw [Finset.sum_eq_single d0]
    · have hu : D.index u = D.index x + d0 := by
        dsimp only [d0]
        abel
      have hv : D.index v = D.index y + d0 := by
        dsimp only [d0]
        linear_combination hrel.1.symm
      simp [hu, hv]
    · intro d hd hdne
      rw [if_neg]
      intro huv
      apply hdne
      dsimp only [d0]
      linear_combination huv.1.symm
    · exact fun hd0not => (hd0not hd0).elim
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
    · have hu : D.index u - D.index x = d := by
        rw [huv.1]
        abel
      rw [hu]
      exact hd

private lemma restrictedWeight_eq_sum_fibre {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x y : X) :
    (domainRestrictedDifferenceWeight D B x y : Real) =
      ∑ d ∈ B, ((D.fibre (D.index x + d)).card : Real) *
        (D.fibre (D.index y + d)).card := by
  classical
  unfold domainRestrictedDifferenceWeight
  change (countWhere (RestrictedPair D B x y) : Real) = _
  rw [countWhere_cast_eq_sum_ite]
  rw [Fintype.sum_prod_type]
  simp_rw [restrictedPair_ite_eq_sum]
  calc
    (∑ u : X, ∑ v : X, ∑ d ∈ B,
        if D.index u = D.index x + d ∧ D.index v = D.index y + d
        then (1 : Real) else 0) =
        ∑ u : X, ∑ d ∈ B, ∑ v : X,
          if D.index u = D.index x + d ∧ D.index v = D.index y + d
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
    _ = ∑ d ∈ B, ∑ u : X, ∑ v : X,
          if D.index u = D.index x + d ∧ D.index v = D.index y + d
          then 1 else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [fibre_card_cast_eq_sum_ite, fibre_card_cast_eq_sum_ite]
      have hprod := sum_mul_sum_mul
        (fun u : X => if D.index u = D.index x + d then (1 : Real) else 0)
        (fun v : X => if D.index v = D.index y + d then (1 : Real) else 0) 1
      calc
        (∑ u : X, ∑ v : X,
            if D.index u = D.index x + d ∧ D.index v = D.index y + d
            then (1 : Real) else 0) =
            ∑ u : X, ∑ v : X,
              (if D.index u = D.index x + d then 1 else 0) *
                (if D.index v = D.index y + d then 1 else 0) * 1 := by
          apply Finset.sum_congr rfl
          intro u _
          apply Finset.sum_congr rfl
          intro v _
          by_cases hu : D.index u = D.index x + d <;>
            by_cases hv : D.index v = D.index y + d <;>
            simp [hu, hv]
        _ = (∑ u : X, if D.index u = D.index x + d then 1 else 0) *
              (∑ v : X, if D.index v = D.index y + d then 1 else 0) * 1 :=
          hprod.symm
        _ = _ := by ring

private lemma restrictedWeight_le_four_of_large {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (B : Finset (ZMod N))
    (alpha sigma eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hinvariant : DomainInvariant D B (sigma * M))
    (hsigma : sigma ≤ eta * alpha ^ 2)
    (x y u v : X)
    (hxlarge : 5 * eta * alpha ^ 2 * M ≤ (D.fibre (D.index x)).card)
    (hylarge : 5 * eta * alpha ^ 2 * M ≤ (D.fibre (D.index y)).card)
    (hrel : RestrictedPair D B x y (u, v)) :
    (domainRestrictedDifferenceWeight D B u v : Real) ≤
      4 * domainRestrictedDifferenceWeight D B x y := by
  let L : Real := eta * alpha ^ 2 * M
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hsigmaM : sigma * (M : Real) ≤ L := by
    dsimp only [L]
    exact mul_le_mul_of_nonneg_right hsigma (by positivity)
  have hxlargeL : 5 * L ≤ (D.fibre (D.index x)).card := by
    dsimp only [L]
    simpa only [mul_assoc] using hxlarge
  have hylargeL : 5 * L ≤ (D.fibre (D.index y)).card := by
    dsimp only [L]
    simpa only [mul_assoc] using hylarge
  let d0 : ZMod N := D.index u - D.index x
  have hd0 : d0 ∈ B := hrel.2
  have hvIndex : D.index v - D.index y = d0 := hrel.1.symm
  rw [restrictedWeight_eq_sum_fibre, restrictedWeight_eq_sum_fibre]
  calc
    (∑ d ∈ B, ((D.fibre (D.index u + d)).card : Real) *
        (D.fibre (D.index v + d)).card) ≤
        ∑ d ∈ B, 4 * (((D.fibre (D.index x + d)).card : Real) *
          (D.fibre (D.index y + d)).card) := by
      apply Finset.sum_le_sum
      intro d hd
      let Ax : Real := (D.fibre (D.index x + d)).card
      let Ay : Real := (D.fibre (D.index y + d)).card
      let Au : Real := (D.fibre (D.index u + d)).card
      let Av : Real := (D.fibre (D.index v + d)).card
      have hxShift :
          |Ax - (D.fibre (D.index x)).card| ≤ L := by
        exact (hinvariant (D.index x) d hd).trans hsigmaM
      have hyShift :
          |Ay - (D.fibre (D.index y)).card| ≤ L := by
        exact (hinvariant (D.index y) d hd).trans hsigmaM
      have huxIndex : D.index u + d = (D.index x + d) + d0 := by
        dsimp only [d0]
        abel
      have hvyIndex : D.index v + d = (D.index y + d) + d0 := by
        rw [show D.index v = D.index y + d0 by
          dsimp only [d0] at hvIndex ⊢
          linear_combination hvIndex]
        abel
      have huxShift : |Au - Ax| ≤ L := by
        dsimp only [Au, Ax]
        rw [huxIndex]
        exact (hinvariant (D.index x + d) d0 hd0).trans hsigmaM
      have hvyShift : |Av - Ay| ≤ L := by
        dsimp only [Av, Ay]
        rw [hvyIndex]
        exact (hinvariant (D.index y + d) d0 hd0).trans hsigmaM
      have hLleAx : L ≤ Ax := by
        have hxlow := (abs_le.mp hxShift).1
        nlinarith only [hxlow, hxlargeL, hL]
      have hLleAy : L ≤ Ay := by
        have hylow := (abs_le.mp hyShift).1
        nlinarith only [hylow, hylargeL, hL]
      have hAu : Au ≤ 2 * Ax := by
        have hupper := (abs_le.mp huxShift).2
        nlinarith only [hupper, hLleAx]
      have hAv : Av ≤ 2 * Ay := by
        have hupper := (abs_le.mp hvyShift).2
        nlinarith only [hupper, hLleAy]
      have hAvNonneg : 0 ≤ Av := by
        dsimp only [Av]
        exact_mod_cast Nat.zero_le (D.fibre (D.index v + d)).card
      have hAxNonneg : 0 ≤ Ax := by
        dsimp only [Ax]
        exact_mod_cast Nat.zero_le (D.fibre (D.index x + d)).card
      have hprod : Au * Av ≤ (2 * Ax) * (2 * Ay) := by
        exact mul_le_mul hAu hAv hAvNonneg
          (mul_nonneg (by norm_num) hAxNonneg)
      dsimp only [Au, Av, Ax, Ay] at hprod ⊢
      nlinarith only [hprod]
    _ = 4 * ∑ d ∈ B, ((D.fibre (D.index x + d)).card : Real) *
        (D.fibre (D.index y + d)).card := by
      rw [Finset.mul_sum]

private lemma restrictedError_inv_sum_le_one {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    (∑ uv : X × X, if RestrictedError D phi B x y uv
      then (domainRestrictedDifferenceWeight D B x y : Real)⁻¹ else 0) ≤ 1 := by
  classical
  let e : Nat := countWhere (RestrictedError D phi B x y)
  let b : Nat := domainRestrictedDifferenceWeight D B x y
  have heb : e ≤ b := by
    dsimp only [e, b]
    unfold domainRestrictedDifferenceWeight
    apply countWhere_mono
    intro uv huv
    exact ⟨huv.1, huv.2.1⟩
  have hebReal : (e : Real) ≤ b := by exact_mod_cast heb
  have hecast : (e : Real) =
      ∑ uv : X × X, if RestrictedError D phi B x y uv then 1 else 0 := by
    dsimp only [e]
    exact countWhere_cast_eq_sum_ite _
  calc
    (∑ uv : X × X, if RestrictedError D phi B x y uv
        then (domainRestrictedDifferenceWeight D B x y : Real)⁻¹ else 0) =
        (e : Real) * (b : Real)⁻¹ := by
      rw [hecast]
      dsimp only [b]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro uv _
      by_cases huv : RestrictedError D phi B x y uv <;> simp [huv]
    _ ≤ (b : Real) * (b : Real)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hebReal (inv_nonneg.mpr (by positivity))
    _ ≤ 1 := by
      by_cases hb : b = 0
      · simp [hb]
      · rw [mul_inv_cancel₀]
        exact_mod_cast hb

private abbrev LargeFibre {N : Nat} {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha eta : Real) (M : Nat) (x : X) : Prop :=
  5 * eta * alpha ^ 2 * M ≤ (D.fibre (D.index x)).card

private lemma restrictedPair_reverse {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N))
    (hsymmetric : IsSymmetricModSet B) (x y u v : X)
    (hrel : RestrictedPair D B x y (u, v)) :
    RestrictedPair D B u v (x, y) := by
  constructor
  · simpa only [neg_sub] using congrArg Neg.neg hrel.1
  · have hneg : -(D.index u - D.index x) ∈ B :=
      (hsymmetric (D.index u - D.index x)).mp hrel.2
    convert hneg using 1
    abel

private lemma restrictedWeight_pos_of_pair {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x y u v : X)
    (hrel : RestrictedPair D B x y (u, v)) :
    0 < domainRestrictedDifferenceWeight D B x y := by
  classical
  unfold domainRestrictedDifferenceWeight countWhere
  rw [Finset.filter_congr_decidable]
  apply Finset.card_pos.mpr
  exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩⟩

private lemma large_reverse_inv_sum_le_four {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (B : Finset (ZMod N))
    (alpha sigma eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hsymmetric : IsSymmetricModSet B)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hsigma : sigma ≤ eta * alpha ^ 2) (u v : X) :
    (∑ xy : X × X,
      if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
          RestrictedPair D B xy.1 xy.2 (u, v)
      then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0) ≤ 4 := by
  classical
  let Eligible (xy : X × X) : Prop :=
    LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
      RestrictedPair D B xy.1 xy.2 (u, v)
  let c : Nat := countWhere Eligible
  let buv : Nat := domainRestrictedDifferenceWeight D B u v
  have hc : c ≤ buv := by
    dsimp only [c, buv]
    unfold domainRestrictedDifferenceWeight
    apply countWhere_mono
    intro xy hxy
    exact restrictedPair_reverse D B hsymmetric xy.1 xy.2 u v hxy.2.2
  have hcReal : (c : Real) ≤ buv := by exact_mod_cast hc
  have hpoint (xy : X × X) (hxy : Eligible xy) :
      (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ ≤
        4 * (buv : Real)⁻¹ := by
    have hcomp := restrictedWeight_le_four_of_large D B alpha sigma eta M
      heta hinvariant hsigma xy.1 xy.2 u v hxy.1 hxy.2.1 hxy.2.2
    have hxyPosNat := restrictedWeight_pos_of_pair D B xy.1 xy.2 u v hxy.2.2
    have hrev := restrictedPair_reverse D B hsymmetric xy.1 xy.2 u v hxy.2.2
    have huvPosNat := restrictedWeight_pos_of_pair D B u v xy.1 xy.2 hrev
    have hxyPos : (0 : Real) < domainRestrictedDifferenceWeight D B xy.1 xy.2 := by
      exact_mod_cast hxyPosNat
    have huvPos : (0 : Real) < buv := by
      dsimp only [buv]
      exact_mod_cast huvPosNat
    have hcross : (1 : Real) * (buv : Real) ≤
        4 * domainRestrictedDifferenceWeight D B xy.1 xy.2 := by
      dsimp only [buv]
      simpa only [one_mul] using hcomp
    simp only [inv_eq_one_div]
    simpa only [div_eq_mul_inv, one_mul] using
      (div_le_div_iff₀ hxyPos huvPos).2 hcross
  have hsumPoint :
      (∑ xy : X × X, if Eligible xy
        then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0) ≤
      ∑ xy : X × X, if Eligible xy then 4 * (buv : Real)⁻¹ else 0 := by
    apply Finset.sum_le_sum
    intro xy _
    by_cases hxy : Eligible xy
    · simp only [if_pos hxy]
      exact hpoint xy hxy
    · simp [hxy]
  have hccast : (c : Real) =
      ∑ xy : X × X, if Eligible xy then 1 else 0 := by
    dsimp only [c]
    exact countWhere_cast_eq_sum_ite _
  calc
    (∑ xy : X × X,
        if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
            RestrictedPair D B xy.1 xy.2 (u, v)
        then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0) =
        ∑ xy : X × X, if Eligible xy
          then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0 := by
      rfl
    _ ≤ ∑ xy : X × X, if Eligible xy then 4 * (buv : Real)⁻¹ else 0 := hsumPoint
    _ = (c : Real) * (4 * (buv : Real)⁻¹) := by
      rw [hccast, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro xy _
      by_cases hxy : Eligible xy <;> simp [hxy]
    _ ≤ (buv : Real) * (4 * (buv : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hcReal (by positivity)
    _ ≤ 4 := by
      by_cases hbuv : buv = 0
      · simp [hbuv]
      · field_simp
        norm_num

private lemma bad_left_or_bad_right {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (x y : X) (zw uv : X × X)
    (hq : DifferenceQuad D x y zw)
    (he : RestrictedError D phi B x y uv) :
    AltPhiBad D phi ![x, y, zw.1, zw.2] ∨
      AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2] := by
  have hvuIndex : D.index uv.2 - D.index uv.1 =
      D.index y - D.index x := by
    apply sub_eq_sub_iff_add_eq_add.mpr
    have hadd := sub_eq_sub_iff_add_eq_add.mp he.1
    simpa only [add_comm] using hadd.symm
  have hrightIndex : D.index zw.2 - D.index zw.1 =
      D.index uv.2 - D.index uv.1 := hq.trans hvuIndex.symm
  have herr : phi uv.1 - phi x ≠ phi uv.2 - phi y := by
    simpa using he.2.2
  by_cases hleft : phi zw.2 - phi zw.1 ≠ phi y - phi x
  · exact Or.inl ⟨hq, hleft⟩
  · right
    refine ⟨hrightIndex, ?_⟩
    intro hright
    apply herr
    apply sub_eq_sub_iff_add_eq_add.mpr
    have hvuPhi : phi uv.2 - phi uv.1 = phi y - phi x :=
      hright.symm.trans (not_ne_iff.mp hleft)
    have hadd := sub_eq_sub_iff_add_eq_add.mp hvuPhi
    simpa only [add_comm] using hadd.symm

private lemma bad_count_eq_xy_pair_sum {N : Nat} {X : Type*}
    [Fintype X] (D : MultifunctionDomain N X) (phi : X → ZMod N) :
    (countWhere (AltPhiBad D phi) : Real) =
      ∑ x : X, ∑ y : X, ∑ zw : X × X,
        if AltPhiBad D phi ![x, y, zw.1, zw.2] then 1 else 0 := by
  classical
  rw [countWhere_cast_eq_sum_ite, sum_fin_four]
  simp_rw [Fintype.sum_prod_type]

private lemma bad_count_eq_pair_pair_sum {N : Nat} {X : Type*}
    [Fintype X] (D : MultifunctionDomain N X) (phi : X → ZMod N) :
    (countWhere (AltPhiBad D phi) : Real) =
      ∑ uv : X × X, ∑ zw : X × X,
        if AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2] then 1 else 0 := by
  classical
  rw [countWhere_cast_eq_sum_ite, sum_fin_four]
  simp_rw [Fintype.sum_prod_type]

private lemma sum_triple_rotate {A C E : Type*}
    [Fintype A] [Fintype C] [Fintype E] (f : A → C → E → Real) :
    (∑ a, ∑ c, ∑ e, f a c e) = ∑ e, ∑ c, ∑ a, f a c e := by
  calc
    (∑ a, ∑ c, ∑ e, f a c e) = ∑ a, ∑ e, ∑ c, f a c e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ e, ∑ a, ∑ c, f a c e := by rw [Finset.sum_comm]
    _ = ∑ e, ∑ c, ∑ a, f a c e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm]

private lemma ite_ite_nonneg (P Q : Prop) [Decidable P] [Decidable Q]
    (r : Real) (hr : 0 ≤ r) :
    0 ≤ if P then (if Q then r else 0) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hr]

private lemma left_contribution_le_bad {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha eta : Real) (M : Nat) :
    (∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
      if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
          AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2]
      then if RestrictedError D phi B xy.1 xy.2 uv
        then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0
      else 0) ≤ countWhere (AltPhiBad D phi) := by
  classical
  rw [bad_count_eq_pair_pair_sum]
  apply Finset.sum_le_sum
  intro xy _
  apply Finset.sum_le_sum
  intro zw _
  by_cases houter : LargeFibre D alpha eta M xy.1 ∧
      LargeFibre D alpha eta M xy.2 ∧
      AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2]
  · simp only [if_pos houter, if_pos houter.2.2]
    exact restrictedError_inv_sum_le_one D phi B xy.1 xy.2
  · simp only [if_neg houter, Finset.sum_const_zero]
    by_cases hbad : AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2]
    · rw [if_pos hbad]
      norm_num
    · rw [if_neg hbad]

private lemma right_contribution_le_four_bad {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha sigma eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hsymmetric : IsSymmetricModSet B)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hsigma : sigma ≤ eta * alpha ^ 2) :
    (∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
      if AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2]
      then if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
          RestrictedPair D B xy.1 xy.2 uv
        then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0
      else 0) ≤ 4 * countWhere (AltPhiBad D phi) := by
  classical
  rw [sum_triple_rotate]
  rw [bad_count_eq_pair_pair_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro uv _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro zw _
  by_cases hbad : AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2]
  · simp only [if_pos hbad]
    norm_num
    exact large_reverse_inv_sum_le_four D B alpha sigma eta M heta hsymmetric
      hinvariant hsigma uv.1 uv.2
  · simp only [if_neg hbad, Finset.sum_const_zero]
    norm_num

private lemma large_weighted_sum_le_five_bad {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha sigma eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hsymmetric : IsSymmetricModSet B)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hsigma : sigma ≤ eta * alpha ^ 2) :
    (∑ xy : X × X,
      if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2
      then domainProportionateError D phi B xy.1 xy.2 *
        domainDifferenceWeight D xy.1 xy.2
      else 0) ≤ 5 * countWhere (AltPhiBad D phi) := by
  classical
  calc
    (∑ xy : X × X,
        if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2
        then domainProportionateError D phi B xy.1 xy.2 *
          domainDifferenceWeight D xy.1 xy.2
        else 0) =
        ∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
          if (LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2) ∧
              (DifferenceQuad D xy.1 xy.2 zw ∧
                RestrictedError D phi B xy.1 xy.2 uv)
          then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹
          else 0 := by
      apply Finset.sum_congr rfl
      intro xy _
      by_cases hlarge : LargeFibre D alpha eta M xy.1 ∧
          LargeFibre D alpha eta M xy.2
      · rw [if_pos hlarge, weightedTerm_eq_sextuple_sum]
        apply Finset.sum_congr rfl
        intro zw _
        apply Finset.sum_congr rfl
        intro uv _
        by_cases hq : DifferenceQuad D xy.1 xy.2 zw <;>
          by_cases he : RestrictedError D phi B xy.1 xy.2 uv <;>
          simp [hlarge, hq, he]
      · simp [hlarge]
    _ ≤ ∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
          ((if LargeFibre D alpha eta M xy.1 ∧
                LargeFibre D alpha eta M xy.2 ∧
                AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2]
            then if RestrictedError D phi B xy.1 xy.2 uv
              then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹
              else 0
            else 0) +
          (if AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2]
            then if LargeFibre D alpha eta M xy.1 ∧
                LargeFibre D alpha eta M xy.2 ∧
                RestrictedPair D B xy.1 xy.2 uv
              then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹
              else 0
            else 0)) := by
      apply Finset.sum_le_sum
      intro xy _
      apply Finset.sum_le_sum
      intro zw _
      apply Finset.sum_le_sum
      intro uv _
      by_cases hs :
          (LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2) ∧
            (DifferenceQuad D xy.1 xy.2 zw ∧
              RestrictedError D phi B xy.1 xy.2 uv)
      · rw [if_pos hs]
        rcases bad_left_or_bad_right D phi B xy.1 xy.2 zw uv hs.2.1 hs.2.2 with
          hleft | hright
        · have houter : LargeFibre D alpha eta M xy.1 ∧
              LargeFibre D alpha eta M xy.2 ∧
              AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2] :=
            ⟨hs.1.1, hs.1.2, hleft⟩
          rw [if_pos houter, if_pos hs.2.2]
          apply le_add_of_nonneg_right
          exact ite_ite_nonneg _ _ _ (inv_nonneg.mpr (by positivity))
        · have hpair : RestrictedPair D B xy.1 xy.2 uv :=
            ⟨hs.2.2.1, hs.2.2.2.1⟩
          have hinner : LargeFibre D alpha eta M xy.1 ∧
              LargeFibre D alpha eta M xy.2 ∧
              RestrictedPair D B xy.1 xy.2 uv :=
            ⟨hs.1.1, hs.1.2, hpair⟩
          rw [if_pos hright, if_pos hinner]
          apply le_add_of_nonneg_left
          exact ite_ite_nonneg _ _ _ (inv_nonneg.mpr (by positivity))
      · rw [if_neg hs]
        apply add_nonneg
        · exact ite_ite_nonneg _ _ _ (inv_nonneg.mpr (by positivity))
        · exact ite_ite_nonneg _ _ _ (inv_nonneg.mpr (by positivity))
    _ = (∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
          if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
              AltPhiBad D phi ![xy.1, xy.2, zw.1, zw.2]
          then if RestrictedError D phi B xy.1 xy.2 uv
            then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0
          else 0) +
        (∑ xy : X × X, ∑ zw : X × X, ∑ uv : X × X,
          if AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2]
          then if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2 ∧
              RestrictedPair D B xy.1 xy.2 uv
            then (domainRestrictedDifferenceWeight D B xy.1 xy.2 : Real)⁻¹ else 0
          else 0) := by
      simp_rw [Finset.sum_add_distrib]
    _ ≤ (countWhere (AltPhiBad D phi) : Real) +
        4 * countWhere (AltPhiBad D phi) :=
      add_le_add (left_contribution_le_bad D phi B alpha eta M)
        (right_contribution_le_four_bad D phi B alpha sigma eta M heta
          hsymmetric hinvariant hsigma)
    _ = 5 * countWhere (AltPhiBad D phi) := by
      nlinarith only

private lemma proportionateError_nonneg {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    0 ≤ domainProportionateError D phi B x y := by
  unfold domainProportionateError
  positivity

private lemma proportionateError_le_one {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    domainProportionateError D phi B x y ≤ 1 := by
  let e : Nat := domainDifferenceErrorCount D phi B x y
  let b : Nat := domainRestrictedDifferenceWeight D B x y
  have heb : e ≤ b := by
    dsimp only [e, b]
    unfold domainDifferenceErrorCount domainRestrictedDifferenceWeight
    apply countWhere_mono
    intro uv huv
    exact ⟨huv.1, huv.2.1⟩
  unfold domainProportionateError
  change (e : Real) / (b : Real) ≤ 1
  by_cases hb : b = 0
  · have he : e = 0 := Nat.eq_zero_of_le_zero (by simpa [hb] using heb)
    simp [hb, he]
  · rw [div_le_one (by exact_mod_cast Nat.zero_lt_of_ne_zero hb)]
    exact_mod_cast heb

private lemma sum_comp_index_eq_sum_mul_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (f : ZMod N → Real) :
    (∑ x : X, f (D.index x)) =
      ∑ s : ZMod N, f s * (D.fibre s).card := by
  classical
  simp_rw [fibre_card_cast_eq_sum_ite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (D.index x)]
  · simp
  · intro s _ hs
    rw [if_neg (Ne.symm hs)]
    simp
  · simp

private lemma small_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha eta : Real) (M : Nat)
    (heta : 0 ≤ eta) :
    (countWhere (fun x : X => ¬ LargeFibre D alpha eta M x) : Real) ≤
      5 * eta * alpha ^ 2 * M * N := by
  classical
  let T : Real := 5 * eta * alpha ^ 2 * M
  let f : ZMod N → Real := fun s =>
    if T ≤ (D.fibre s).card then 0 else 1
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hcast : (countWhere (fun x : X => ¬ LargeFibre D alpha eta M x) : Real) =
      ∑ x : X, f (D.index x) := by
    rw [countWhere_cast_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : LargeFibre D alpha eta M x
    · simp [f, T, LargeFibre, hx]
    · simp [f, T, LargeFibre, hx]
  rw [hcast, sum_comp_index_eq_sum_mul_fibre]
  calc
    (∑ s : ZMod N, f s * (D.fibre s).card) ≤ ∑ _s : ZMod N, T := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : T ≤ ((D.fibre s).card : Real)
      · simp [f, hs, hT]
      · have hle : ((D.fibre s).card : Real) ≤ T := le_of_not_ge hs
        simpa [f, hs] using hle
    _ = T * N := by simp [ZMod.card, mul_comm]
    _ = 5 * eta * alpha ^ 2 * M * N := by rfl

private lemma differenceWeight_symm {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x y : X) :
    domainDifferenceWeight D x y = domainDifferenceWeight D y x := by
  classical
  unfold domainDifferenceWeight countWhere
  apply Finset.card_equiv (Equiv.prodComm X X)
  intro zw
  rcases zw with ⟨z, w⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply]
  constructor
  · intro h
    change D.index w - D.index z = D.index y - D.index x at h
    change D.index z - D.index w = D.index x - D.index y
    simpa only [neg_sub] using congrArg Neg.neg h
  · intro h
    change D.index z - D.index w = D.index x - D.index y at h
    simpa only [neg_sub] using congrArg Neg.neg h

private lemma small_first_weight_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hbounds : Section10DomainBounds D alpha M) :
    (∑ x : X, if ¬ LargeFibre D alpha eta M x
      then ∑ y : X, (domainDifferenceWeight D x y : Real) else 0) ≤
      5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 := by
  classical
  have hcount := small_fibre_card_bound D alpha eta M heta
  have htotal (x : X) :
      (∑ y : X, (domainDifferenceWeight D x y : Real)) ≤
        alpha ^ 2 * M ^ 3 * N ^ 2 := by
    simpa only [domainTotalWeight, Nat.cast_sum] using
      (lemma_10_1_holds N X D alpha M hbounds).2.1 x
  calc
    (∑ x : X, if ¬ LargeFibre D alpha eta M x
        then ∑ y : X, (domainDifferenceWeight D x y : Real) else 0) ≤
        ∑ x : X, if ¬ LargeFibre D alpha eta M x
          then alpha ^ 2 * M ^ 3 * N ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : ¬ LargeFibre D alpha eta M x
      · simp only [if_pos hx]
        exact htotal x
      · simp [hx]
    _ = (countWhere (fun x : X => ¬ LargeFibre D alpha eta M x) : Real) *
        (alpha ^ 2 * M ^ 3 * N ^ 2) := by
      rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ¬ LargeFibre D alpha eta M x <;> simp [hx]
    _ ≤ (5 * eta * alpha ^ 2 * M * N) *
        (alpha ^ 2 * M ^ 3 * N ^ 2) := by
      exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 := by ring

private lemma small_second_weight_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha eta : Real) (M : Nat)
    (heta : 0 ≤ eta) (hbounds : Section10DomainBounds D alpha M) :
    (∑ y : X, if ¬ LargeFibre D alpha eta M y
      then ∑ x : X, (domainDifferenceWeight D x y : Real) else 0) ≤
      5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 := by
  calc
    (∑ y : X, if ¬ LargeFibre D alpha eta M y
        then ∑ x : X, (domainDifferenceWeight D x y : Real) else 0) =
        ∑ y : X, if ¬ LargeFibre D alpha eta M y
          then ∑ x : X, (domainDifferenceWeight D y x : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      rw [differenceWeight_symm]
    _ ≤ 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 :=
      small_first_weight_le D alpha eta M heta hbounds

/-- **Gowers, Lemma 10.2.** -/
theorem lemma_10_2_holds : lemma_10_2 := by
  classical
  intro N _ X _ _ D phi B alpha M sigma eta hsetup hsigma
  rcases hsetup with
    ⟨hbounds, _hsigmaPos, heta, _hetaOne, hsymmetric, hinvariant, happrox⟩
  let Q : Real := ∑ x : X, ∑ y : X, (domainDifferenceWeight D x y : Real)
  let Lg : Real := ∑ xy : X × X,
    if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2
    then domainProportionateError D phi B xy.1 xy.2 *
      domainDifferenceWeight D xy.1 xy.2
    else 0
  let S₁ : Real := ∑ xy : X × X,
    if ¬ LargeFibre D alpha eta M xy.1
    then (domainDifferenceWeight D xy.1 xy.2 : Real) else 0
  let S₂ : Real := ∑ xy : X × X,
    if ¬ LargeFibre D alpha eta M xy.2
    then (domainDifferenceWeight D xy.1 xy.2 : Real) else 0
  have hdecomp :
      (∑ x : X, ∑ y : X, domainProportionateError D phi B x y *
        domainDifferenceWeight D x y) ≤ Lg + S₁ + S₂ := by
    calc
      (∑ x : X, ∑ y : X, domainProportionateError D phi B x y *
          domainDifferenceWeight D x y) =
          ∑ xy : X × X, domainProportionateError D phi B xy.1 xy.2 *
            domainDifferenceWeight D xy.1 xy.2 := by
        rw [Fintype.sum_prod_type]
      _ ≤ ∑ xy : X × X, (
          ((if LargeFibre D alpha eta M xy.1 ∧ LargeFibre D alpha eta M xy.2
            then domainProportionateError D phi B xy.1 xy.2 *
              domainDifferenceWeight D xy.1 xy.2
            else 0) +
          (if ¬ LargeFibre D alpha eta M xy.1
            then (domainDifferenceWeight D xy.1 xy.2 : Real) else 0)) +
          (if ¬ LargeFibre D alpha eta M xy.2
            then (domainDifferenceWeight D xy.1 xy.2 : Real) else 0)) := by
        apply Finset.sum_le_sum
        intro xy _
        have hq : (0 : Real) ≤ domainDifferenceWeight D xy.1 xy.2 := by positivity
        have hterm : domainProportionateError D phi B xy.1 xy.2 *
            domainDifferenceWeight D xy.1 xy.2 ≤
            domainDifferenceWeight D xy.1 xy.2 :=
          mul_le_of_le_one_left hq (proportionateError_le_one D phi B xy.1 xy.2)
        by_cases hx : LargeFibre D alpha eta M xy.1 <;>
          by_cases hy : LargeFibre D alpha eta M xy.2
        · simp [hx, hy]
        · simpa [hx, hy] using hterm
        · simpa [hx, hy] using hterm
        · simp only [hx, hy, and_self, not_false_eq_true, if_false, if_true,
            zero_add]
          nlinarith only [hterm, hq]
      _ = Lg + S₁ + S₂ := by
        dsimp only [Lg, S₁, S₂]
        simp_rw [Finset.sum_add_distrib]
  have hlarge : Lg ≤ 5 * countWhere (AltPhiBad D phi) := by
    exact large_weighted_sum_le_five_bad D phi B alpha sigma eta M heta hsymmetric
      hinvariant hsigma
  have hbad : (countWhere (AltPhiBad D phi) : Real) ≤ eta * Q := by
    dsimp only [Q]
    exact bad_additive_count_le D phi eta happrox
  have hlargeQ : Lg ≤ 5 * eta * Q := by
    calc
      Lg ≤ 5 * (countWhere (AltPhiBad D phi) : Real) := hlarge
      _ ≤ 5 * (eta * Q) := mul_le_mul_of_nonneg_left hbad (by norm_num)
      _ = 5 * eta * Q := by ring
  have hS₁ : S₁ ≤ 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 := by
    dsimp only [S₁]
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : X, ∑ y : X,
          if ¬LargeFibre D alpha eta M x
          then (domainDifferenceWeight D x y : Real) else 0) =
          ∑ x : X, if ¬LargeFibre D alpha eta M x
            then ∑ y : X, (domainDifferenceWeight D x y : Real) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : ¬ LargeFibre D alpha eta M x
        · simp only [if_pos hx]
        · simp only [if_neg hx, Finset.sum_const_zero]
      _ ≤ 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 :=
        small_first_weight_le D alpha eta M heta hbounds
  have hS₂ : S₂ ≤ 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 := by
    dsimp only [S₂]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ y : X, ∑ x : X,
          if ¬LargeFibre D alpha eta M y
          then (domainDifferenceWeight D x y : Real) else 0) =
          ∑ y : X, if ¬LargeFibre D alpha eta M y
            then ∑ x : X, (domainDifferenceWeight D x y : Real) else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : ¬ LargeFibre D alpha eta M y
        · simp only [if_pos hy]
        · simp only [if_neg hy, Finset.sum_const_zero]
      _ ≤ 5 * eta * alpha ^ 4 * M ^ 4 * N ^ 3 :=
        small_second_weight_le D alpha eta M heta hbounds
  have hQlower : alpha ^ 4 * M ^ 4 * N ^ 3 ≤ Q := by
    dsimp only [Q]
    exact (lemma_10_1_holds N X D alpha M hbounds).2.2
  have hscale : 0 ≤ 5 * eta := mul_nonneg (by norm_num) heta
  have hsmallBase : 5 * eta * (alpha ^ 4 * M ^ 4 * N ^ 3) ≤
      5 * eta * Q := mul_le_mul_of_nonneg_left hQlower hscale
  have hS₁Q : S₁ ≤ 5 * eta * Q := by
    exact hS₁.trans (by simpa only [mul_assoc] using hsmallBase)
  have hS₂Q : S₂ ≤ 5 * eta * Q := by
    exact hS₂.trans (by simpa only [mul_assoc] using hsmallBase)
  change (∑ x : X, ∑ y : X, domainProportionateError D phi B x y *
      domainDifferenceWeight D x y) ≤ 15 * eta * Q
  calc
    (∑ x : X, ∑ y : X, domainProportionateError D phi B x y *
        domainDifferenceWeight D x y) ≤ Lg + S₁ + S₂ := hdecomp
    _ ≤ (5 * eta * Q) + (5 * eta * Q) + (5 * eta * Q) :=
      add_le_add (add_le_add hlargeQ hS₁Q) hS₂Q
    _ = 15 * eta * Q := by ring

end LeanProofs.GowersSzemeredi

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

private lemma countWhere_eq_card_filter {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    countWhere P = (Finset.univ.filter P).card := by
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

lemma hasEqualHalfSums_two {G : Type*} [AddCommMonoid G]
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
  rw [countWhere_cast_eq_sum_ite, sum_fin_four]
  unfold domainDifferenceWeight
  simp_rw [countWhere_cast_eq_sum_ite]
  simp_rw [Fintype.sum_prod_type]
  rfl

private lemma alt_additive_partition {N : Nat} {X : Type*}
    [Fintype X] (D : MultifunctionDomain N X) (phi : X → ZMod N) :
    countWhere (AltDomainAdditive D) =
      countWhere (AltPhiAdditive D phi) + countWhere (AltPhiBad D phi) := by
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

private lemma weightedTerm_eq_sextuple_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    domainProportionateError D phi B x y * domainDifferenceWeight D x y =
      ∑ zw : X × X, ∑ uv : X × X,
        if DifferenceQuad D x y zw ∧ RestrictedError D phi B x y uv
        then ((domainRestrictedDifferenceWeight D B x y : Real)⁻¹) else 0 := by
  unfold domainProportionateError domainDifferenceErrorCount domainDifferenceWeight
  change ((countWhere (RestrictedError D phi B x y) : Real) /
      (domainRestrictedDifferenceWeight D B x y : Real)) *
      (countWhere (DifferenceQuad D x y) : Real) = _
  rw [countWhere_cast_eq_sum_ite, countWhere_cast_eq_sum_ite, div_eq_mul_inv, Finset.sum_mul,
    mul_comm, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun zw _ => Finset.sum_congr rfl fun uv _ => ?_
  simp only [ite_mul, one_mul, zero_mul, ite_and]

lemma fibre_card_cast_eq_sum_ite {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (s : ZMod N) :
    ((D.fibre s).card : Real) =
      ∑ x : X, if D.index x = s then 1 else 0 := by
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma restrictedPair_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N)) (x y u v : X) :
    (if RestrictedPair D B x y (u, v) then (1 : Real) else 0) =
      ∑ d ∈ B,
        if D.index u = D.index x + d ∧ D.index v = D.index y + d
        then 1 else 0 := by
  simp_rw [RestrictedPair, ← sub_eq_iff_eq_add', ite_and, Finset.sum_ite_eq]
  by_cases h : D.index u - D.index x ∈ B <;> simp [h, eq_comm]

private lemma restrictedWeight_eq_sum_fibre {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x y : X) :
    (domainRestrictedDifferenceWeight D B x y : Real) =
      ∑ d ∈ B, ((D.fibre (D.index x + d)).card : Real) *
        (D.fibre (D.index y + d)).card := by
  unfold domainRestrictedDifferenceWeight
  change (countWhere (RestrictedPair D B x y) : Real) = _
  rw [countWhere_cast_eq_sum_ite, Fintype.sum_prod_type]
  simp_rw [restrictedPair_ite_eq_sum, fibre_card_cast_eq_sum_ite, Fintype.sum_mul_sum, ite_and,
    boole_mul]
  exact Eq.trans (Finset.sum_congr rfl fun u _ => Finset.sum_comm) Finset.sum_comm

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
  obtain ⟨h1, h2⟩ : D.index u - D.index x = D.index v - D.index y ∧
      D.index u - D.index x ∈ B := hrel
  have hL : sigma * (M : Real) ≤ eta * alpha ^ 2 * M :=
    mul_le_mul_of_nonneg_right hsigma (Nat.cast_nonneg _)
  have hL0 : 0 ≤ eta * alpha ^ 2 * M := by positivity
  rw [restrictedWeight_eq_sum_fibre, restrictedWeight_eq_sum_fibre, Finset.mul_sum]
  refine Finset.sum_le_sum fun d hd => ?_
  -- each of the four fibres moves by at most `eta * alpha ^ 2 * M` under the shifts
  have hx := (abs_le.mp ((hinvariant (D.index x) d hd).trans hL)).1
  have hy := (abs_le.mp ((hinvariant (D.index y) d hd).trans hL)).1
  have hu := (abs_le.mp ((hinvariant (D.index x + d) _ h2).trans hL)).2
  have hv := (abs_le.mp ((hinvariant (D.index y + d) _ h2).trans hL)).2
  rw [show D.index x + d + (D.index u - D.index x) = D.index u + d by ring] at hu
  rw [h1, show D.index y + d + (D.index v - D.index y) = D.index v + d by ring] at hv
  have hAu : ((D.fibre (D.index u + d)).card : Real) ≤ 2 * (D.fibre (D.index x + d)).card := by
    linarith
  have hAv : ((D.fibre (D.index v + d)).card : Real) ≤ 2 * (D.fibre (D.index y + d)).card := by
    linarith
  linarith [mul_le_mul hAu hAv (Nat.cast_nonneg _) (by positivity)]

private lemma restrictedError_inv_sum_le_one {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x y : X) :
    (∑ uv : X × X, if RestrictedError D phi B x y uv
      then (domainRestrictedDifferenceWeight D B x y : Real)⁻¹ else 0) ≤ 1 := by
  -- the sum is `e / b`, and the error pairs are among the `b` restricted pairs
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← countWhere_eq_card_filter,
    ← div_eq_mul_inv]
  exact div_le_one_of_le₀ (Nat.cast_le.mpr (countWhere_mono fun uv huv => ⟨huv.1, huv.2.1⟩))
    (Nat.cast_nonneg _)

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
  unfold domainRestrictedDifferenceWeight countWhere
  rw [Finset.filter_congr_decidable]
  exact Finset.card_pos.mpr (⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel⟩⟩)

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
  -- the eligible pairs inject into the restricted translates of `(u, v)`
  have hc : countWhere (fun xy : X × X => LargeFibre D alpha eta M xy.1 ∧
      LargeFibre D alpha eta M xy.2 ∧ RestrictedPair D B xy.1 xy.2 (u, v)) ≤
      domainRestrictedDifferenceWeight D B u v :=
    countWhere_mono fun xy hxy => restrictedPair_reverse D B hsymmetric xy.1 xy.2 u v hxy.2.2
  rw [← Finset.sum_filter]
  refine le_trans (Finset.sum_le_card_nsmul _ _
    (4 * (domainRestrictedDifferenceWeight D B u v : Real)⁻¹) fun xy hxy => ?_) ?_
  · obtain ⟨hx, hy, hrel⟩ := (Finset.mem_filter.mp hxy).2
    have hpos : (0 : Real) < domainRestrictedDifferenceWeight D B u v := by
      exact_mod_cast restrictedWeight_pos_of_pair D B u v xy.1 xy.2
        (restrictedPair_reverse D B hsymmetric xy.1 xy.2 u v hrel)
    have h4 := inv_anti₀ hpos (restrictedWeight_le_four_of_large D B alpha sigma eta M heta
      hinvariant hsigma xy.1 xy.2 u v hx hy hrel)
    rw [mul_inv] at h4
    linarith
  · rw [nsmul_eq_mul, ← countWhere_eq_card_filter, mul_left_comm, ← div_eq_mul_inv]
    exact mul_le_of_le_one_right (by norm_num)
      (div_le_one_of_le₀ (by exact_mod_cast hc) (Nat.cast_nonneg _))

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

private lemma bad_count_eq_pair_pair_sum {N : Nat} {X : Type*}
    [Fintype X] (D : MultifunctionDomain N X) (phi : X → ZMod N) :
    (countWhere (AltPhiBad D phi) : Real) =
      ∑ uv : X × X, ∑ zw : X × X,
        if AltPhiBad D phi ![uv.1, uv.2, zw.1, zw.2] then 1 else 0 := by
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
  rw [bad_count_eq_pair_pair_sum]
  gcongr with xy _ zw _
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
  rw [sum_triple_rotate, bad_count_eq_pair_pair_sum, Finset.mul_sum]
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
  refine le_trans ?_ ((add_le_add (left_contribution_le_bad D phi B alpha eta M)
    (right_contribution_le_four_bad D phi B alpha sigma eta M heta hsymmetric hinvariant
      hsigma)).trans_eq (by ring))
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun xy _ => ?_
  split_ifs with hlarge
  · rw [weightedTerm_eq_sextuple_sum]
    refine Finset.sum_le_sum fun zw _ => Finset.sum_le_sum fun uv _ => ?_
    -- an error term is charged to the bad quadruple on its left or on its right
    by_cases hs : DifferenceQuad D xy.1 xy.2 zw ∧ RestrictedError D phi B xy.1 xy.2 uv
    · rw [if_pos hs]
      rcases bad_left_or_bad_right D phi B xy.1 xy.2 zw uv hs.1 hs.2 with h | h
      · rw [if_pos (And.intro hlarge.1 (And.intro hlarge.2 h)), if_pos hs.2]
        exact le_add_of_nonneg_right (by positivity)
      · rw [if_pos h,
          if_pos (And.intro hlarge.1 (And.intro hlarge.2 (And.intro hs.2.1 hs.2.2.1)))]
        exact le_add_of_nonneg_left (by positivity)
    · rw [if_neg hs]
      positivity
  · positivity

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

lemma sum_comp_index_eq_sum_mul_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (f : ZMod N → Real) :
    (∑ x : X, f (D.index x)) =
      ∑ s : ZMod N, f s * (D.fibre s).card := by
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

/-- At most `T·N` points lie in fibres of size below `T ≥ 0`. -/
theorem small_fibre_count_le {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) {T : Real} (hT : 0 ≤ T) :
    (countWhere (fun x : X => ¬ T ≤ (D.fibreSize x : Real)) : Real) ≤ T * N := by
  let f : ZMod N → Real := fun s =>
    if T ≤ (D.fibre s).card then 0 else 1
  have hcast :
      (countWhere (fun x : X => ¬ T ≤ (D.fibreSize x : Real)) : Real) =
        ∑ x : X, f (D.index x) := by
    rw [countWhere_cast_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro x _
    unfold MultifunctionDomain.fibreSize
    by_cases hx : T ≤ ((D.fibre (D.index x)).card : Real)
    · simp [f, hx]
    · simp [f, hx]
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

private lemma small_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha eta : Real) (M : Nat)
    (heta : 0 ≤ eta) :
    (countWhere (fun x : X => ¬ LargeFibre D alpha eta M x) : Real) ≤
      5 * eta * alpha ^ 2 * M * N :=
  small_fibre_count_le D (T := 5 * eta * alpha ^ 2 * M) (by positivity)

private lemma differenceWeight_symm {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (x y : X) :
    domainDifferenceWeight D x y = domainDifferenceWeight D y x := by
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
  intro N _ X _ _ D phi B alpha M sigma eta hsetup hsigma
  obtain ⟨hbounds, -, heta, -, hsymmetric, hinvariant, happrox⟩ := hsetup
  have hL := large_weighted_sum_le_five_bad D phi B alpha sigma eta M heta hsymmetric
    hinvariant hsigma
  simp only [Fintype.sum_prod_type] at hL
  -- split every term into its large-fibre part and two small-fibre parts
  calc _ ≤ ∑ x : X, ∑ y : X, ((if ¬ LargeFibre D alpha eta M y
          then (domainDifferenceWeight D x y : Real) else 0) +
        ((if ¬ LargeFibre D alpha eta M x then (domainDifferenceWeight D x y : Real) else 0) +
          if LargeFibre D alpha eta M x ∧ LargeFibre D alpha eta M y
          then domainProportionateError D phi B x y * domainDifferenceWeight D x y else 0)) := by
        gcongr with x _ y _
        have hq : (0 : Real) ≤ domainDifferenceWeight D x y := by positivity
        have := mul_le_of_le_one_left hq (proportionateError_le_one D phi B x y)
        by_cases hx : LargeFibre D alpha eta M x <;> by_cases hy : LargeFibre D alpha eta M y <;>
          simp [hx, hy] <;> linarith
    _ ≤ _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
        linarith [small_first_weight_le D alpha eta M heta hbounds,
          small_second_weight_le D alpha eta M heta hbounds, bad_additive_count_le D phi eta happrox,
          mul_le_mul_of_nonneg_left (lemma_10_1_holds N X D alpha M hbounds).2.2 heta]

end LeanProofs.GowersSzemeredi

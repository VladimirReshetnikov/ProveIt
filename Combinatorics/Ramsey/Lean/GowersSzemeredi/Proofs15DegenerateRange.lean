import GowersSzemeredi.Proofs15WalshGeneral
import GowersSzemeredi.Proofs15LevelSets
import GowersSzemeredi.Proofs15DegenerateArrangements

/-!
# Degenerate arrangements for coefficients in `[−m, m]` (Notes L.16)

Lemma 15.4 bounds the arrangements carrying a **ternary** dependence other
than a modular multiple of the parity dependence. The Fejér selection of
L.16 needs the same bound for dependences with integer coefficients in
`[−m, m]`. The printed proof carries over verbatim: ternarity enters only
through Corollary 15.2, which holds for arbitrary coefficients
(`booleanWalsh_multiple_of_invariant`). Only the number of coefficient
patterns changes, from `3^(2d·2^k)` to `(2m+1)^(2d·2^k)`:

`degenerate_count_within_le`:
`#{m-degenerate d-arrangements} ≤ (2m+1)^(2d·2^k)·k·N^((2d+1)k+2d−2)`.

At `m = 1` this is the printed Lemma 15.4 (`isDegenerateWithin_one_iff`).
The file is a copy of `Proofs15DegenerateArrangements` with the coefficient
alphabet `Fin (2m+1)` in place of `Fin 3`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- A `d`-arrangement is **`m`-degenerate** when it has a dependence with
integer coefficients in `[−m, m]` other than a modular scalar multiple of the
defining parity dependence. At `m = 1` this is `IsDegenerate`. -/
def GeneralArrangement.IsDegenerateWithin {N k d : Nat} [NeZero N] (m : Nat)
    (R : GeneralArrangement N k d) : Prop :=
  ∃ eta : (Fin k → Bool) → Fin (2 * d) → Int,
    (∀ e j, -(m : Int) ≤ eta e j ∧ eta e j ≤ m) ∧
    ¬ IsModularMultiple
        (fun z : (Fin k → Bool) × Fin (2 * d) => eta z.1 z.2)
        (fun z => arrangementParityCoefficient (N := N) z.1 z.2) ∧
    ∀ A : Finset (Fin (k + 1)), arrangementMoment R eta A = 0

/-- Number of `m`-degenerate `d`-arrangements in the full ambient group. -/
def degenerateGeneralArrangementCountWithin {N k : Nat} [NeZero N] (m d : Nat) : Nat :=
  countWhere fun R : GeneralArrangement N k d =>
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m

theorem isDegenerateWithin_one_iff {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) : R.IsDegenerateWithin 1 ↔ R.IsDegenerate := by
  constructor
  · rintro ⟨eta, hb, hn, hm⟩
    refine ⟨eta, ?_, hn, hm⟩
    rintro ⟨e, j⟩
    have := hb e j
    push_cast at this
    show eta e j = -1 ∨ eta e j = 0 ∨ eta e j = 1
    omega
  · rintro ⟨eta, ht, hn, hm⟩
    refine ⟨eta, ?_, hn, hm⟩
    intro e j
    rcases ht (e, j) with h | h | h <;> simp only at h <;> rw [h] <;> norm_num

variable {m : Nat}

private abbrev RangeDegCoefficient (m k d : Nat) :=
  (Fin k → Bool) → Fin (2 * d) → Fin (2 * m + 1)

private def rangeDegCoefficientValue {k d : Nat}
    (c : RangeDegCoefficient m k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) : Int :=
  ((c e j : Nat) : Int) - m

private def rangeDegEncodeCoefficient (m : Nat) {k d : Nat}
    (eta : (Fin k → Bool) → Fin (2 * d) → Int) :
    RangeDegCoefficient m k d :=
  fun e j => ⟨(eta e j + m).toNat % (2 * m + 1), Nat.mod_lt _ (by omega)⟩

private lemma rangeDeg_encode_value {k d : Nat}
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (heta : ∀ e j, -(m : Int) ≤ eta e j ∧ eta e j ≤ m)
    (e : Fin k → Bool) (j : Fin (2 * d)) :
    rangeDegCoefficientValue (rangeDegEncodeCoefficient m eta) e j = eta e j := by
  obtain ⟨h1, h2⟩ := heta e j
  unfold rangeDegCoefficientValue rangeDegEncodeCoefficient
  simp only
  have hlt : (eta e j + m).toNat < 2 * m + 1 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

private lemma rangeDeg_coefficient_card (m k d : Nat) :
    Fintype.card (RangeDegCoefficient m k d) = (2 * m + 1) ^ (2 * d * 2 ^ k) := by
  simp only [RangeDegCoefficient, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [← pow_mul]

private def rangeDegIndexSign {N d : Nat} (j : Fin (2 * d)) : ZMod N :=
  if (j : Nat) < d then 1 else -1

private lemma rangeDeg_additive_iff {N d : Nat} (x : Fin (2 * d) → ZMod N) :
    IsAdditiveTuple x ↔ ∑ j, rangeDegIndexSign (N := N) j * x j = 0 := by
  let L := Finset.univ.filter fun j : Fin (2 * d) ↦ (j : Nat) < d
  let U := Finset.univ.filter fun j : Fin (2 * d) ↦ d ≤ (j : Nat)
  have hcomp :
      (Finset.univ.filter fun j : Fin (2 * d) ↦ ¬(j : Nat) < d) = U := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U]
    omega
  have hsum :
      (∑ j, rangeDegIndexSign (N := N) j * x j) =
        (∑ j ∈ L, x j) - ∑ j ∈ U, x j := by
    dsimp only [L, U]
    simp_rw [rangeDegIndexSign, ite_mul, one_mul, neg_one_mul]
    rw [Finset.sum_ite, hcomp, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hsum, sub_eq_zero]
  rfl

private abbrev RangeDegLinearSolutions {N : Nat} {I : Type*}
    [Fintype I] (a : I → ZMod N) :=
  {x : I → ZMod N // ∑ t, a t * x t = 0}

private lemma rangeDeg_linear_solutions_card_le {N : Nat} [NeZero N]
    [Fact N.Prime] {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ZMod N) (i : I) (hai : a i ≠ 0) :
    Fintype.card (RangeDegLinearSolutions a) ≤
      N ^ (Fintype.card I - 1) := by
  let proj : RangeDegLinearSolutions a → ({t : I // t ≠ i} → ZMod N) :=
    fun x t => x.1 t
  have hinj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    funext t
    by_cases hti : t = i
    · subst t
      have hoff : ∀ s, s ≠ i → x.1 s = y.1 s := by
        intro s hsi
        exact congrFun hxy ⟨s, hsi⟩
      have hdiff := rangeDeg_sum_mul_sub_eq_one a x.1 y.1 i hoff
      rw [x.2, y.2, sub_self] at hdiff
      have hz : x.1 i - y.1 i = 0 :=
        (mul_eq_zero.mp hdiff.symm).resolve_left hai
      exact sub_eq_zero.mp hz
    · exact congrFun hxy ⟨t, hti⟩
  calc
    Fintype.card (RangeDegLinearSolutions a) ≤
        Fintype.card ({t : I // t ≠ i} → ZMod N) :=
      Fintype.card_le_of_injective proj hinj
    _ = N ^ (Fintype.card I - 1) := by
      rw [Fintype.card_fun, ZMod.card]
      congr 1
      rw [Fintype.card_subtype_compl]
      simp

private abbrev RangeDegDoubleLinearSolutions {N : Nat} {I : Type*}
    [Fintype I] (a b : I → ZMod N) :=
  {x : I → ZMod N //
    (∑ t, a t * x t = 0) ∧ ∑ t, b t * x t = 0}

private lemma rangeDeg_double_linear_solutions_card_le {N : Nat} [NeZero N]
    [Fact N.Prime] {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ZMod N) (i j : I) (hij : i ≠ j)
    (hdet : a i * b j - a j * b i ≠ 0) :
    Fintype.card (RangeDegDoubleLinearSolutions a b) ≤
      N ^ (Fintype.card I - 2) := by
  let proj : RangeDegDoubleLinearSolutions a b →
      ({t : I // t ≠ i ∧ t ≠ j} → ZMod N) := fun x t => x.1 t
  have hinj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    funext t
    have hoff : ∀ s, s ≠ i → s ≠ j → x.1 s = y.1 s := by
      intro s hsi hsj
      exact congrFun hxy ⟨s, hsi, hsj⟩
    have haDiff := lemma154_sum_mul_sub_eq_two a x.1 y.1 i j hij hoff
    have hbDiff := lemma154_sum_mul_sub_eq_two b x.1 y.1 i j hij hoff
    rw [x.2.1, y.2.1, sub_self] at haDiff
    rw [x.2.2, y.2.2, sub_self] at hbDiff
    have ha : a i * (x.1 i - y.1 i) + a j * (x.1 j - y.1 j) = 0 :=
      haDiff.symm
    have hb : b i * (x.1 i - y.1 i) + b j * (x.1 j - y.1 j) = 0 :=
      hbDiff.symm
    have hi : x.1 i - y.1 i = 0 := by
      have hmul : (a i * b j - a j * b i) * (x.1 i - y.1 i) = 0 := by
        linear_combination b j * ha - a j * hb
      exact (mul_eq_zero.mp hmul).resolve_left hdet
    have hj : x.1 j - y.1 j = 0 := by
      have hmul : (a i * b j - a j * b i) * (x.1 j - y.1 j) = 0 := by
        linear_combination a i * hb - b i * ha
      exact (mul_eq_zero.mp hmul).resolve_left hdet
    by_cases hti : t = i
    · subst t
      exact sub_eq_zero.mp hi
    by_cases htj : t = j
    · subst t
      exact sub_eq_zero.mp hj
    exact hoff t hti htj
  calc
    Fintype.card (RangeDegDoubleLinearSolutions a b) ≤
        Fintype.card ({t : I // t ≠ i ∧ t ≠ j} → ZMod N) :=
      Fintype.card_le_of_injective proj hinj
    _ = N ^ (Fintype.card I - 2) := by
      rw [Fintype.card_fun, ZMod.card, lemma154_double_except_card i j hij]

private abbrev RangeDegAdditiveCrossSections (N d : Nat) :=
  {r : Fin (2 * d) → ZMod N // IsAdditiveTuple r}

private noncomputable instance rangeDegAdditiveCrossSectionsFintype
    (N d : Nat) [NeZero N] : Fintype (RangeDegAdditiveCrossSections N d) := by
  letI : Finite (RangeDegAdditiveCrossSections N d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma rangeDeg_additive_cross_sections_card_le {N d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) :
    Fintype.card (RangeDegAdditiveCrossSections N d) ≤ N ^ (2 * d - 1) := by
  let j0 : Fin (2 * d) := ⟨0, by omega⟩
  let a : Fin (2 * d) → ZMod N := rangeDegIndexSign
  let e : RangeDegAdditiveCrossSections N d ≃ RangeDegLinearSolutions a :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun r => rangeDeg_additive_iff r)
  rw [Fintype.card_congr e]
  have hd0 : 0 < d := by omega
  have ha : a j0 ≠ 0 := by
    simp [a, j0, rangeDegIndexSign, hd0]
  simpa [a] using rangeDeg_linear_solutions_card_le a j0 ha

private abbrev RangeDegZeroSideArrangements (N k d : Nat) :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ ∃ i, R.side i = 0}

private noncomputable instance rangeDegZeroSideArrangementsFintype
    (N k d : Nat) [NeZero N] : Fintype (RangeDegZeroSideArrangements N k d) := by
  letI : Finite (RangeDegZeroSideArrangements N k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev RangeDegZeroSideAt (N k d : Nat) (i : Fin k) :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.side i = 0}

private noncomputable instance rangeDegZeroSideAtFintype
    (N k d : Nat) [NeZero N] (i : Fin k) :
    Fintype (RangeDegZeroSideAt N k d i) := by
  letI : Finite (RangeDegZeroSideAt N k d i) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev RangeDegZeroSideCode (N k d : Nat) (i : Fin k) :=
  ({t : Fin k // t ≠ i} → ZMod N) ×
    (Fin (2 * d) → Point N k) × RangeDegAdditiveCrossSections N d

private lemma rangeDeg_zero_side_code_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (i : Fin k) :
    Fintype.card (RangeDegZeroSideCode N k d i) ≤
      N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
  have hcross := rangeDeg_additive_cross_sections_card_le (N := N) hd
  calc
    Fintype.card (RangeDegZeroSideCode N k d i) =
        N ^ (k - 1) * N ^ (2 * d * k) *
          Fintype.card (RangeDegAdditiveCrossSections N d) := by
      simp only [RangeDegZeroSideCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_fin, ZMod.card, Point]
      simp only [Fintype.card_subtype_eq]
      rw [show (N ^ k) ^ (2 * d) = N ^ (2 * d * k) by
        rw [← pow_mul]
        congr 1
        ring]
      ring
    _ ≤ N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
      exact Nat.mul_le_mul_left (N ^ (k - 1) * N ^ (2 * d * k)) hcross

private lemma rangeDeg_zero_side_at_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (i : Fin k) :
    Fintype.card (RangeDegZeroSideAt N k d i) ≤
      N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
  let proj : RangeDegZeroSideAt N k d i → RangeDegZeroSideCode N k d i :=
    fun R => ⟨fun t => R.1.side t, R.1.base, ⟨R.1.crossSection, R.2.1⟩⟩
  have hinj : Function.Injective proj := by
    intro R S hRS
    apply Subtype.ext
    have htail := congrArg Prod.fst hRS
    have hbase := congrArg (fun z => z.2.1) hRS
    have hcross := congrArg (fun z => z.2.2) hRS
    apply Prod.ext
    · funext t
      by_cases hti : t = i
      · subst t
        exact R.2.2.trans S.2.2.symm
      · exact congrFun htail ⟨t, hti⟩
    · apply Prod.ext
      · exact hbase
      · exact congrArg Subtype.val hcross
  exact (Fintype.card_le_of_injective proj hinj).trans
    (rangeDeg_zero_side_code_card_le hd i)

private lemma rangeDeg_zero_side_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (RangeDegZeroSideArrangements N k d) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  let enc : RangeDegZeroSideArrangements N k d →
      Σ i : Fin k, RangeDegZeroSideAt N k d i := fun R => by
    let i : Fin k := Classical.choose R.2.2
    exact ⟨i, R.1, R.2.1, Classical.choose_spec R.2.2⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) hRS
  calc
    Fintype.card (RangeDegZeroSideArrangements N k d) ≤
        Fintype.card (Σ i : Fin k, RangeDegZeroSideAt N k d i) :=
      Fintype.card_le_of_injective enc hinj
    _ = ∑ i : Fin k, Fintype.card (RangeDegZeroSideAt N k d i) :=
      Fintype.card_sigma
    _ ≤ ∑ _i : Fin k,
        N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
      exact Finset.sum_le_sum fun i _ => rangeDeg_zero_side_at_card_le hd i
    _ = k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← pow_add, ← pow_add]
      congr 2
      have hmul : (2 * d + 1) * k = 2 * d * k + k := by ring
      rw [hmul]
      omega

private noncomputable def rangeDegLiftFinset {k : Nat}
    (A : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  A.map Fin.castSuccEmb

private lemma rangeDeg_vertex_product_lift {N k d : Nat}
    (R : GeneralArrangement N k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) (A : Finset (Fin k)) :
    (∏ i ∈ rangeDegLiftFinset A, R.vertex e j i) =
      ∏ i ∈ A, (R.base j i + if e i then R.side i else 0) := by
  unfold rangeDegLiftFinset
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i _
  exact lemma154_vertex_castSucc R e j i

private lemma rangeDeg_arrangementMoment_lift {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d)
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (A : Finset (Fin k)) :
    arrangementMoment R eta (rangeDegLiftFinset A) =
      ∑ j : Fin (2 * d),
        booleanWalshMoment (fun e => eta e j) R.side (R.base j) A := by
  unfold arrangementMoment booleanWalshMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro e _
  rw [rangeDeg_vertex_product_lift]

private abbrev rangeDegEta {k d : Nat} (c : RangeDegCoefficient m k d) :=
  fun e j => rangeDegCoefficientValue c e j

private def rangeDegExceptional {N k d : Nat} (c : RangeDegCoefficient m k d) : Prop :=
  ¬ IsModularMultiple
      (fun z : (Fin k → Bool) × Fin (2 * d) => rangeDegEta c z.1 z.2)
      (fun z => arrangementParityCoefficient (N := N) z.1 z.2)

private abbrev RangeDegCoefficientSolutions (N k d : Nat) [NeZero N]
    (c : RangeDegCoefficient m k d) :=
  {R : GeneralArrangement N k d //
    (∀ i, R.side i ≠ 0) ∧ IsAdditiveTuple R.crossSection ∧
      ∀ A : Finset (Fin (k + 1)), arrangementMoment R (rangeDegEta c) A = 0}

private noncomputable instance rangeDegCoefficientSolutionsFintype
    (N k d : Nat) [NeZero N] (c : RangeDegCoefficient m k d) :
    Fintype (RangeDegCoefficientSolutions N k d c) := by
  letI : Finite (RangeDegCoefficientSolutions N k d c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev RangeDegCaseOneKey (N k d : Nat) (j : Fin (2 * d)) :=
  Point N k × RangeDegAdditiveCrossSections N d ×
    ({t : Fin (2 * d) // t ≠ j} → Point N k)

private lemma rangeDeg_case_one_key_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (j : Fin (2 * d)) :
    Fintype.card (RangeDegCaseOneKey N k d j) ≤
      N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k) := by
  have hcross := rangeDeg_additive_cross_sections_card_le (N := N) hd
  calc
    Fintype.card (RangeDegCaseOneKey N k d j) =
        N ^ k * Fintype.card (RangeDegAdditiveCrossSections N d) *
          N ^ ((2 * d - 1) * k) := by
      simp only [RangeDegCaseOneKey, Fintype.card_prod, Point,
        Fintype.card_fun, Fintype.card_fin, ZMod.card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      rw [show (N ^ k) ^ (2 * d - 1) = N ^ ((2 * d - 1) * k) by
        rw [← pow_mul]
        congr 1
        ring]
      ring
    _ ≤ N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcross)

private lemma rangeDeg_case_one_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : RangeDegCoefficient m k d) (j : Fin (2 * d))
    (hblock : ¬ IsModularMultiple (fun e => rangeDegEta c e j)
      (parityCharacter (N := N))) :
    Fintype.card (RangeDegCoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  letI : Fact N.Prime := ⟨hprime⟩
  let proj : RangeDegCoefficientSolutions N k d c →
      RangeDegCaseOneKey N k d j := fun R =>
    ⟨R.1.side, ⟨R.1.crossSection, R.2.2.1⟩,
      fun t => R.1.base t⟩
  have hfiber : ∀ b : RangeDegCaseOneKey N k d j,
      Fintype.card {R : RangeDegCoefficientSolutions N k d c // proj R = b} ≤
        k * N ^ (k - 1) := by
    intro b
    by_cases hex : Nonempty
        {R : RangeDegCoefficientSolutions N k d c // proj R = b}
    · let R₀ := Classical.choice hex
      have hside : ∀ i, b.1 i ≠ 0 := by
        intro i
        have hs : R₀.1.1.side = b.1 := congrArg (fun z => z.1) R₀.2
        rw [← hs]
        exact R₀.1.2.1 i
      have hnotInvariant : ¬ ∀ (A : Finset (Fin k)) (y z : Point N k),
          booleanWalshMoment (fun e => rangeDegEta c e j) b.1 y A =
            booleanWalshMoment (fun e => rangeDegEta c e j) b.1 z A := by
        intro hinvariant
        apply hblock
        exact booleanWalsh_multiple_of_invariant hprime hodd b.1
          (fun e => rangeDegEta c e j) hside hinvariant
      push Not at hnotInvariant
      obtain ⟨A, y, z, hyz⟩ := hnotInvariant
      let mu : Point N k → ZMod N := fun v =>
        booleanWalshMoment (fun e => rangeDegEta c e j) b.1 v A
      have hmuMultilinear : IsMultilinear mu :=
        lemma154_booleanWalshMoment_multilinear _ _ _
      have hmuNonconstant : ¬ ∃ a, ∀ v, mu v = a := by
        rintro ⟨a, ha⟩
        exact hyz ((ha y).trans (ha z).symm)
      let enc : {R : RangeDegCoefficientSolutions N k d c // proj R = b} →
          {v : Point N k // mu v = mu (R₀.1.1.base j)} := fun R => by
        refine ⟨R.1.1.base j, ?_⟩
        have hproj : proj R.1 = proj R₀.1 := R.2.trans R₀.2.symm
        have hsideEq : R.1.1.side = R₀.1.1.side :=
          congrArg (fun q => q.1) hproj
        have htail : (fun t : {t : Fin (2 * d) // t ≠ j} => R.1.1.base t) =
            (fun t : {t : Fin (2 * d) // t ≠ j} => R₀.1.1.base t) :=
          congrArg (fun q => q.2.2) hproj
        have hoff : ∀ t, t ≠ j →
            booleanWalshMoment (fun e => rangeDegEta c e t) R.1.1.side
                (R.1.1.base t) A =
              booleanWalshMoment (fun e => rangeDegEta c e t) R₀.1.1.side
                (R₀.1.1.base t) A := by
          intro t ht
          have htbase := congrFun htail
            (⟨t, ht⟩ : {q : Fin (2 * d) // q ≠ j})
          rw [hsideEq, htbase]
        have hdiff := rangeDeg_sum_mul_sub_eq_one
          (fun _ : Fin (2 * d) => (1 : ZMod N))
          (fun t => booleanWalshMoment (fun e => rangeDegEta c e t)
            R.1.1.side (R.1.1.base t) A)
          (fun t => booleanWalshMoment (fun e => rangeDegEta c e t)
            R₀.1.1.side (R₀.1.1.base t) A) j hoff
        have hzeroR := R.1.2.2.2 (rangeDegLiftFinset A)
        have hzeroR₀ := R₀.1.2.2.2 (rangeDegLiftFinset A)
        rw [rangeDeg_arrangementMoment_lift] at hzeroR hzeroR₀
        simp only [one_mul] at hdiff
        rw [hzeroR, hzeroR₀, sub_self] at hdiff
        have hsideRB : R.1.1.side = b.1 := congrArg (fun q => q.1) R.2
        have hsideR₀B : R₀.1.1.side = b.1 := congrArg (fun q => q.1) R₀.2
        rw [hsideRB, hsideR₀B] at hdiff
        dsimp only [mu]
        simpa only [one_mul] using sub_eq_zero.mp hdiff.symm
      have henc : Function.Injective enc := by
        intro R S hRS
        apply Subtype.ext
        apply Subtype.ext
        have hproj : proj R.1 = proj S.1 := R.2.trans S.2.symm
        have hsideEq := congrArg (fun q => q.1) hproj
        have hcrossEq := congrArg (fun q => q.2.1) hproj
        have htail := congrArg (fun q => q.2.2) hproj
        have hbasej : R.1.1.base j = S.1.1.base j :=
          congrArg Subtype.val hRS
        apply Prod.ext
        · exact hsideEq
        · apply Prod.ext
          · funext t
            by_cases ht : t = j
            · subst t
              exact hbasej
            · exact congrFun htail ⟨t, ht⟩
          · exact congrArg Subtype.val hcrossEq
      have hlevel := lemma_15_3_holds N k hprime mu (mu (R₀.1.1.base j))
        hmuMultilinear hmuNonconstant
      have hlevelReal :
          (countWhere (fun v : Point N k => mu v = mu (R₀.1.1.base j)) : Real) ≤
            k * (N : Real) ^ (k - 1) := hlevel.1.trans hlevel.2
      have hlevelNat :
          countWhere (fun v : Point N k => mu v = mu (R₀.1.1.base j)) ≤
            k * N ^ (k - 1) := by exact_mod_cast hlevelReal
      calc
        Fintype.card {R : RangeDegCoefficientSolutions N k d c // proj R = b} ≤
            Fintype.card {v : Point N k // mu v = mu (R₀.1.1.base j)} :=
          Fintype.card_le_of_injective enc henc
        _ = countWhere (fun v : Point N k => mu v = mu (R₀.1.1.base j)) :=
          lemma154_level_subtype_card mu _
        _ ≤ k * N ^ (k - 1) := hlevelNat
    · haveI : IsEmpty
          {R : RangeDegCoefficientSolutions N k d c // proj R = b} :=
        ⟨fun R => hex ⟨R⟩⟩
      simp
  have htotal := lemma154_card_le_of_fiber_le proj (k * N ^ (k - 1)) hfiber
  have hkey := rangeDeg_case_one_key_card_le (N := N) (k := k) hd j
  calc
    Fintype.card (RangeDegCoefficientSolutions N k d c) ≤
        Fintype.card (RangeDegCaseOneKey N k d j) *
          (k * N ^ (k - 1)) := htotal
    _ ≤ (N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k)) *
          (k * N ^ (k - 1)) := Nat.mul_le_mul_right _ hkey
    _ = k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      have hmul : (2 * d + 1) * k = 2 * d * k + k := by ring
      calc
        (N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k)) *
              (k * N ^ (k - 1)) =
            k * (N ^ k * N ^ (2 * d - 1) *
              N ^ ((2 * d - 1) * k) * N ^ (k - 1)) := by ring
        _ = k * N ^ (k + (2 * d - 1) + (2 * d - 1) * k + (k - 1)) := by
          rw [pow_add, pow_add, pow_add]
        _ = k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
          congr 2
          have hsubmul : (2 * d - 1) * k = 2 * d * k - k := by
            rw [Nat.sub_mul]
            simp
          have hkle : k ≤ 2 * d * k := by
            calc
              k = 1 * k := by simp
              _ ≤ (2 * d) * k := Nat.mul_le_mul_right k (by omega)
          have hcancel : 2 * d * k - k + k = 2 * d * k :=
            Nat.sub_add_cancel hkle
          rw [hmul, hsubmul]
          omega

private abbrev RangeDegCaseTwoKey {N k d : Nat} [NeZero N]
    (a s : Fin (2 * d) → ZMod N) :=
  Point N k × (Fin (2 * d) → Point N k) ×
    RangeDegDoubleLinearSolutions a s

private lemma rangeDeg_case_two_key_card_le {N k d : Nat} [NeZero N]
    [Fact N.Prime] (hd : 1 ≤ d) (a s : Fin (2 * d) → ZMod N)
    (i j : Fin (2 * d)) (hij : i ≠ j)
    (hdet : a i * s j - a j * s i ≠ 0) :
    Fintype.card (RangeDegCaseTwoKey (N := N) (k := k) a s) ≤
      N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  have hcross := rangeDeg_double_linear_solutions_card_le a s i j hij hdet
  calc
    Fintype.card (RangeDegCaseTwoKey (N := N) (k := k) a s) =
        N ^ k * N ^ (2 * d * k) *
          Fintype.card (RangeDegDoubleLinearSolutions a s) := by
      simp only [RangeDegCaseTwoKey, Fintype.card_prod, Point,
        Fintype.card_fun, Fintype.card_fin, ZMod.card]
      rw [show (N ^ k) ^ (2 * d) = N ^ (2 * d * k) by
        rw [← pow_mul]
        congr 1
        ring]
      ring
    _ ≤ N ^ k * N ^ (2 * d * k) * N ^ (2 * d - 2) := by
      exact Nat.mul_le_mul_left _ (by simpa using hcross)
    _ = N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      have hmul : (2 * d + 1) * k = 2 * d * k + k := by ring
      rw [hmul]
      omega

private lemma rangeDeg_case_two_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : RangeDegCoefficient m k d)
    (hblocks : ∀ j, IsModularMultiple (fun e ↦ rangeDegEta c e j)
      (parityCharacter (N := N)))
    (hexceptional : rangeDegExceptional (N := N) c) :
    Fintype.card (RangeDegCoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  letI : Fact N.Prime := ⟨hprime⟩
  letI : Nonempty (Fin (2 * d)) := ⟨⟨0, by omega⟩⟩
  let a : Fin (2 * d) → ZMod N := rangeDegIndexSign
  let s : Fin (2 * d) → ZMod N := fun j ↦ Classical.choose (hblocks j)
  have hs : ∀ j e, (rangeDegEta c e j : ZMod N) =
      s j * parityCharacter (N := N) e := by
    intro j e
    exact Classical.choose_spec (hblocks j) e
  have ha : ∀ j, a j ≠ 0 := by
    intro j
    by_cases hj : (j : Nat) < d <;>
      simp [a, rangeDegIndexSign, hj]
  have hnotprop : ¬ ∃ q, ∀ j, s j = q * a j := by
    rintro ⟨q, hq⟩
    apply hexceptional
    refine ⟨q, ?_⟩
    rintro ⟨e, j⟩
    rw [hs j e, hq j]
    by_cases hj : (j : Nat) < d <;>
      simp [a, rangeDegIndexSign, arrangementParityCoefficient, hj]
  obtain ⟨i, j, hij, hdet⟩ := rangeDeg_exists_det_pair a s ha hnotprop
  let proj : RangeDegCoefficientSolutions N k d c →
      RangeDegCaseTwoKey (N := N) (k := k) a s := fun R ↦ by
    have hadd : ∑ t, a t * R.1.crossSection t = 0 :=
      (rangeDeg_additive_iff R.1.crossSection).mp R.2.2.1
    have hmoment := R.2.2.2 Finset.univ
    rw [lemma154_full_moment_eq R.1 (rangeDegEta c) s hs] at hmoment
    have hfactor : ((-1 : ZMod N) ^ k * ∏ t, R.1.side t) ≠ 0 := by
      apply mul_ne_zero
      · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      · exact Finset.prod_ne_zero_iff.mpr fun t _ ↦ R.2.1 t
    have hsecond : ∑ t, s t * R.1.crossSection t = 0 :=
      (mul_eq_zero.mp hmoment).resolve_left hfactor
    exact ⟨R.1.side, R.1.base, ⟨R.1.crossSection, hadd, hsecond⟩⟩
  have hinj : Function.Injective proj := by
    intro R S hRS
    apply Subtype.ext
    have hside := congrArg (fun z ↦ z.1) hRS
    have hbase := congrArg (fun z ↦ z.2.1) hRS
    have hcross := congrArg (fun z ↦ z.2.2) hRS
    change R.1.1 = S.1.1 at hside
    change R.1.2.1 = S.1.2.1 at hbase
    have hcross' := congrArg Subtype.val hcross
    change R.1.2.2 = S.1.2.2 at hcross'
    exact Prod.ext hside (Prod.ext hbase hcross')
  calc
    Fintype.card (RangeDegCoefficientSolutions N k d c) ≤
        Fintype.card (RangeDegCaseTwoKey (N := N) (k := k) a s) :=
      Fintype.card_le_of_injective proj hinj
    _ ≤ N ^ ((2 * d + 1) * k + 2 * d - 2) :=
      rangeDeg_case_two_key_card_le hd a s i j hij hdet
    _ ≤ k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      exact Nat.le_mul_of_pos_left _ hk

private lemma rangeDeg_coefficient_solutions_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : RangeDegCoefficient m k d) (hexceptional : rangeDegExceptional (N := N) c) :
    Fintype.card (RangeDegCoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  by_cases hcase : ∃ j, ¬ IsModularMultiple (fun e ↦ rangeDegEta c e j)
      (parityCharacter (N := N))
  · obtain ⟨j, hj⟩ := hcase
    exact rangeDeg_case_one_card_le hprime hodd hk hd c j hj
  · simp only [not_exists, not_not] at hcase
    exact rangeDeg_case_two_card_le hprime hk hd c hcase hexceptional

private def rangeDegZeroCoefficient (m k d : Nat) : RangeDegCoefficient m k d :=
  fun _ _ ↦ ⟨m, by omega⟩

private lemma rangeDeg_zero_coefficient_not_exceptional {N k d : Nat} :
    ¬ rangeDegExceptional (N := N) (rangeDegZeroCoefficient m k d) := by
  intro h
  apply h
  refine ⟨0, ?_⟩
  rintro ⟨e, j⟩
  simp [rangeDegEta, rangeDegZeroCoefficient, rangeDegCoefficientValue]

private abbrev RangeDegExceptionalCoefficients (N m k d : Nat) :=
  {c : RangeDegCoefficient m k d // rangeDegExceptional (N := N) c}

private noncomputable instance rangeDegExceptionalCoefficientsFintype
    (N m k d : Nat) : Fintype (RangeDegExceptionalCoefficients N m k d) := by
  letI : Finite (RangeDegExceptionalCoefficients N m k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma rangeDeg_exceptional_coefficients_card_le (N m k d : Nat) :
    Fintype.card (RangeDegExceptionalCoefficients N m k d) ≤
      (2 * m + 1) ^ (2 * d * 2 ^ k) - 1 := by
  let enc : RangeDegExceptionalCoefficients N m k d →
      {c : RangeDegCoefficient m k d // c ≠ rangeDegZeroCoefficient m k d} :=
    fun c ↦ ⟨c.1, by
      intro hc
      exact rangeDeg_zero_coefficient_not_exceptional (hc ▸ c.2)⟩
  have hinj : Function.Injective enc := by
    intro c c' h
    apply Subtype.ext
    exact congrArg
      (fun z : {q : RangeDegCoefficient m k d //
        q ≠ rangeDegZeroCoefficient m k d} ↦ z.1) h
  calc
    Fintype.card (RangeDegExceptionalCoefficients N m k d) ≤
        Fintype.card
          {c : RangeDegCoefficient m k d // c ≠ rangeDegZeroCoefficient m k d} :=
      Fintype.card_le_of_injective enc hinj
    _ = Fintype.card (RangeDegCoefficient m k d) - 1 := by
      rw [Fintype.card_subtype_compl]
      simp
    _ = (2 * m + 1) ^ (2 * d * 2 ^ k) - 1 := by
      rw [rangeDeg_coefficient_card]

private lemma rangeDeg_degenerate_witness {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) (hdeg : R.IsDegenerateWithin m) :
    ∃ c : RangeDegCoefficient m k d,
      rangeDegExceptional (N := N) c ∧
        ∀ A : Finset (Fin (k + 1)), arrangementMoment R (rangeDegEta c) A = 0 := by
  rcases hdeg with ⟨eta, heta, hnot, hmoment⟩
  let c := rangeDegEncodeCoefficient m eta
  have hceta : rangeDegEta c = eta := by
    funext e j
    exact rangeDeg_encode_value eta heta e j
  have hcexceptional : rangeDegExceptional (N := N) c := by
    intro hmultiple
    apply hnot
    rcases hmultiple with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rintro ⟨e, j⟩
    calc
      (eta e j : ZMod N) = (rangeDegEta c e j : ZMod N) := by
        exact congrArg (fun z : Int ↦ (z : ZMod N))
          (congrFun (congrFun hceta e) j).symm
      _ = q * arrangementParityCoefficient (N := N) e j := hq (e, j)
  exact ⟨c, hcexceptional, fun A ↦ by simpa only [hceta] using hmoment A⟩

private abbrev RangeDegNonzeroDegenerateArrangements
    (N m k d : Nat) [NeZero N] :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m ∧
      ∀ i, R.side i ≠ 0}

private noncomputable instance rangeDegNonzeroDegenerateArrangementsFintype
    (N m k d : Nat) [NeZero N] :
    Fintype (RangeDegNonzeroDegenerateArrangements N m k d) := by
  letI : Finite (RangeDegNonzeroDegenerateArrangements N m k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma rangeDeg_nonzero_degenerate_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (RangeDegNonzeroDegenerateArrangements N m k d) ≤
      ((2 * m + 1) ^ (2 * d * 2 ^ k) - 1) *
        (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by
  let enc : RangeDegNonzeroDegenerateArrangements N m k d →
      Σ c : RangeDegExceptionalCoefficients N m k d,
        RangeDegCoefficientSolutions N k d c.1 := fun R ↦ by
    let w := rangeDeg_degenerate_witness R.1 R.2.2.1
    let c := Classical.choose w
    have hc := Classical.choose_spec w
    exact ⟨⟨c, hc.1⟩, ⟨R.1, R.2.2.2, R.2.1, hc.2⟩⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hRS
  have hcoeff := rangeDeg_exceptional_coefficients_card_le N m k d
  calc
    Fintype.card (RangeDegNonzeroDegenerateArrangements N m k d) ≤
        Fintype.card (Σ c : RangeDegExceptionalCoefficients N m k d,
          RangeDegCoefficientSolutions N k d c.1) :=
      Fintype.card_le_of_injective enc hinj
    _ = ∑ c : RangeDegExceptionalCoefficients N m k d,
          Fintype.card (RangeDegCoefficientSolutions N k d c.1) :=
      Fintype.card_sigma
    _ ≤ ∑ _c : RangeDegExceptionalCoefficients N m k d,
          k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      exact Finset.sum_le_sum fun c _ ↦
        rangeDeg_coefficient_solutions_card_le hprime hodd hk hd c.1 c.2
    _ = Fintype.card (RangeDegExceptionalCoefficients N m k d) *
          (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by simp
    _ ≤ ((2 * m + 1) ^ (2 * d * 2 ^ k) - 1) *
          (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) :=
      Nat.mul_le_mul_right _ hcoeff

private abbrev RangeDegDegenerateArrangements
    (N m k d : Nat) [NeZero N] :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m}

private noncomputable instance rangeDegDegenerateArrangementsFintype
    (N m k d : Nat) [NeZero N] :
    Fintype (RangeDegDegenerateArrangements N m k d) := by
  letI : Finite (RangeDegDegenerateArrangements N m k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma rangeDeg_degenerate_count_eq_card (N m k d : Nat) [NeZero N] :
    degenerateGeneralArrangementCountWithin (N := N) (k := k) m d =
      Fintype.card (RangeDegDegenerateArrangements N m k d) := by
  classical
  unfold degenerateGeneralArrangementCountWithin countWhere
  rw [Finset.filter_congr_decidable]
  symm
  exact Fintype.card_subtype fun R : GeneralArrangement N k d ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m

private lemma rangeDeg_degenerate_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (RangeDegDegenerateArrangements N m k d) ≤
      (2 * m + 1) ^ (2 * d * 2 ^ k) *
        (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by
  let enc : RangeDegDegenerateArrangements N m k d →
      RangeDegZeroSideArrangements N k d ⊕
        RangeDegNonzeroDegenerateArrangements N m k d := fun R ↦ by
    by_cases hzero : ∃ i, R.1.side i = 0
    · exact Sum.inl ⟨R.1, R.2.1, hzero⟩
    · have hnonzero : ∀ i, R.1.side i ≠ 0 := by
        intro i hi
        exact hzero ⟨i, hi⟩
      exact Sum.inr ⟨R.1, R.2.1, R.2.2, hnonzero⟩
  let recover : RangeDegZeroSideArrangements N k d ⊕
      RangeDegNonzeroDegenerateArrangements N m k d →
      GeneralArrangement N k d :=
    Sum.elim (fun z ↦ z.1) (fun z ↦ z.1)
  have hrecover (R : RangeDegDegenerateArrangements N m k d) :
      recover (enc R) = R.1 := by
    dsimp only [recover, enc]
    split <;> rfl
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact (hrecover R).symm.trans ((congrArg recover hRS).trans (hrecover S))
  letI : Fact N.Prime := ⟨hprime⟩
  have hzero := rangeDeg_zero_side_card_le (N := N) hk hd
  have hnonzero := rangeDeg_nonzero_degenerate_card_le (m := m) hprime hodd hk hd
  let Q := (2 * m + 1) ^ (2 * d * 2 ^ k)
  let X := k * N ^ ((2 * d + 1) * k + 2 * d - 2)
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact Nat.one_le_pow _ _ (by omega)
  calc
    Fintype.card (RangeDegDegenerateArrangements N m k d) ≤
        Fintype.card (RangeDegZeroSideArrangements N k d ⊕
          RangeDegNonzeroDegenerateArrangements N m k d) :=
      Fintype.card_le_of_injective enc hinj
    _ = Fintype.card (RangeDegZeroSideArrangements N k d) +
          Fintype.card (RangeDegNonzeroDegenerateArrangements N m k d) := by simp
    _ ≤ X + (Q - 1) * X := Nat.add_le_add hzero hnonzero
    _ = Q * X := by
      calc
        X + (Q - 1) * X = 1 * X + (Q - 1) * X := by rw [one_mul]
        _ = (1 + (Q - 1)) * X := (Nat.add_mul _ _ _).symm
        _ = Q * X := by rw [Nat.add_sub_of_le hQ]

/-- **Lemma 15.4 for coefficients in `[−m, m]`.** -/
theorem degenerate_count_within_le (N m k d : Nat) [NeZero N] (hprime : N.Prime)
    (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (degenerateGeneralArrangementCountWithin (N := N) (k := k) m d : Real) ≤
      (2 * m + 1) ^ (2 * d * 2 ^ k) * k *
        (N : Real) ^ ((2 * d + 1) * k + 2 * d - 2) := by
  have hcard := rangeDeg_degenerate_card_le (m := m) hprime hodd hk hd
  rw [← rangeDeg_degenerate_count_eq_card] at hcard
  have hcard' : degenerateGeneralArrangementCountWithin (N := N) (k := k) m d ≤
      ((2 * m + 1) ^ (2 * d * 2 ^ k) * k) *
        N ^ ((2 * d + 1) * k + 2 * d - 2) := by
    simpa only [mul_assoc] using hcard
  exact_mod_cast hcard'

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs15Walsh2
import GowersSzemeredi.Proofs15LevelSets

/-!
# Degenerate higher-dimensional arrangements

This file proves Lemma 15.4.  The proof separates arrangements with a zero
sidelength from those with all sidelengths nonzero, and then follows the two
coefficient cases in the paper.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private abbrev Lemma154Coefficient (k d : Nat) :=
  (Fin k → Bool) → Fin (2 * d) → Fin 3

private def lemma154CoefficientValue {k d : Nat}
    (c : Lemma154Coefficient k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) : Int :=
  if c e j = 0 then -1 else if c e j = 1 then 0 else 1

private lemma lemma154CoefficientValue_ternary {k d : Nat}
    (c : Lemma154Coefficient k d) :
    IsTernaryCoefficient (fun z : (Fin k → Bool) × Fin (2 * d) =>
      lemma154CoefficientValue c z.1 z.2) := by
  rintro ⟨e, j⟩
  by_cases h0 : c e j = 0
  · simp [lemma154CoefficientValue, h0]
  by_cases h1 : c e j = 1
  · simp [lemma154CoefficientValue, h1]
  have h2 : c e j = 2 := by
    apply Fin.ext
    omega
  simp [lemma154CoefficientValue, h2]

private def lemma154EncodeCoefficient {k d : Nat}
    (eta : (Fin k → Bool) → Fin (2 * d) → Int) :
    Lemma154Coefficient k d :=
  fun e j => if eta e j = -1 then 0 else if eta e j = 0 then 1 else 2

private lemma lemma154_encode_value {k d : Nat}
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (heta : IsTernaryCoefficient
      (fun z : (Fin k → Bool) × Fin (2 * d) => eta z.1 z.2))
    (e : Fin k → Bool) (j : Fin (2 * d)) :
    lemma154CoefficientValue (lemma154EncodeCoefficient eta) e j = eta e j := by
  have h := heta (e, j)
  rcases h with h | h | h <;>
    simp [lemma154CoefficientValue, lemma154EncodeCoefficient, h]

private lemma lemma154_coefficient_card (k d : Nat) :
    Fintype.card (Lemma154Coefficient k d) = 3 ^ (2 * d * 2 ^ k) := by
  simp only [Lemma154Coefficient, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
  rw [← pow_mul]

private def lemma154IndexSign {N d : Nat} (j : Fin (2 * d)) : ZMod N :=
  if (j : Nat) < d then 1 else -1

private lemma lemma154_additive_iff {N d : Nat} (x : Fin (2 * d) → ZMod N) :
    IsAdditiveTuple x ↔ ∑ j, lemma154IndexSign (N := N) j * x j = 0 := by
  classical
  let L := Finset.univ.filter fun j : Fin (2 * d) ↦ (j : Nat) < d
  let U := Finset.univ.filter fun j : Fin (2 * d) ↦ d ≤ (j : Nat)
  have hcomp :
      (Finset.univ.filter fun j : Fin (2 * d) ↦ ¬(j : Nat) < d) = U := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U]
    omega
  have hsum :
      (∑ j, lemma154IndexSign (N := N) j * x j) =
        (∑ j ∈ L, x j) - ∑ j ∈ U, x j := by
    dsimp only [L, U]
    simp_rw [lemma154IndexSign, ite_mul, one_mul, neg_one_mul]
    rw [Finset.sum_ite]
    rw [hcomp, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hsum, sub_eq_zero]
  rfl

private lemma lemma154_card_le_of_fiber_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) (m : Nat)
    (h : ∀ b, Fintype.card {a : A // f a = b} ≤ m) :
    Fintype.card A ≤ Fintype.card B * m := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  calc
    (∑ b : B, Fintype.card {a : A // f a = b}) ≤ ∑ _ : B, m :=
      Finset.sum_le_sum fun b _ => h b
    _ = Fintype.card B * m := by simp

private lemma lemma154_sum_mul_sub_eq_one {N : Nat} {I : Type*}
    [Fintype I] [DecidableEq I] (a x y : I → ZMod N) (i : I)
    (hoff : ∀ t, t ≠ i → x t = y t) :
    (∑ t, a t * x t) - (∑ t, a t * y t) =
      a i * (x i - y i) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t, (a t * x t - a t * y t)) =
        ∑ t, a t * (x t - y t) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ ({i} : Finset I), a t * (x t - y t) := by
      symm
      apply Finset.sum_subset (by simp)
      intro t _ ht
      have hti : t ≠ i := by simpa using ht
      rw [hoff t hti, sub_self, mul_zero]
    _ = a i * (x i - y i) := by simp

private lemma lemma154_sum_mul_sub_eq_two {N : Nat} {I : Type*}
    [Fintype I] [DecidableEq I] (a x y : I → ZMod N) (i j : I)
    (hij : i ≠ j) (hoff : ∀ t, t ≠ i → t ≠ j → x t = y t) :
    (∑ t, a t * x t) - (∑ t, a t * y t) =
      a i * (x i - y i) + a j * (x j - y j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t, (a t * x t - a t * y t)) =
        ∑ t, a t * (x t - y t) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ ({i, j} : Finset I), a t * (x t - y t) := by
      symm
      apply Finset.sum_subset (by simp)
      intro t _ ht
      have hti : t ≠ i := by
        intro h
        subst t
        exact ht (by simp)
      have htj : t ≠ j := by
        intro h
        subst t
        exact ht (by simp)
      rw [hoff t hti htj, sub_self, mul_zero]
    _ = a i * (x i - y i) + a j * (x j - y j) := by simp [hij]

private abbrev Lemma154LinearSolutions {N : Nat} {I : Type*}
    [Fintype I] (a : I → ZMod N) :=
  {x : I → ZMod N // ∑ t, a t * x t = 0}

private lemma lemma154_linear_solutions_card_le {N : Nat} [NeZero N]
    [Fact N.Prime] {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ZMod N) (i : I) (hai : a i ≠ 0) :
    Fintype.card (Lemma154LinearSolutions a) ≤
      N ^ (Fintype.card I - 1) := by
  classical
  let proj : Lemma154LinearSolutions a → ({t : I // t ≠ i} → ZMod N) :=
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
      have hdiff := lemma154_sum_mul_sub_eq_one a x.1 y.1 i hoff
      rw [x.2, y.2, sub_self] at hdiff
      have hz : x.1 i - y.1 i = 0 :=
        (mul_eq_zero.mp hdiff.symm).resolve_left hai
      exact sub_eq_zero.mp hz
    · exact congrFun hxy ⟨t, hti⟩
  calc
    Fintype.card (Lemma154LinearSolutions a) ≤
        Fintype.card ({t : I // t ≠ i} → ZMod N) :=
      Fintype.card_le_of_injective proj hinj
    _ = N ^ (Fintype.card I - 1) := by
      rw [Fintype.card_fun, ZMod.card]
      congr 1
      rw [Fintype.card_subtype_compl]
      simp

private def lemma154DoubleExceptEquiv {I : Type*} [DecidableEq I]
    (i j : I) (hij : i ≠ j) :
    {t : I // t ≠ i ∧ t ≠ j} ≃
      {t : {t : I // t ≠ i} // t ≠ ⟨j, hij.symm⟩} where
  toFun t := ⟨⟨t, t.2.1⟩, by
    intro h
    exact t.2.2 (congrArg Subtype.val h)⟩
  invFun t := ⟨t.1.1, t.1.2, by
    intro h
    apply t.2
    apply Subtype.ext
    exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma lemma154_double_except_card {I : Type*} [Fintype I]
    [DecidableEq I] (i j : I) (hij : i ≠ j) :
    Fintype.card {t : I // t ≠ i ∧ t ≠ j} = Fintype.card I - 2 := by
  rw [Fintype.card_congr (lemma154DoubleExceptEquiv i j hij)]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype_eq]
  omega

private abbrev Lemma154DoubleLinearSolutions {N : Nat} {I : Type*}
    [Fintype I] (a b : I → ZMod N) :=
  {x : I → ZMod N //
    (∑ t, a t * x t = 0) ∧ ∑ t, b t * x t = 0}

private lemma lemma154_double_linear_solutions_card_le {N : Nat} [NeZero N]
    [Fact N.Prime] {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ZMod N) (i j : I) (hij : i ≠ j)
    (hdet : a i * b j - a j * b i ≠ 0) :
    Fintype.card (Lemma154DoubleLinearSolutions a b) ≤
      N ^ (Fintype.card I - 2) := by
  classical
  let proj : Lemma154DoubleLinearSolutions a b →
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
    Fintype.card (Lemma154DoubleLinearSolutions a b) ≤
        Fintype.card ({t : I // t ≠ i ∧ t ≠ j} → ZMod N) :=
      Fintype.card_le_of_injective proj hinj
    _ = N ^ (Fintype.card I - 2) := by
      rw [Fintype.card_fun, ZMod.card, lemma154_double_except_card i j hij]

private abbrev Lemma154AdditiveCrossSections (N d : Nat) :=
  {r : Fin (2 * d) → ZMod N // IsAdditiveTuple r}

private noncomputable instance lemma154AdditiveCrossSectionsFintype
    (N d : Nat) [NeZero N] : Fintype (Lemma154AdditiveCrossSections N d) := by
  letI : Finite (Lemma154AdditiveCrossSections N d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma lemma154_additive_cross_sections_card_le {N d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) :
    Fintype.card (Lemma154AdditiveCrossSections N d) ≤ N ^ (2 * d - 1) := by
  let j0 : Fin (2 * d) := ⟨0, by omega⟩
  let a : Fin (2 * d) → ZMod N := lemma154IndexSign
  let e : Lemma154AdditiveCrossSections N d ≃ Lemma154LinearSolutions a :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun r => lemma154_additive_iff r)
  rw [Fintype.card_congr e]
  have hd0 : 0 < d := by omega
  have ha : a j0 ≠ 0 := by
    simp [a, j0, lemma154IndexSign, hd0]
  simpa [a] using lemma154_linear_solutions_card_le a j0 ha

private abbrev Lemma154ZeroSideArrangements (N k d : Nat) :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ ∃ i, R.side i = 0}

private noncomputable instance lemma154ZeroSideArrangementsFintype
    (N k d : Nat) [NeZero N] : Fintype (Lemma154ZeroSideArrangements N k d) := by
  letI : Finite (Lemma154ZeroSideArrangements N k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev Lemma154ZeroSideAt (N k d : Nat) (i : Fin k) :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.side i = 0}

private noncomputable instance lemma154ZeroSideAtFintype
    (N k d : Nat) [NeZero N] (i : Fin k) :
    Fintype (Lemma154ZeroSideAt N k d i) := by
  letI : Finite (Lemma154ZeroSideAt N k d i) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev Lemma154ZeroSideCode (N k d : Nat) (i : Fin k) :=
  ({t : Fin k // t ≠ i} → ZMod N) ×
    (Fin (2 * d) → Point N k) × Lemma154AdditiveCrossSections N d

private lemma lemma154_zero_side_code_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (i : Fin k) :
    Fintype.card (Lemma154ZeroSideCode N k d i) ≤
      N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
  have hcross := lemma154_additive_cross_sections_card_le (N := N) hd
  calc
    Fintype.card (Lemma154ZeroSideCode N k d i) =
        N ^ (k - 1) * N ^ (2 * d * k) *
          Fintype.card (Lemma154AdditiveCrossSections N d) := by
      simp only [Lemma154ZeroSideCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_fin, ZMod.card, Point]
      simp only [Fintype.card_subtype_eq]
      rw [show (N ^ k) ^ (2 * d) = N ^ (2 * d * k) by
        rw [← pow_mul]
        congr 1
        ring]
      ring
    _ ≤ N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
      exact Nat.mul_le_mul_left (N ^ (k - 1) * N ^ (2 * d * k)) hcross

private lemma lemma154_zero_side_at_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (i : Fin k) :
    Fintype.card (Lemma154ZeroSideAt N k d i) ≤
      N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
  let proj : Lemma154ZeroSideAt N k d i → Lemma154ZeroSideCode N k d i :=
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
    (lemma154_zero_side_code_card_le hd i)

private lemma lemma154_zero_side_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (Lemma154ZeroSideArrangements N k d) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  classical
  let enc : Lemma154ZeroSideArrangements N k d →
      Σ i : Fin k, Lemma154ZeroSideAt N k d i := fun R => by
    let i : Fin k := Classical.choose R.2.2
    exact ⟨i, R.1, R.2.1, Classical.choose_spec R.2.2⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) hRS
  calc
    Fintype.card (Lemma154ZeroSideArrangements N k d) ≤
        Fintype.card (Σ i : Fin k, Lemma154ZeroSideAt N k d i) :=
      Fintype.card_le_of_injective enc hinj
    _ = ∑ i : Fin k, Fintype.card (Lemma154ZeroSideAt N k d i) :=
      Fintype.card_sigma
    _ ≤ ∑ _i : Fin k,
        N ^ (k - 1) * N ^ (2 * d * k) * N ^ (2 * d - 1) := by
      exact Finset.sum_le_sum fun i _ => lemma154_zero_side_at_card_le hd i
    _ = k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← pow_add, ← pow_add]
      congr 2
      have hmul : (2 * d + 1) * k = 2 * d * k + k := by ring
      rw [hmul]
      omega

private noncomputable def lemma154LiftFinset {k : Nat}
    (A : Finset (Fin k)) : Finset (Fin (k + 1)) :=
  A.map Fin.castSuccEmb

private lemma lemma154_vertex_castSucc {N k d : Nat}
    (R : GeneralArrangement N k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) (i : Fin k) :
    R.vertex e j i.castSucc =
      R.base j i + if e i then R.side i else 0 := by
  simp [GeneralArrangement.vertex, GeneralArrangement.cube, AxisCube.vertex,
    AxisCube.base, AxisCube.side, appendCoordinate]

private lemma lemma154_vertex_last {N k d : Nat}
    (R : GeneralArrangement N k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) :
    R.vertex e j (Fin.last k) = R.crossSection j := by
  simp [GeneralArrangement.vertex, appendCoordinate]

private lemma lemma154_vertex_product_lift {N k d : Nat}
    (R : GeneralArrangement N k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) (A : Finset (Fin k)) :
    (∏ i ∈ lemma154LiftFinset A, R.vertex e j i) =
      ∏ i ∈ A, (R.base j i + if e i then R.side i else 0) := by
  classical
  unfold lemma154LiftFinset
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  exact lemma154_vertex_castSucc R e j i

private lemma lemma154_arrangementMoment_lift {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d)
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (A : Finset (Fin k)) :
    arrangementMoment R eta (lemma154LiftFinset A) =
      ∑ j : Fin (2 * d),
        booleanWalshMoment (fun e => eta e j) R.side (R.base j) A := by
  classical
  unfold arrangementMoment booleanWalshMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro e _
  rw [lemma154_vertex_product_lift]

private def lemma154BooleanCoefficient {N k : Nat}
    (eta : (Fin k → Bool) → Int) (h : Point N k)
    (A : Finset (Fin k)) (u : Fin k → Bool) : ZMod N :=
  ∑ e : Fin k → Bool, (eta e : ZMod N) *
    ∏ i : Fin k,
      if i ∈ A then
        if u i then 1 else if e i then h i else 0
      else if u i then 0 else 1

private lemma lemma154_booleanWalshMoment_multilinear {N k : Nat} [NeZero N]
    (eta : (Fin k → Bool) → Int) (h : Point N k)
    (A : Finset (Fin k)) :
    IsMultilinear (fun y => booleanWalshMoment eta h y A) := by
  classical
  refine ⟨lemma154BooleanCoefficient eta h A, ?_⟩
  intro y
  unfold booleanWalshMoment lemma154BooleanCoefficient
  calc
    (∑ e : Fin k → Bool, (eta e : ZMod N) *
        ∏ i ∈ A, (y i + if e i then h i else 0)) =
        ∑ e : Fin k → Bool, (eta e : ZMod N) *
          ∏ i : Fin k,
            ∑ b : Bool,
              (if i ∈ A then
                  if b then 1 else if e i then h i else 0
                else if b then 0 else 1) *
                (if b then y i else 1) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
        ite_mul, mul_ite, one_mul, zero_mul, mul_one]
      symm
      calc
        (∏ x, ((if x ∈ A then y x else 0) +
            if x ∈ A then (if e x then h x else 0) else 1)) =
            ∏ x, if x ∈ A then y x + (if e x then h x else 0) else 1 := by
          apply Finset.prod_congr rfl
          intro x _
          by_cases hx : x ∈ A <;> simp [hx]
        _ = ∏ x ∈ A, (y x + if e x then h x else 0) := by
          rw [Finset.prod_ite]
          simp
    _ = ∑ e : Fin k → Bool, (eta e : ZMod N) *
          ∑ u : Fin k → Bool,
            ∏ i : Fin k,
              (if i ∈ A then
                  if u i then 1 else if e i then h i else 0
                else if u i then 0 else 1) *
                (if u i then y i else 1) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.prod_sum]
    _ = ∑ e : Fin k → Bool, ∑ u : Fin k → Bool,
          (eta e : ZMod N) *
            ∏ i : Fin k,
              (if i ∈ A then
                  if u i then 1 else if e i then h i else 0
                else if u i then 0 else 1) *
                (if u i then y i else 1) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
    _ = ∑ u : Fin k → Bool,
          (∑ e : Fin k → Bool, (eta e : ZMod N) *
            ∏ i : Fin k,
              if i ∈ A then
                if u i then 1 else if e i then h i else 0
              else if u i then 0 else 1) *
            ∏ i : Fin k, if u i then y i else 1 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.prod_mul_distrib]
      ring

private abbrev lemma154Eta {k d : Nat} (c : Lemma154Coefficient k d) :=
  fun e j => lemma154CoefficientValue c e j

private def lemma154Exceptional {N k d : Nat} (c : Lemma154Coefficient k d) : Prop :=
  ¬ IsModularMultiple
      (fun z : (Fin k → Bool) × Fin (2 * d) => lemma154Eta c z.1 z.2)
      (fun z => arrangementParityCoefficient (N := N) z.1 z.2)

private abbrev Lemma154CoefficientSolutions (N k d : Nat) [NeZero N]
    (c : Lemma154Coefficient k d) :=
  {R : GeneralArrangement N k d //
    (∀ i, R.side i ≠ 0) ∧ IsAdditiveTuple R.crossSection ∧
      ∀ A : Finset (Fin (k + 1)), arrangementMoment R (lemma154Eta c) A = 0}

private noncomputable instance lemma154CoefficientSolutionsFintype
    (N k d : Nat) [NeZero N] (c : Lemma154Coefficient k d) :
    Fintype (Lemma154CoefficientSolutions N k d c) := by
  letI : Finite (Lemma154CoefficientSolutions N k d c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev Lemma154CaseOneKey (N k d : Nat) (j : Fin (2 * d)) :=
  Point N k × Lemma154AdditiveCrossSections N d ×
    ({t : Fin (2 * d) // t ≠ j} → Point N k)

private lemma lemma154_case_one_key_card_le {N k d : Nat}
    [NeZero N] [Fact N.Prime] (hd : 1 ≤ d) (j : Fin (2 * d)) :
    Fintype.card (Lemma154CaseOneKey N k d j) ≤
      N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k) := by
  have hcross := lemma154_additive_cross_sections_card_le (N := N) hd
  calc
    Fintype.card (Lemma154CaseOneKey N k d j) =
        N ^ k * Fintype.card (Lemma154AdditiveCrossSections N d) *
          N ^ ((2 * d - 1) * k) := by
      simp only [Lemma154CaseOneKey, Fintype.card_prod, Point,
        Fintype.card_fun, Fintype.card_fin, ZMod.card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      rw [show (N ^ k) ^ (2 * d - 1) = N ^ ((2 * d - 1) * k) by
        rw [← pow_mul]
        congr 1
        ring]
      ring
    _ ≤ N ^ k * N ^ (2 * d - 1) * N ^ ((2 * d - 1) * k) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcross)

private lemma lemma154_level_subtype_card {N k : Nat} [NeZero N]
    (mu : Point N k → ZMod N) (a : ZMod N) :
    Fintype.card {y : Point N k // mu y = a} =
      countWhere fun y : Point N k => mu y = a := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  exact Fintype.card_subtype (fun y : Point N k => mu y = a)

private lemma lemma154_case_one_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : Lemma154Coefficient k d) (j : Fin (2 * d))
    (hblock : ¬ IsModularMultiple (fun e => lemma154Eta c e j)
      (parityCharacter (N := N))) :
    Fintype.card (Lemma154CoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  classical
  letI : Fact N.Prime := ⟨hprime⟩
  let proj : Lemma154CoefficientSolutions N k d c →
      Lemma154CaseOneKey N k d j := fun R =>
    ⟨R.1.side, ⟨R.1.crossSection, R.2.2.1⟩,
      fun t => R.1.base t⟩
  have hfiber : ∀ b : Lemma154CaseOneKey N k d j,
      Fintype.card {R : Lemma154CoefficientSolutions N k d c // proj R = b} ≤
        k * N ^ (k - 1) := by
    intro b
    by_cases hex : Nonempty
        {R : Lemma154CoefficientSolutions N k d c // proj R = b}
    · let R₀ := Classical.choice hex
      have hside : ∀ i, b.1 i ≠ 0 := by
        intro i
        have hs : R₀.1.1.side = b.1 := congrArg (fun z => z.1) R₀.2
        rw [← hs]
        exact R₀.1.2.1 i
      have hnotInvariant : ¬ ∀ (A : Finset (Fin k)) (y z : Point N k),
          booleanWalshMoment (fun e => lemma154Eta c e j) b.1 y A =
            booleanWalshMoment (fun e => lemma154Eta c e j) b.1 z A := by
        intro hinvariant
        apply hblock
        exact corollary_15_2_holds N k hprime hodd b.1
          (fun e => lemma154Eta c e j) hside
          (fun e => lemma154CoefficientValue_ternary c (e, j)) hinvariant
      push Not at hnotInvariant
      obtain ⟨A, y, z, hyz⟩ := hnotInvariant
      let mu : Point N k → ZMod N := fun v =>
        booleanWalshMoment (fun e => lemma154Eta c e j) b.1 v A
      have hmuMultilinear : IsMultilinear mu :=
        lemma154_booleanWalshMoment_multilinear _ _ _
      have hmuNonconstant : ¬ ∃ a, ∀ v, mu v = a := by
        rintro ⟨a, ha⟩
        exact hyz ((ha y).trans (ha z).symm)
      let enc : {R : Lemma154CoefficientSolutions N k d c // proj R = b} →
          {v : Point N k // mu v = mu (R₀.1.1.base j)} := fun R => by
        refine ⟨R.1.1.base j, ?_⟩
        have hproj : proj R.1 = proj R₀.1 := R.2.trans R₀.2.symm
        have hsideEq : R.1.1.side = R₀.1.1.side :=
          congrArg (fun q => q.1) hproj
        have htail : (fun t : {t : Fin (2 * d) // t ≠ j} => R.1.1.base t) =
            (fun t : {t : Fin (2 * d) // t ≠ j} => R₀.1.1.base t) :=
          congrArg (fun q => q.2.2) hproj
        have hoff : ∀ t, t ≠ j →
            booleanWalshMoment (fun e => lemma154Eta c e t) R.1.1.side
                (R.1.1.base t) A =
              booleanWalshMoment (fun e => lemma154Eta c e t) R₀.1.1.side
                (R₀.1.1.base t) A := by
          intro t ht
          have htbase := congrFun htail
            (⟨t, ht⟩ : {q : Fin (2 * d) // q ≠ j})
          rw [hsideEq, htbase]
        have hdiff := lemma154_sum_mul_sub_eq_one
          (fun _ : Fin (2 * d) => (1 : ZMod N))
          (fun t => booleanWalshMoment (fun e => lemma154Eta c e t)
            R.1.1.side (R.1.1.base t) A)
          (fun t => booleanWalshMoment (fun e => lemma154Eta c e t)
            R₀.1.1.side (R₀.1.1.base t) A) j hoff
        have hzeroR := R.1.2.2.2 (lemma154LiftFinset A)
        have hzeroR₀ := R₀.1.2.2.2 (lemma154LiftFinset A)
        rw [lemma154_arrangementMoment_lift] at hzeroR hzeroR₀
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
        Fintype.card {R : Lemma154CoefficientSolutions N k d c // proj R = b} ≤
            Fintype.card {v : Point N k // mu v = mu (R₀.1.1.base j)} :=
          Fintype.card_le_of_injective enc henc
        _ = countWhere (fun v : Point N k => mu v = mu (R₀.1.1.base j)) :=
          lemma154_level_subtype_card mu _
        _ ≤ k * N ^ (k - 1) := hlevelNat
    · haveI : IsEmpty
          {R : Lemma154CoefficientSolutions N k d c // proj R = b} :=
        ⟨fun R => hex ⟨R⟩⟩
      simp
  have htotal := lemma154_card_le_of_fiber_le proj (k * N ^ (k - 1)) hfiber
  have hkey := lemma154_case_one_key_card_le (N := N) (k := k) hd j
  calc
    Fintype.card (Lemma154CoefficientSolutions N k d c) ≤
        Fintype.card (Lemma154CaseOneKey N k d j) *
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
          rw [hmul]
          rw [hsubmul]
          omega

private lemma lemma154_parity_eq_prod {N k : Nat} (e : Fin k → Bool) :
    parityCharacter (N := N) e =
      ∏ i : Fin k, if e i then (-1 : ZMod N) else 1 := by
  classical
  simp only [parityCharacter, boolWeight, countWhere]
  rw [← Finset.prod_const]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : e i = true <;> simp [h]

private lemma lemma154_parity_cube_sum {N k : Nat} [NeZero N]
    (h y : Point N k) :
    (∑ e : Fin k → Bool, parityCharacter (N := N) e *
      ∏ i : Fin k, (y i + if e i then h i else 0)) =
        (-1 : ZMod N) ^ k * ∏ i, h i := by
  classical
  simp_rw [lemma154_parity_eq_prod, ← Finset.prod_mul_distrib]
  calc
    (∑ e : Fin k → Bool,
        ∏ i : Fin k,
          (if e i then (-1 : ZMod N) else 1) *
            (y i + if e i then h i else 0)) =
        ∏ i : Fin k, ∑ b : Bool,
          (if b then (-1 : ZMod N) else 1) *
            (y i + if b then h i else 0) := by
      exact (Fintype.prod_sum (fun i (b : Bool) =>
        (if b then (-1 : ZMod N) else 1) *
          (y i + if b then h i else 0))).symm
    _ = ∏ i : Fin k, (-h i) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      simp
    _ = (-1 : ZMod N) ^ k * ∏ i, h i := by
      have hconst : (-1 : ZMod N) ^ k = ∏ _i : Fin k, (-1 : ZMod N) := by
        simp
      rw [hconst, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring

private lemma lemma154_append_product {N k : Nat} (x : Point N k) (r : ZMod N) :
    (∏ i : Fin (k + 1), appendCoordinate x r i) = (∏ i, x i) * r := by
  induction k with
  | zero =>
      simp [appendCoordinate]
  | succ k ih =>
      rw [Fin.prod_univ_succ]
      have hzero : appendCoordinate x r 0 = x 0 := by
        simp [appendCoordinate]
      have htail :
          (fun i : Fin (k + 1) => appendCoordinate x r i.succ) =
            appendCoordinate (Fin.tail x) r := by
        funext i
        simp [appendCoordinate, Fin.tail]
      rw [hzero, htail, ih]
      rw [Fin.prod_univ_succ]
      simp only [Fin.tail]
      ring

private lemma lemma154_vertex_product_univ {N k d : Nat}
    (R : GeneralArrangement N k d) (e : Fin k → Bool)
    (j : Fin (2 * d)) :
    (∏ i : Fin (k + 1), R.vertex e j i) =
      (∏ i : Fin k, (R.base j i + if e i then R.side i else 0)) *
        R.crossSection j := by
  exact lemma154_append_product _ _

private lemma lemma154_exists_det_pair {N : Nat} [NeZero N] [Fact N.Prime]
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (a b : I → ZMod N) (ha : ∀ i, a i ≠ 0)
    (hnot : ¬ ∃ q, ∀ i, b i = q * a i) :
    ∃ i j, i ≠ j ∧ a i * b j - a j * b i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  let i0 : I := Classical.choice inferInstance
  apply hnot
  refine ⟨b i0 / a i0, ?_⟩
  intro j
  have hdet : a i0 * b j - a j * b i0 = 0 := by
    by_cases hij : i0 = j
    · subst j
      ring
    · exact h i0 j hij
  field_simp [ha i0]
  simpa [mul_comm] using sub_eq_zero.mp hdet

private lemma lemma154_full_moment_eq {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d)
    (eta : (Fin k → Bool) → Fin (2 * d) → Int)
    (s : Fin (2 * d) → ZMod N)
    (hs : ∀ j e, (eta e j : ZMod N) = s j * parityCharacter (N := N) e) :
    arrangementMoment R eta Finset.univ =
      ((-1 : ZMod N) ^ k * ∏ i, R.side i) *
        ∑ j, s j * R.crossSection j := by
  classical
  unfold arrangementMoment
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin (2 * d), ∑ e : Fin k → Bool,
        (eta e j : ZMod N) * ∏ i ∈ Finset.univ, R.vertex e j i) =
        ∑ j : Fin (2 * d), ∑ e : Fin k → Bool,
          (s j * parityCharacter (N := N) e) *
            ((∏ i : Fin k,
              (R.base j i + if e i then R.side i else 0)) *
                R.crossSection j) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro e _
      rw [hs j e, lemma154_vertex_product_univ]
    _ = ∑ j : Fin (2 * d),
          (s j * R.crossSection j) *
            ((-1 : ZMod N) ^ k * ∏ i, R.side i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← lemma154_parity_cube_sum R.side (R.base j)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = ((-1 : ZMod N) ^ k * ∏ i, R.side i) *
          ∑ j, s j * R.crossSection j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

private abbrev Lemma154CaseTwoKey {N k d : Nat} [NeZero N]
    (a s : Fin (2 * d) → ZMod N) :=
  Point N k × (Fin (2 * d) → Point N k) ×
    Lemma154DoubleLinearSolutions a s

private lemma lemma154_case_two_key_card_le {N k d : Nat} [NeZero N]
    [Fact N.Prime] (hd : 1 ≤ d) (a s : Fin (2 * d) → ZMod N)
    (i j : Fin (2 * d)) (hij : i ≠ j)
    (hdet : a i * s j - a j * s i ≠ 0) :
    Fintype.card (Lemma154CaseTwoKey (N := N) (k := k) a s) ≤
      N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  have hcross := lemma154_double_linear_solutions_card_le a s i j hij hdet
  calc
    Fintype.card (Lemma154CaseTwoKey (N := N) (k := k) a s) =
        N ^ k * N ^ (2 * d * k) *
          Fintype.card (Lemma154DoubleLinearSolutions a s) := by
      simp only [Lemma154CaseTwoKey, Fintype.card_prod, Point,
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

private lemma lemma154_case_two_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : Lemma154Coefficient k d)
    (hblocks : ∀ j, IsModularMultiple (fun e ↦ lemma154Eta c e j)
      (parityCharacter (N := N)))
    (hexceptional : lemma154Exceptional (N := N) c) :
    Fintype.card (Lemma154CoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  classical
  letI : Fact N.Prime := ⟨hprime⟩
  letI : Nonempty (Fin (2 * d)) := ⟨⟨0, by omega⟩⟩
  let a : Fin (2 * d) → ZMod N := lemma154IndexSign
  let s : Fin (2 * d) → ZMod N := fun j ↦ Classical.choose (hblocks j)
  have hs : ∀ j e, (lemma154Eta c e j : ZMod N) =
      s j * parityCharacter (N := N) e := by
    intro j e
    exact Classical.choose_spec (hblocks j) e
  have ha : ∀ j, a j ≠ 0 := by
    intro j
    by_cases hj : (j : Nat) < d <;>
      simp [a, lemma154IndexSign, hj]
  have hnotprop : ¬ ∃ q, ∀ j, s j = q * a j := by
    rintro ⟨q, hq⟩
    apply hexceptional
    refine ⟨q, ?_⟩
    rintro ⟨e, j⟩
    rw [hs j e, hq j]
    by_cases hj : (j : Nat) < d <;>
      simp [a, lemma154IndexSign, arrangementParityCoefficient, hj]
  obtain ⟨i, j, hij, hdet⟩ := lemma154_exists_det_pair a s ha hnotprop
  let proj : Lemma154CoefficientSolutions N k d c →
      Lemma154CaseTwoKey (N := N) (k := k) a s := fun R ↦ by
    have hadd : ∑ t, a t * R.1.crossSection t = 0 :=
      (lemma154_additive_iff R.1.crossSection).mp R.2.2.1
    have hmoment := R.2.2.2 Finset.univ
    rw [lemma154_full_moment_eq R.1 (lemma154Eta c) s hs] at hmoment
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
    Fintype.card (Lemma154CoefficientSolutions N k d c) ≤
        Fintype.card (Lemma154CaseTwoKey (N := N) (k := k) a s) :=
      Fintype.card_le_of_injective proj hinj
    _ ≤ N ^ ((2 * d + 1) * k + 2 * d - 2) :=
      lemma154_case_two_key_card_le hd a s i j hij hdet
    _ ≤ k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      exact Nat.le_mul_of_pos_left _ hk

private lemma lemma154_coefficient_solutions_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (c : Lemma154Coefficient k d) (hexceptional : lemma154Exceptional (N := N) c) :
    Fintype.card (Lemma154CoefficientSolutions N k d c) ≤
      k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
  by_cases hcase : ∃ j, ¬ IsModularMultiple (fun e ↦ lemma154Eta c e j)
      (parityCharacter (N := N))
  · obtain ⟨j, hj⟩ := hcase
    exact lemma154_case_one_card_le hprime hodd hk hd c j hj
  · simp only [not_exists, not_not] at hcase
    exact lemma154_case_two_card_le hprime hk hd c hcase hexceptional

private def lemma154ZeroCoefficient (k d : Nat) : Lemma154Coefficient k d :=
  fun _ _ ↦ 1

private lemma lemma154_zero_coefficient_not_exceptional {N k d : Nat} :
    ¬ lemma154Exceptional (N := N) (lemma154ZeroCoefficient k d) := by
  intro h
  apply h
  refine ⟨0, ?_⟩
  rintro ⟨e, j⟩
  simp [lemma154Eta, lemma154ZeroCoefficient, lemma154CoefficientValue]

private abbrev Lemma154ExceptionalCoefficients (N k d : Nat) :=
  {c : Lemma154Coefficient k d // lemma154Exceptional (N := N) c}

private noncomputable instance lemma154ExceptionalCoefficientsFintype
    (N k d : Nat) : Fintype (Lemma154ExceptionalCoefficients N k d) := by
  letI : Finite (Lemma154ExceptionalCoefficients N k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma lemma154_exceptional_coefficients_card_le (N k d : Nat) :
    Fintype.card (Lemma154ExceptionalCoefficients N k d) ≤
      3 ^ (2 * d * 2 ^ k) - 1 := by
  classical
  let enc : Lemma154ExceptionalCoefficients N k d →
      {c : Lemma154Coefficient k d // c ≠ lemma154ZeroCoefficient k d} :=
    fun c ↦ ⟨c.1, by
      intro hc
      exact lemma154_zero_coefficient_not_exceptional (hc ▸ c.2)⟩
  have hinj : Function.Injective enc := by
    intro c c' h
    apply Subtype.ext
    exact congrArg
      (fun z : {q : Lemma154Coefficient k d //
        q ≠ lemma154ZeroCoefficient k d} ↦ z.1) h
  calc
    Fintype.card (Lemma154ExceptionalCoefficients N k d) ≤
        Fintype.card
          {c : Lemma154Coefficient k d // c ≠ lemma154ZeroCoefficient k d} :=
      Fintype.card_le_of_injective enc hinj
    _ = Fintype.card (Lemma154Coefficient k d) - 1 := by
      rw [Fintype.card_subtype_compl]
      simp
    _ = 3 ^ (2 * d * 2 ^ k) - 1 := by
      rw [lemma154_coefficient_card]

private lemma lemma154_degenerate_witness {N k d : Nat} [NeZero N]
    (R : GeneralArrangement N k d) (hdeg : R.IsDegenerate) :
    ∃ c : Lemma154Coefficient k d,
      lemma154Exceptional (N := N) c ∧
        ∀ A : Finset (Fin (k + 1)), arrangementMoment R (lemma154Eta c) A = 0 := by
  rcases hdeg with ⟨eta, heta, hnot, hmoment⟩
  let c := lemma154EncodeCoefficient eta
  have hceta : lemma154Eta c = eta := by
    funext e j
    exact lemma154_encode_value eta heta e j
  have hcexceptional : lemma154Exceptional (N := N) c := by
    intro hmultiple
    apply hnot
    rcases hmultiple with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rintro ⟨e, j⟩
    calc
      (eta e j : ZMod N) = (lemma154Eta c e j : ZMod N) := by
        exact congrArg (fun z : Int ↦ (z : ZMod N))
          (congrFun (congrFun hceta e) j).symm
      _ = q * arrangementParityCoefficient (N := N) e j := hq (e, j)
  exact ⟨c, hcexceptional, fun A ↦ by simpa only [hceta] using hmoment A⟩

private abbrev Lemma154NonzeroDegenerateArrangements
    (N k d : Nat) [NeZero N] :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate ∧
      ∀ i, R.side i ≠ 0}

private noncomputable instance lemma154NonzeroDegenerateArrangementsFintype
    (N k d : Nat) [NeZero N] :
    Fintype (Lemma154NonzeroDegenerateArrangements N k d) := by
  letI : Finite (Lemma154NonzeroDegenerateArrangements N k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma lemma154_nonzero_degenerate_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (Lemma154NonzeroDegenerateArrangements N k d) ≤
      (3 ^ (2 * d * 2 ^ k) - 1) *
        (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by
  classical
  let enc : Lemma154NonzeroDegenerateArrangements N k d →
      Σ c : Lemma154ExceptionalCoefficients N k d,
        Lemma154CoefficientSolutions N k d c.1 := fun R ↦ by
    let w := lemma154_degenerate_witness R.1 R.2.2.1
    let c := Classical.choose w
    have hc := Classical.choose_spec w
    exact ⟨⟨c, hc.1⟩, ⟨R.1, R.2.2.2, R.2.1, hc.2⟩⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hRS
  have hcoeff := lemma154_exceptional_coefficients_card_le N k d
  calc
    Fintype.card (Lemma154NonzeroDegenerateArrangements N k d) ≤
        Fintype.card (Σ c : Lemma154ExceptionalCoefficients N k d,
          Lemma154CoefficientSolutions N k d c.1) :=
      Fintype.card_le_of_injective enc hinj
    _ = ∑ c : Lemma154ExceptionalCoefficients N k d,
          Fintype.card (Lemma154CoefficientSolutions N k d c.1) :=
      Fintype.card_sigma
    _ ≤ ∑ _c : Lemma154ExceptionalCoefficients N k d,
          k * N ^ ((2 * d + 1) * k + 2 * d - 2) := by
      exact Finset.sum_le_sum fun c _ ↦
        lemma154_coefficient_solutions_card_le hprime hodd hk hd c.1 c.2
    _ = Fintype.card (Lemma154ExceptionalCoefficients N k d) *
          (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by simp
    _ ≤ (3 ^ (2 * d * 2 ^ k) - 1) *
          (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) :=
      Nat.mul_le_mul_right _ hcoeff

private abbrev Lemma154DegenerateArrangements
    (N k d : Nat) [NeZero N] :=
  {R : GeneralArrangement N k d //
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate}

private noncomputable instance lemma154DegenerateArrangementsFintype
    (N k d : Nat) [NeZero N] :
    Fintype (Lemma154DegenerateArrangements N k d) := by
  letI : Finite (Lemma154DegenerateArrangements N k d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma lemma154_degenerate_count_eq_card (N k d : Nat) [NeZero N] :
    degenerateGeneralArrangementCount (N := N) (k := k) d =
      Fintype.card (Lemma154DegenerateArrangements N k d) := by
  classical
  unfold degenerateGeneralArrangementCount countWhere
  rw [Finset.filter_congr_decidable]
  symm
  exact Fintype.card_subtype fun R : GeneralArrangement N k d ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate

private lemma lemma154_degenerate_card_le {N k d : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    Fintype.card (Lemma154DegenerateArrangements N k d) ≤
      3 ^ (2 * d * 2 ^ k) *
        (k * N ^ ((2 * d + 1) * k + 2 * d - 2)) := by
  classical
  let enc : Lemma154DegenerateArrangements N k d →
      Lemma154ZeroSideArrangements N k d ⊕
        Lemma154NonzeroDegenerateArrangements N k d := fun R ↦ by
    by_cases hzero : ∃ i, R.1.side i = 0
    · exact Sum.inl ⟨R.1, R.2.1, hzero⟩
    · have hnonzero : ∀ i, R.1.side i ≠ 0 := by
        intro i hi
        exact hzero ⟨i, hi⟩
      exact Sum.inr ⟨R.1, R.2.1, R.2.2, hnonzero⟩
  let recover : Lemma154ZeroSideArrangements N k d ⊕
      Lemma154NonzeroDegenerateArrangements N k d →
      GeneralArrangement N k d :=
    Sum.elim (fun z ↦ z.1) (fun z ↦ z.1)
  have hrecover (R : Lemma154DegenerateArrangements N k d) :
      recover (enc R) = R.1 := by
    dsimp only [recover, enc]
    split <;> rfl
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    exact (hrecover R).symm.trans ((congrArg recover hRS).trans (hrecover S))
  letI : Fact N.Prime := ⟨hprime⟩
  have hzero := lemma154_zero_side_card_le (N := N) hk hd
  have hnonzero := lemma154_nonzero_degenerate_card_le hprime hodd hk hd
  let Q := 3 ^ (2 * d * 2 ^ k)
  let X := k * N ^ ((2 * d + 1) * k + 2 * d - 2)
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact Nat.one_le_pow _ 3 (by omega)
  calc
    Fintype.card (Lemma154DegenerateArrangements N k d) ≤
        Fintype.card (Lemma154ZeroSideArrangements N k d ⊕
          Lemma154NonzeroDegenerateArrangements N k d) :=
      Fintype.card_le_of_injective enc hinj
    _ = Fintype.card (Lemma154ZeroSideArrangements N k d) +
          Fintype.card (Lemma154NonzeroDegenerateArrangements N k d) := by simp
    _ ≤ X + (Q - 1) * X := Nat.add_le_add hzero hnonzero
    _ = Q * X := by
      calc
        X + (Q - 1) * X = 1 * X + (Q - 1) * X := by rw [one_mul]
        _ = (1 + (Q - 1)) * X := (Nat.add_mul _ _ _).symm
        _ = Q * X := by rw [Nat.add_sub_of_le hQ]

/-- Lemma 15.4: the corrected odd-prime bound for degenerate arrangements. -/
theorem lemma_15_4_holds : lemma_15_4 := by
  unfold lemma_15_4
  intro N k d _ hprime hodd hk hd
  have hcard := lemma154_degenerate_card_le hprime hodd hk hd
  rw [← lemma154_degenerate_count_eq_card] at hcard
  have hcard' : degenerateGeneralArrangementCount (N := N) (k := k) d ≤
      (3 ^ (2 * d * 2 ^ k) * k) *
        N ^ ((2 * d + 1) * k + 2 * d - 2) := by
    simpa only [mul_assoc] using hcard
  exact_mod_cast hcard'

end LeanProofs.GowersSzemeredi

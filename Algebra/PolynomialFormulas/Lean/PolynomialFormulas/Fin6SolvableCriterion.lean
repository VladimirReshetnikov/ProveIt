import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Perm.Cycle.Type
import PolynomialFormulas.Fin6BlockSystems

/-!
# Solvable transitive subgroups in degree six

This module connects abstract blocks for a transitive subgroup of `S₆` to the
two explicit finite tables used by the sextic resolvents.  The remaining group-
theoretic step is to prove that a solvable transitive subgroup cannot act
primitively on six letters.
-/

open scoped Pointwise

namespace LeanProofs.PolynomialFormulas.Fin6SolvableCriterion

open MulAction
open LeanProofs.PolynomialFormulas.Fin6BlockSystems

variable (G : Subgroup S6) {B : Set (Fin 6)}

/-- The equivalence relation whose classes are the translates of a nonempty
block. -/
noncomputable def blockSetoid [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) : Setoid (Fin 6) :=
  Setoid.mkClasses (orbit G B) (hB.isBlockSystem hB0).1.2

theorem blockSetoid_classes [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) :
    (blockSetoid G hB hB0).classes = orbit G B := by
  exact Setoid.classes_mkClasses _ (hB.isBlockSystem hB0).1

private theorem blockSetoid_forward_invariant [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) (g : G) {i j : Fin 6}
    (hij : blockSetoid G hB hB0 i j) :
    blockSetoid G hB hB0 (g • i) (g • j) := by
  rw [Setoid.rel_iff_exists_classes, blockSetoid_classes G hB hB0] at hij ⊢
  obtain ⟨C, ⟨h, rfl⟩, hi, hj⟩ := hij
  refine ⟨g • (h • B), ⟨g * h, by simp [mul_smul]⟩, ?_, ?_⟩
  · exact Set.smul_mem_smul_set hi
  · exact Set.smul_mem_smul_set hj

theorem blockSetoid_invariant [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) (g : G) (i j : Fin 6) :
    blockSetoid G hB hB0 (g • i) (g • j) ↔
      blockSetoid G hB hB0 i j := by
  constructor
  · intro h
    have := blockSetoid_forward_invariant G hB hB0 g⁻¹ h
    simpa using this
  · exact blockSetoid_forward_invariant G hB hB0 g

theorem blockSetoid_class_ncard [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) (i : Fin 6) :
    Set.ncard {j | blockSetoid G hB hB0 j i} = Set.ncard B := by
  have hmem : {j | blockSetoid G hB hB0 j i} ∈ orbit G B := by
    rw [← blockSetoid_classes G hB hB0]
    exact Setoid.mem_classes _ i
  obtain ⟨g, hg⟩ := hmem
  rw [← hg]
  change Set.ncard ((fun x ↦ g • x) '' B) = Set.ncard B
  exact Set.ncard_image_of_injective B (MulAction.injective g)

theorem blockSetoid_quotient_card [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hB0 : B.Nonempty) :
    Nat.card (Quotient (blockSetoid G hB hB0)) = Set.ncard (orbit G B) := by
  calc
    Nat.card (Quotient (blockSetoid G hB hB0)) =
        Nat.card (blockSetoid G hB hB0).classes :=
      Nat.card_congr (Setoid.quotientEquivClasses _)
    _ = Set.ncard (blockSetoid G hB hB0).classes := rfl
    _ = Set.ncard (orbit G B) := by rw [blockSetoid_classes G hB hB0]

theorem exists_nontrivial_block [IsPretransitive G (Fin 6)]
    (hprimitive : ¬ IsPreprimitive G (Fin 6)) :
    ∃ B : Set (Fin 6), IsBlock G B ∧ ¬ B.Subsingleton ∧ B ≠ Set.univ := by
  by_contra h
  push Not at h
  apply hprimitive
  refine ⟨fun {B} hB ↦ ?_⟩
  rcases Set.subsingleton_or_nontrivial B with hsub | hnontrivial
  · exact Or.inl hsub
  · exact Or.inr (h B hB hnontrivial)

theorem nontrivial_block_ncard_two_or_three [IsPretransitive G (Fin 6)]
    (hB : IsBlock G B) (hBsub : ¬ B.Subsingleton) (hBuniv : B ≠ Set.univ) :
    Set.ncard B = 2 ∨ Set.ncard B = 3 := by
  have hBnt : B.Nontrivial := (Set.subsingleton_or_nontrivial B).resolve_left hBsub
  have hB0 : B.Nonempty := hBnt.nonempty
  have hdvd : Set.ncard B ∣ 6 := by
    simpa using hB.ncard_dvd_card hB0
  have hlo' : 1 < Set.ncard B := Set.one_lt_ncard_iff_nontrivial.mpr hBnt
  have hlo : 2 ≤ Set.ncard B := by omega
  have hhi : Set.ncard B < 6 := by
    simpa using Set.ncard_lt_card hBuniv
  have hcases : Set.ncard B = 2 ∨ Set.ncard B = 3 ∨
      Set.ncard B = 4 ∨ Set.ncard B = 5 := by omega
  rcases hcases with h2 | h3 | h4 | h5
  · exact Or.inl h2
  · exact Or.inr h3
  · rw [h4] at hdvd
    norm_num at hdvd
  · rw [h5] at hdvd
    norm_num at hdvd

/-- A commutative transitive subgroup of a permutation group acts regularly.
For six letters this forces the subgroup itself to have cardinality six. -/
theorem natCard_eq_six_of_commutative_pretransitive
    (A : Type*) [Group A] [MulAction A (Fin 6)] [IsPretransitive A (Fin 6)]
    (hcomm : ∀ a b : A, a * b = b * a)
    (hfaithful : Function.Injective (MulAction.toPermHom A (Fin 6))) :
    Nat.card A = 6 := by
  have hstab : stabilizer A (0 : Fin 6) = ⊥ := by
    ext a
    constructor
    · intro ha
      rw [mem_stabilizer_iff] at ha
      rw [Subgroup.mem_bot]
      apply hfaithful
      apply Equiv.Perm.ext
      intro y
      obtain ⟨b, hb⟩ := exists_smul_eq A (0 : Fin 6) y
      change a • y = (1 : A) • y
      rw [one_smul]
      calc
        a • y = a • (b • (0 : Fin 6)) := by rw [hb]
        _ = (a * b) • (0 : Fin 6) := (mul_smul a b 0).symm
        _ = (b * a) • (0 : Fin 6) := by rw [hcomm]
        _ = b • (a • (0 : Fin 6)) := mul_smul b a 0
        _ = b • (0 : Fin 6) := by rw [ha]
        _ = y := hb
    · intro ha
      rw [Subgroup.mem_bot] at ha
      subst a
      exact one_mem _
  calc
    Nat.card A = (⊥ : Subgroup A).index := Subgroup.index_bot.symm
    _ = (stabilizer A (0 : Fin 6)).index := by rw [hstab]
    _ = Nat.card (Fin 6) := index_stabilizer_of_transitive A 0
    _ = 6 := by simp

theorem exists_last_nontrivial_derived (H : Type*) [Group H] [Nontrivial H]
    [IsSolvable H] :
    ∃ k, derivedSeries H k ≠ ⊥ ∧ derivedSeries H (k + 1) = ⊥ := by
  have aux : ∀ n, derivedSeries H n = ⊥ →
      ∃ k, derivedSeries H k ≠ ⊥ ∧ derivedSeries H (k + 1) = ⊥ := by
    intro n
    induction n with
    | zero =>
        intro h
        rw [derivedSeries_zero] at h
        exact (top_ne_bot h).elim
    | succ n ih =>
        intro h
        by_cases hn : derivedSeries H n = ⊥
        · exact ih hn
        · exact ⟨n, hn, h⟩
  obtain ⟨n, hn⟩ := (inferInstance : IsSolvable H).solvable
  exact aux n hn

/-- In a primitive solvable permutation group, the last nontrivial derived
subgroup would be a nontrivial commutative normal transitive subgroup. -/
theorem exists_commutative_normal_pretransitive_of_primitive
    (H : Subgroup S6) [IsSolvable H] [IsPreprimitive H (Fin 6)] :
    ∃ A : Subgroup H,
      A ≠ ⊥ ∧ A.Normal ∧ (∀ a b : A, a * b = b * a) ∧
        IsPretransitive A (Fin 6) := by
  letI : Nontrivial H := by
    obtain ⟨g, hg⟩ := exists_smul_eq H (0 : Fin 6) (1 : Fin 6)
    apply nontrivial_of_ne g 1
    intro h
    subst g
    norm_num at hg
  obtain ⟨k, hk, hks⟩ := exists_last_nontrivial_derived H
  let A : Subgroup H := derivedSeries H k
  have hAnormal : A.Normal := derivedSeries_normal H k
  letI : A.Normal := hAnormal
  have hAcommutator : commutator A = ⊥ := by
    apply le_bot_iff.mp
    have hmap : Subgroup.map A.subtype (commutator A) = ⊥ := by
      rw [A.map_subtype_commutator]
      change derivedSeries H (k + 1) = ⊥
      exact hks
    have hle := (Subgroup.map_eq_bot_iff (commutator A)).mp hmap
    simpa using hle
  have hAcomm : ∀ a b : A, a * b = b * a :=
    (commutator_eq_bot_iff A).mp hAcommutator |>.is_comm.comm
  have hfixed : fixedPoints A (Fin 6) ≠ Set.univ := by
    intro hfixed
    apply hk
    apply le_bot_iff.mp
    intro a ha
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro i
    have hi : i ∈ fixedPoints A (Fin 6) := by rw [hfixed]; trivial
    have hfix := (mem_fixedPoints.mp hi) ⟨a, ha⟩
    change (a : S6) i = i at hfix
    exact hfix
  have hApre : IsPretransitive A (Fin 6) :=
    IsQuasiPreprimitive.isPretransitive_of_normal hfixed
  exact ⟨A, hk, hAnormal, hAcomm, hApre⟩

set_option maxHeartbeats 2000000 in
/-- A solvable transitive subgroup of `S₆` cannot be primitive.  The last
nontrivial derived subgroup would be abelian, normal, and transitive, hence a
regular group of order six.  Its characteristic subgroup of squares has order
three; primitivity would force that three-element subgroup to act transitively
on six points, which is impossible. -/
theorem not_preprimitive_of_solvable (H : Subgroup S6) [IsSolvable H]
    [IsPretransitive H (Fin 6)] : ¬ IsPreprimitive H (Fin 6) := by
  intro hprimitive
  letI : IsPreprimitive H (Fin 6) := hprimitive
  obtain ⟨A, hAne, hAnormal, hAcomm, hApre⟩ :=
    exists_commutative_normal_pretransitive_of_primitive H
  letI : A.Normal := hAnormal
  letI : IsPretransitive A (Fin 6) := hApre
  have hAfaithful : Function.Injective (MulAction.toPermHom A (Fin 6)) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro i
    have hi := congrArg (fun q : Equiv.Perm (Fin 6) ↦ q i) hab
    exact hi
  have hAcard : Nat.card A = 6 :=
    natCard_eq_six_of_commutative_pretransitive A hAcomm hAfaithful
  letI : CommGroup A := { (inferInstance : Group A) with
    mul_comm := hAcomm }
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := A) 2 (by
    rw [← Nat.card_eq_fintype_card, hAcard]
    norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card (G := A) 3 (by
    rw [← Nat.card_eq_fintype_card, hAcard]
    norm_num)
  have hxy : orderOf (x * y) = 6 := by
    have hcop : (orderOf x).Coprime (orderOf y) := by
      rw [hx, hy]
      decide
    rw [(Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy]
  letI : IsCyclic A := isCyclic_of_orderOf_eq_card (x * y) (by
    rw [hAcard]
    exact hxy)
  let R : Subgroup A := (powMonoidHom (α := A) 2).range
  let P : Subgroup H := R.map A.subtype
  have hRcard : Nat.card R = 3 := by
    change Nat.card (powMonoidHom (α := A) 2).range = 3
    rw [IsCyclic.card_powMonoidHom_range A 2, hAcard]
    norm_num
  have hPcard : Nat.card P = 3 := by
    rw [← hRcard]
    exact (Nat.card_congr
      (R.equivMapOfInjective A.subtype A.subtype_injective).toEquiv).symm
  have hPnormal : P.Normal := by
    constructor
    intro n hn g
    rcases Subgroup.mem_map.mp hn with ⟨a, ha, rfl⟩
    rcases ha with ⟨z, rfl⟩
    let w : A :=
      ⟨g * (z : H) * g⁻¹, hAnormal.conj_mem (z : H) z.property g⟩
    apply Subgroup.mem_map.mpr
    refine ⟨w ^ 2, ⟨w, rfl⟩, ?_⟩
    change ((w ^ 2 : A) : H) = g * ((z ^ 2 : A) : H) * g⁻¹
    dsimp [w]
    simp [pow_two, mul_assoc]
  letI : P.Normal := hPnormal
  have hPne : P ≠ ⊥ := by
    intro h
    have hc := hPcard
    rw [h] at hc
    norm_num at hc
  have hPfixed : fixedPoints P (Fin 6) ≠ Set.univ := by
    intro hfixed
    apply hPne
    apply le_bot_iff.mp
    intro p hp
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro i
    have hi : i ∈ fixedPoints P (Fin 6) := by rw [hfixed]; trivial
    have hfix := (mem_fixedPoints.mp hi) ⟨p, hp⟩
    change (p : S6) i = i at hfix
    exact hfix
  have hPpre : IsPretransitive P (Fin 6) :=
    IsQuasiPreprimitive.isPretransitive_of_normal hPfixed
  letI : IsPretransitive P (Fin 6) := hPpre
  have hdvd := (stabilizer P (0 : Fin 6)).index_dvd_card
  rw [index_stabilizer_of_transitive P 0, hPcard] at hdvd
  norm_num at hdvd

/-- Every nontrivial block system on six letters is one of the two explicit
tables. -/
theorem le_explicit_stabilizer_of_nonpreprimitive
    [IsPretransitive G (Fin 6)] (hprimitive : ¬ IsPreprimitive G (Fin 6)) :
    (∃ p : PairPartition, G ≤ pairStabilizer p) ∨
      (∃ p : TriplePartition, G ≤ tripleStabilizer p) := by
  obtain ⟨B, hB, hBsub, hBuniv⟩ := exists_nontrivial_block G hprimitive
  have hB0 : B.Nonempty :=
    ((Set.subsingleton_or_nontrivial B).resolve_left hBsub).nonempty
  let r := blockSetoid G hB hB0
  have hinv : ∀ g ∈ G, ∀ i j, r (g i) (g j) ↔ r i j := by
    intro g hg i j
    exact blockSetoid_invariant G hB hB0 ⟨g, hg⟩ i j
  rcases nontrivial_block_ncard_two_or_three G hB hBsub hBuniv with hcard | hcard
  · left
    have hq : Nat.card (Quotient r) = 3 := by
      have hmul := hB.ncard_block_mul_ncard_orbit_eq hB0
      rw [hcard] at hmul
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
      have horbit : Set.ncard (orbit G B) = 3 := by omega
      exact (blockSetoid_quotient_card G hB hB0).trans horbit
    letI : Fintype (Quotient r) := Fintype.ofFinite _
    let e : Quotient r ≃ Fin 3 := Fintype.equivOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hq)
    exact le_pairStabilizer_of_invariant_setoid G r e
      (fun i ↦ (blockSetoid_class_ncard G hB hB0 i).trans hcard) hinv
  · right
    have hq : Nat.card (Quotient r) = 2 := by
      have hmul := hB.ncard_block_mul_ncard_orbit_eq hB0
      rw [hcard] at hmul
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hmul
      have horbit : Set.ncard (orbit G B) = 2 := by omega
      exact (blockSetoid_quotient_card G hB hB0).trans horbit
    letI : Fintype (Quotient r) := Fintype.ofFinite _
    let e : Quotient r ≃ Fin 2 := Fintype.equivOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hq)
    exact le_tripleStabilizer_of_invariant_setoid G r e
      (fun i ↦ (blockSetoid_class_ncard G hB hB0 i).trans hcard) hinv

/-- Classification in the exact form needed by the two sextic resolvents: a
transitive subgroup of `S₆` is solvable exactly when it fixes a partition into
three pairs or a partition into two triples. -/
theorem isSolvable_iff_le_pair_or_triple (H : Subgroup S6)
    [IsPretransitive H (Fin 6)] :
    IsSolvable H ↔
      (∃ p : PairPartition, H ≤ pairStabilizer p) ∨
      (∃ p : TriplePartition, H ≤ tripleStabilizer p) := by
  constructor
  · intro hsolvable
    letI : IsSolvable H := hsolvable
    exact le_explicit_stabilizer_of_nonpreprimitive H
      (not_preprimitive_of_solvable H)
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · exact solvable_of_le_pairStabilizer H p hp
    · exact solvable_of_le_tripleStabilizer H p hp

end LeanProofs.PolynomialFormulas.Fin6SolvableCriterion

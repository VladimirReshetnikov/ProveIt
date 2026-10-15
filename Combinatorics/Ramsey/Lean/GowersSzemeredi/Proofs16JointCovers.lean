import GowersSzemeredi.Proofs16WithLemma6
import GowersSzemeredi.Proofs16SinglePieceGradedRemainder

/-! Joint covers: additive composition of vertex covers (Notes L.12).

The remainder of the single-piece step needs one multilinear map per non-top
cube vertex on a common dense piece. `remainder_piece_on` and its graded form
nest one *provider* per vertex, each applied at the density the previous one
left, so the `t`-degrees of the vertex controls multiply.

The providers come from covers (`MultiplyLinearWith`), which work at a
precision fixed in advance. Composed as covers, they refine one partition
vertex by vertex, each at its own precision `θ_e`. The bad sets add up, and a
single pigeonhole at the end picks one map per vertex:
* `JointCoverOn E Dom f s Qt Et P`: a partition of `P` into proper boxes of
  width at least `P.width^Et`, a good set of density `1 - s`, and at most
  `Qt` tuples of maps per cell, one map per index in `E`;
* `joint_cover_on`: the covers of the `f e` give `JointCoverOn` with
  `s = Σ θ_e`, `Qt = Π Qb_e(θ_e)` and `Et = Π Eb_e(θ_e)`;
* `JointCoverOn.piece`: on a set of density `θ` inside every domain, one box
  carries one map per index on a `(θ - s)/Qt` fraction;
* `remainder_piece_of_vertex_covers`: the remainder map on that piece.

The density `(θ - Σ θ_e)/Π Qb_e(θ_e)` has `t`-degree `1 + Σ D_e`, the sum
of the vertex degrees rather than their product. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- **Joint cover of a family of partial functions on one box.** -/
def JointCoverOn {N d : Nat} [NeZero N] {ι : Type*} (E : Finset ι)
    (Dom : ι → Finset (Point N d)) (f : ι → Point N d → ZMod N)
    (s Qt Et : Real) (P : Box N d) : Prop :=
  ∃ M q : Nat, ∃ G : Finset (Point N d), ∃ Q : Fin M → Box N d,
    ∃ mu : Fin M → Fin q → ι → Point N d → ZMod N,
      G ⊆ P.carrier ∧ (1 - s) * (P.carrier.card : Real) ≤ G.card ∧
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧ (q : Real) ≤ Qt ∧
      (∀ j, (P.width : Real) ^ Et ≤ (Q j).width) ∧
      (∀ j i, ∀ e ∈ E, IsMultilinear (mu j i e)) ∧
      ∀ j x, x ∈ (Q j).carrier → x ∈ G → (∀ e ∈ E, x ∈ Dom e) →
        ∃ i, ∀ e ∈ E, f e x = mu j i e x

/-- **Covers compose additively.** -/
theorem joint_cover_on {N d : Nat} [NeZero N] {ι : Type*} [DecidableEq ι]
    (Dom : ι → Finset (Point N d)) (f : ι → Point N d → ZMod N)
    (Qb Eb : ι → Real → Real) (θ : ι → Real) :
    ∀ E : Finset ι,
      (∀ e ∈ E, MultiplyLinearWith (Qb e) (Eb e) (partialGraph (Dom e) (f e))) →
      (∀ e ∈ E, 0 < θ e ∧ θ e ≤ 1) → (∀ e ∈ E, 0 ≤ Qb e (θ e)) →
      (∀ e ∈ E, 0 ≤ Eb e (θ e)) →
      ∀ P : Box N d, P.IsProper →
        JointCoverOn E Dom f (∑ e ∈ E, θ e) (∏ e ∈ E, Qb e (θ e)) (∏ e ∈ E, Eb e (θ e)) P := by
  intro E
  induction E using Finset.induction_on with
  | empty =>
    intro _ _ _ _ P hP
    have hself : IsBoxPartition (fun _ : Fin 1 => P) P := by
      refine ⟨fun x => ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩, fun i j hij => ?_⟩
      simp [Subsingleton.elim i j] at hij
    refine ⟨1, 1, P.carrier, fun _ => P, fun _ _ _ _ => 0, Finset.Subset.refl _, ?_,
      hself, fun _ => hP, by simp, fun _ => by simp, fun _ _ e he => by simp at he,
      fun _ x _ _ _ => ⟨0, fun e he => by simp at he⟩⟩
    simp
  | insert a E ha ih =>
    intro hML hθ hQ hEb P hP
    have hML' : ∀ e ∈ E, MultiplyLinearWith (Qb e) (Eb e) (partialGraph (Dom e) (f e)) :=
      fun e he => hML e (Finset.mem_insert_of_mem he)
    obtain ⟨M, q, G, Q, mu, hGP, hGm, hQpart, hQprop, hq, hQw, hmu, hcov⟩ :=
      ih hML' (fun e he => hθ e (Finset.mem_insert_of_mem he))
        (fun e he => hQ e (Finset.mem_insert_of_mem he))
        (fun e he => hEb e (Finset.mem_insert_of_mem he)) P hP
    obtain ⟨hθa, hθa1⟩ := hθ a (Finset.mem_insert_self a E)
    obtain ⟨q', G', M', R, mu', hq', hG'P, hG'm, hRpart, hRprop, hRw, hmu', hcov'⟩ :=
      (hML a (Finset.mem_insert_self a E)).on_partition (θ a) hθa hθa1
        (hQ a (Finset.mem_insert_self a E)) P Q hQpart hQprop
    set eqv := section5NatFlattenEquiv M'
    set fp : Fin q × Fin q' ≃ Fin (q * q') := finProdFinEquiv
    refine ⟨∑ j, M' j, q * q', G ∩ G', boxFlatten M' R,
      fun J i e => if e = a then mu' (eqv.symm J).1 (eqv.symm J).2 (fp.symm i).2
        else mu (eqv.symm J).1 (fp.symm i).1 e,
      fun x hx => hGP (Finset.mem_inter.mp hx).1, ?_, boxFlatten_partition P Q M' R hQpart hRpart,
      fun J => hRprop _ _, ?_, ?_, ?_, ?_⟩
    · -- the good set
      rw [Finset.sum_insert ha]
      have hu : (G ∪ G').card ≤ P.carrier.card :=
        Finset.card_le_card (Finset.union_subset hGP hG'P)
      have hui := Finset.card_union_add_card_inter G G'
      have hu' : ((G ∪ G').card : Real) + ((G ∩ G').card : Real) = G.card + G'.card := by
        exact_mod_cast hui
      have huR : ((G ∪ G').card : Real) ≤ P.carrier.card := by exact_mod_cast hu
      nlinarith
    · -- the count
      rw [Finset.prod_insert ha]
      have hq0 : (0 : Real) ≤ q := Nat.cast_nonneg _
      have hprod : 0 ≤ ∏ e ∈ E, Qb e (θ e) := hq0.trans hq
      push_cast
      rw [mul_comm (Qb a (θ a))]
      exact mul_le_mul hq hq' (Nat.cast_nonneg _) hprod
    · -- the widths
      intro J
      rw [Finset.prod_insert ha, mul_comm, Real.rpow_mul (Nat.cast_nonneg _)]
      refine le_trans ?_ (hRw (eqv.symm J).1 (eqv.symm J).2)
      exact Real.rpow_le_rpow (by positivity) (hQw _) (hEb a (Finset.mem_insert_self a E))
    · -- multilinearity
      intro J i e he
      dsimp only
      split_ifs with hea
      · exact hmu' _ _ _
      · exact hmu _ _ e ((Finset.mem_insert.mp he).resolve_left hea)
    · -- the cover
      intro J x hxR hxG hxD
      obtain ⟨hxG1, hxG2⟩ := Finset.mem_inter.mp hxG
      have hxR' : x ∈ (R (eqv.symm J).1 (eqv.symm J).2).carrier := hxR
      have hxQ : x ∈ (Q (eqv.symm J).1).carrier :=
        IsPartition.cell_subset (hRpart (eqv.symm J).1) (eqv.symm J).2 hxR'
      obtain ⟨i1, hi1⟩ := hcov (eqv.symm J).1 x hxQ hxG1
        (fun e he => hxD e (Finset.mem_insert_of_mem he))
      obtain ⟨i2, hi2⟩ := hcov' (eqv.symm J).1 (eqv.symm J).2 x hxR' hxG2 (f a x)
        (Finset.mem_image.mpr ⟨x, hxD a (Finset.mem_insert_self a E), rfl⟩)
      refine ⟨fp (i1, i2), fun e he => ?_⟩
      have hs : fp.symm (fp (i1, i2)) = (i1, i2) := fp.symm_apply_apply _
      show f e x = (if e = a then mu' (eqv.symm J).1 (eqv.symm J).2 (fp.symm (fp (i1, i2))).2
        else mu (eqv.symm J).1 (fp.symm (fp (i1, i2))).1 e) x
      rw [hs]
      split_ifs with hea
      · subst hea; exact hi2
      · exact hi1 e ((Finset.mem_insert.mp he).resolve_left hea)

/-- **One piece from a joint cover**: a single pigeonhole over the tuples. -/
theorem JointCoverOn.piece {N d : Nat} [NeZero N] {ι : Type*} {E : Finset ι}
    {Dom : ι → Finset (Point N d)} {f : ι → Point N d → ZMod N} {s Qt Et : Real}
    {P : Box N d} (hJ : JointCoverOn E Dom f s Qt Et P) {theta : Real} (hs : s < theta)
    (H : Finset (Point N d)) (hHP : H ⊆ P.carrier) (hHD : ∀ e ∈ E, H ⊆ Dom e)
    (hHc : theta * P.carrier.card ≤ H.card) (hPne : P.carrier.Nonempty) :
    ∃ (R : Box N d) (nu : ι → Point N d → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧ (P.width : Real) ^ Et ≤ R.width ∧
      (∀ e ∈ E, IsMultilinear (nu e)) ∧
      (theta - s) / Qt * R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ ∀ e ∈ E, f e x = nu e x).card := by
  classical
  obtain ⟨M, q, G, Q, mu, hGP, hGm, hQpart, hQprop, hq, hQw, hmu, hcov⟩ := hJ
  -- the good part of `H`
  have hHG : (theta - s) * P.carrier.card ≤ (H ∩ G).card := by
    have hu : (H ∪ G).card ≤ P.carrier.card :=
      Finset.card_le_card (Finset.union_subset hHP hGP)
    have hui := Finset.card_union_add_card_inter H G
    have hu' : ((H ∪ G).card : Real) + ((H ∩ G).card : Real) = H.card + G.card := by
      exact_mod_cast hui
    have huR : ((H ∪ G).card : Real) ≤ P.carrier.card := by exact_mod_cast hu
    nlinarith
  have hPpos : (0 : Real) < P.carrier.card := by exact_mod_cast hPne.card_pos
  have hne : (H ∩ G).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos (by linarith) hPpos) hHG)
  obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (Q j).carrier) P.carrier hQpart (H ∩ G) id
    (fun x hx => hGP (Finset.mem_inter.mp hx).2) hne hHG
  set D := (H ∩ G).filter fun x => id x ∈ (Q j).carrier with hDdef
  have hDmem : ∀ x ∈ D, x ∈ H ∧ x ∈ G ∧ x ∈ (Q j).carrier := fun x hx => by
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact ⟨(Finset.mem_inter.mp hx1).1, (Finset.mem_inter.mp hx1).2, hx2⟩
  have hcovD : ∀ x ∈ D, ∃ i, ∀ e ∈ E, f e x = mu j i e x := fun x hx => by
    obtain ⟨hxH, hxG, hxQ⟩ := hDmem x hx
    exact hcov j x hxQ hxG fun e he => hHD e he hxH
  have hQj := IsPartition.cell_subset hQpart j
  have hst : (0 : Real) ≤ theta - s := by linarith
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · -- no tuples: the dense cell is empty of covered points
    subst hq0
    have hD0 : D = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨i, -⟩ := hcovD x hx
      exact i.elim0
    rw [hD0, Finset.card_empty, Nat.cast_zero] at hj
    refine ⟨Q j, fun _ _ => 0, hQprop j, hQj, hQw j, fun e _ => isMultilinear_constant 0, ?_⟩
    rcases le_or_gt Qt 0 with hQt | hQt
    · calc (theta - s) / Qt * (Q j).carrier.card ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonneg_of_nonpos hst hQt)
              (Nat.cast_nonneg _)
        _ ≤ _ := Nat.cast_nonneg _
    · calc (theta - s) / Qt * (Q j).carrier.card = ((theta - s) * (Q j).carrier.card) / Qt := by
            ring
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hj hQt.le
        _ ≤ _ := Nat.cast_nonneg _
  · have hqR : (0 : Real) < q := by exact_mod_cast hq0
    have hQt : 0 < Qt := lt_of_lt_of_le hqR hq
    have hsum : (D.card : Real) ≤ ∑ i, ((D.filter fun x => ∀ e ∈ E, f e x = mu j i e x).card : Real) := by
      have hsub : D ⊆ Finset.univ.biUnion fun i => D.filter fun x => ∀ e ∈ E, f e x = mu j i e x := by
        intro x hx
        obtain ⟨i, hi⟩ := hcovD x hx
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hx, hi⟩⟩
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hne' : (Finset.univ : Finset (Fin q)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hq0⟩⟩
    have hle : ∑ _i : Fin q, (D.card : Real) / q ≤
        ∑ i, ((D.filter fun x => ∀ e ∈ E, f e x = mu j i e x).card : Real) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ hqR.ne']
      exact hsum
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne' hle
    refine ⟨Q j, fun e => mu j i e, hQprop j, hQj, hQw j, fun e he => hmu j i e he, ?_⟩
    have hsub : (D.filter fun x => ∀ e ∈ E, f e x = mu j i e x) ⊆
        H.filter fun x => x ∈ (Q j).carrier ∧ ∀ e ∈ E, f e x = mu j i e x := fun x hx => by
      obtain ⟨hxD, hxe⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxH, -, hxQ⟩ := hDmem x hxD
      exact Finset.mem_filter.mpr ⟨hxH, hxQ, hxe⟩
    calc (theta - s) / Qt * (Q j).carrier.card = ((theta - s) * (Q j).carrier.card) / Qt := by
          ring
      _ ≤ (D.card : Real) / Qt := div_le_div_of_nonneg_right hj hQt.le
      _ ≤ (D.card : Real) / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqR hq
      _ ≤ _ := hi.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- **The remainder map from vertex covers**, on one piece of density
`(θ - Σ θ_e)/Π Qb_e(θ_e)`. -/
theorem remainder_piece_of_vertex_covers {N k : Nat} [NeZero N] [Fact N.Prime]
    {phi : Point N (k + 1) → ZMod N} {x0 : Point N k}
    (Dom : (Fin k → Bool) → Finset (Point N (k + 1)))
    (Qb Eb : (Fin k → Bool) → Real → Real) (θv : (Fin k → Bool) → Real)
    (hML : ∀ e : Fin k → Bool, e ≠ (fun _ => true) →
      MultiplyLinearWith (Qb e) (Eb e) (partialGraph (Dom e) (section16TranslatedVertex phi x0 e)))
    (hθv : ∀ e, 0 < θv e ∧ θv e ≤ 1) (hQb : ∀ e, 0 ≤ Qb e (θv e)) (hEb : ∀ e, 0 ≤ Eb e (θv e))
    {theta : Real}
    (hs : ∑ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), θv e < theta)
    (P : Box N (k + 1)) (H : Finset (Point N (k + 1))) (hP : P.IsProper) (hHP : H ⊆ P.carrier)
    (hHD : ∀ e : Fin k → Bool, e ≠ (fun _ => true) → H ⊆ Dom e)
    (hHc : theta * P.carrier.card ≤ H.card) (hPne : P.carrier.Nonempty) :
    ∃ (R : Box N (k + 1)) (mu : Point N (k + 1) → ZMod N),
      R.IsProper ∧ R.carrier ⊆ P.carrier ∧
      (P.width : Real) ^ (∏ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true),
        Eb e (θv e)) ≤ R.width ∧
      IsMultilinear mu ∧
      (theta - ∑ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), θv e) /
          (∏ e ∈ Finset.univ.filter (fun e : Fin k → Bool => e ≠ fun _ => true), Qb e (θv e)) *
          R.carrier.card ≤
        (H.filter fun x => x ∈ R.carrier ∧ section16PhiRemainder phi x0 x = mu x).card := by
  classical
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  have hEmem : ∀ e ∈ E, e ≠ fun _ => true := fun e he => (Finset.mem_filter.mp he).2
  have hJ := joint_cover_on Dom (section16TranslatedVertex phi x0) Qb Eb θv E
    (fun e he => hML e (hEmem e he)) (fun e _ => hθv e) (fun e _ => hQb e) (fun e _ => hEb e) P hP
  obtain ⟨R, nu, hR, hRP, hRw, hnu, hRc⟩ :=
    hJ.piece hs H hHP (fun e he => hHD e (hEmem e he)) hHc hPne
  refine ⟨R, fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x, hR, hRP, hRw,
    ?_, ?_⟩
  · have hsum := (IsMultilinear.finset_sum E
      (fun e x => (-1 : ZMod N) ^ (k + boolWeight e) * nu e x)
      (fun e he => (hnu e he).const_mul _)).const_mul (-1)
    have hfun : (fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x) =
        fun x => (-1) * ∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x :=
      funext fun x => by ring
    rw [hfun]
    exact hsum
  · refine hRc.trans (Nat.cast_le.mpr (Finset.card_le_card ?_))
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    obtain ⟨hxH, hxR, hxg⟩ := hx
    refine ⟨hxH, hxR, ?_⟩
    simp only [section16PhiRemainder]
    rw [← hEdef]
    congr 1
    exact Finset.sum_congr rfl fun e he => by
      rw [hxg e he]

end LeanProofs.GowersSzemeredi

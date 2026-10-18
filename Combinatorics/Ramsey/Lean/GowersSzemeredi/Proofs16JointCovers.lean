import GowersSzemeredi.Proofs16PieceCalculus

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

/-- Two subsets of `S` meet in at least `|G| + |G'| - |S|` points. -/
private lemma card_add_card_le_card_inter_add {X : Type*} [DecidableEq X] {G G' S : Finset X}
    (hG : G ⊆ S) (hG' : G' ⊆ S) : (G.card : Real) + G'.card ≤ (G ∩ G').card + S.card := by
  have h1 := Finset.card_union_add_card_inter G G'
  have h2 := Finset.card_le_card (Finset.union_subset hG hG')
  exact_mod_cast (by omega : G.card + G'.card ≤ (G ∩ G').card + S.card)

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
    refine ⟨1, 1, P.carrier, fun _ => P, fun _ _ _ _ => 0, subset_rfl, by simp,
      ⟨fun x => ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩, fun i j hij => ?_⟩, fun _ => hP, by simp,
      fun _ => by simp, fun _ _ e he => by simp at he,
      fun _ x _ _ _ => ⟨0, fun e he => by simp at he⟩⟩
    simp [Subsingleton.elim i j] at hij
  | insert a E ha ih =>
    intro hML hθ hQ hEb P hP
    simp only [Finset.forall_mem_insert] at hML hθ hQ hEb
    obtain ⟨M, q, G, Q, mu, hGP, hGm, hQpart, hQprop, hq, hQw, hmu, hcov⟩ :=
      ih hML.2 hθ.2 hQ.2 hEb.2 P hP
    obtain ⟨q', G', M', R, mu', hq', hG'P, hG'm, hRpart, hRprop, hRw, hmu', hcov'⟩ :=
      hML.1.on_partition (θ a) hθ.1.1 hθ.1.2 hQ.1 P Q hQpart hQprop
    set eqv := section5NatFlattenEquiv M'
    set fp : Fin q × Fin q' ≃ Fin (q * q') := finProdFinEquiv
    refine ⟨∑ j, M' j, q * q', G ∩ G', boxFlatten M' R,
      fun J i e => if e = a then mu' (eqv.symm J).1 (eqv.symm J).2 (fp.symm i).2
        else mu (eqv.symm J).1 (fp.symm i).1 e,
      Finset.inter_subset_left.trans hGP, ?_, boxFlatten_partition P Q M' R hQpart hRpart,
      fun J => hRprop _ _, ?_, fun J => ?_, fun J i e he => ?_, fun J x hxR hxG hxD => ?_⟩
    · -- the good set
      rw [Finset.sum_insert ha]
      linarith [card_add_card_le_card_inter_add hGP hG'P]
    · -- the count
      rw [Finset.prod_insert ha, Nat.cast_mul, mul_comm (Qb a (θ a))]
      exact mul_le_mul hq hq' (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hq)
    · -- the widths
      rw [Finset.prod_insert ha, mul_comm, Real.rpow_mul (Nat.cast_nonneg _)]
      exact (Real.rpow_le_rpow (by positivity) (hQw _) hEb.1).trans
        (hRw (eqv.symm J).1 (eqv.symm J).2)
    · -- multilinearity
      dsimp only
      split_ifs with hea
      exacts [hmu' _ _ _, hmu _ _ e ((Finset.mem_insert.mp he).resolve_left hea)]
    · -- the cover
      rw [Finset.mem_inter] at hxG
      rw [Finset.forall_mem_insert] at hxD
      obtain ⟨i1, hi1⟩ := hcov _ x ((hRpart (eqv.symm J).1).cell_subset _ hxR) hxG.1 hxD.2
      obtain ⟨i2, hi2⟩ := hcov' (eqv.symm J).1 (eqv.symm J).2 x hxR hxG.2 (f a x)
        (Finset.mem_image.mpr ⟨x, hxD.1, rfl⟩)
      refine ⟨fp (i1, i2), fun e he => ?_⟩
      simp only [Equiv.symm_apply_apply]
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
  obtain ⟨M, q, G, Q, mu, hGP, hGm, hQpart, hQprop, hq, hQw, hmu, hcov⟩ := hJ
  -- the good part of `H` and a cell `Q j` dense in it
  have hHG : (theta - s) * P.carrier.card ≤ (H ∩ G).card := by
    linarith [card_add_card_le_card_inter_add hHP hGP]
  have hne : (H ∩ G).Nonempty := Finset.card_pos.mp <| Nat.cast_pos.mp <|
    (mul_pos (sub_pos.mpr hs) (Nat.cast_pos.mpr hPne.card_pos)).trans_le hHG
  obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (Q j).carrier) P.carrier hQpart (H ∩ G) id
    (fun x hx => hGP (Finset.mem_inter.mp hx).2) hne hHG
  set D := (H ∩ G).filter fun x => id x ∈ (Q j).carrier
  set T := fun i => H.filter fun x => x ∈ (Q j).carrier ∧ ∀ e ∈ E, f e x = mu j i e x
  -- every point of `D` lies on one of the `q` tuples
  have hsum : (D.card : Real) ≤ ∑ i, ((T i).card : Real) := by
    have hsub : D ⊆ Finset.univ.biUnion T := fun x hx => by
      simp only [D, T, id, Finset.mem_filter, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at hx ⊢
      exact (hcov j x hx.2 hx.1.2 fun e he => hHD e he hx.1.1).imp fun i hi => ⟨hx.1.1, hx.2, hi⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · -- no tuples: the dense cell has no covered points
    refine ⟨Q j, fun _ _ => 0, hQprop j, IsPartition.cell_subset hQpart j, hQw j,
      fun e _ => isMultilinear_constant 0, ?_⟩
    rw [div_mul_eq_mul_div]
    exact (div_nonpos_of_nonpos_of_nonneg (hj.trans (by simpa using hsum))
      ((Nat.cast_nonneg _).trans hq)).trans (Nat.cast_nonneg _)
  · have hqR : (0 : Real) < q := by exact_mod_cast hq0
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty_iff.mpr ⟨⟨0, hq0⟩⟩)
      (show ∑ _i : Fin q, (D.card : Real) / q ≤ ∑ i, ((T i).card : Real) by
        rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_div_cancel₀ _ hqR.ne'])
    refine ⟨Q j, mu j i, hQprop j, IsPartition.cell_subset hQpart j, hQw j, hmu j i, ?_⟩
    calc (theta - s) / Qt * (Q j).carrier.card ≤ (D.card : Real) / Qt := by
          rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hj (hqR.le.trans hq)
      _ ≤ (D.card : Real) / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqR hq
      _ ≤ _ := hi

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
  set E := Finset.univ.filter fun e : Fin k → Bool => e ≠ fun _ => true with hEdef
  have hEmem : ∀ e ∈ E, e ≠ fun _ => true := fun e he => (Finset.mem_filter.mp he).2
  obtain ⟨R, nu, hR, hRP, hRw, hnu, hRc⟩ := (joint_cover_on Dom (section16TranslatedVertex phi x0)
    Qb Eb θv E (fun e he => hML e (hEmem e he)) (fun e _ => hθv e) (fun e _ => hQb e)
    (fun e _ => hEb e) P hP).piece hs H hHP (fun e he => hHD e (hEmem e he)) hHc hPne
  refine ⟨R, fun x => -∑ e ∈ E, (-1 : ZMod N) ^ (k + boolWeight e) * nu e x, hR, hRP, hRw,
    ?_, hRc.trans (Nat.cast_le.mpr (Finset.card_le_card fun x hx => ?_))⟩
  · simpa only [neg_one_mul] using (IsMultilinear.finset_sum E
      (fun e x => (-1 : ZMod N) ^ (k + boolWeight e) * nu e x)
      (fun e he => (hnu e he).const_mul _)).const_mul (-1)
  · simp only [Finset.mem_filter, section16PhiRemainder, ← hEdef] at hx ⊢
    exact ⟨hx.1, hx.2.1, congrArg Neg.neg (Finset.sum_congr rfl fun e he => by rw [hx.2.2 e he])⟩

end LeanProofs.GowersSzemeredi

import GowersSzemeredi.Proofs16SinglePieceSpectrum
import GowersSzemeredi.Proofs16BaseCaseCubicExtraction

/-! Global-to-local inputs for the single-piece lift (Notes L.1 correction,
L.2).

The box-local inputs `LocalMultilinearPieceAt` and `LocalRelationCoverAt`
are false for growing widths: the product property is normalized by the
whole modulus, so it is automatic on short boxes
(`not_localMultilinearPieceAt_of_quadratic`). The right inputs are
global-to-local, like Gowers's Theorem 16.2. A relation with the global
product property, after a `θ`-fraction of base points is deleted, is
covered on every proper box by few multilinear graphs.
* `PolyCoverAt l Qb Eb`: that statement, with controls `Qb γ θ σ` (graph
  count at loss `σ`) and `Eb γ θ σ` (width exponent). It is a named
  hypothesis. `polyCoverAt_one` proves it in dimension one with polynomial
  controls (`section16_product_relation_cubic_cover`).
* `LocalRelationCoverFor`: a local cover provider for one relation on one
  domain. `MultiplyLinearWith.localRelationCoverFor` derives it on the
  good set.
* `MultiplyLinearWith.localPieceFor`: a function cover on a good set gives
  a `LocalPieceFor` provider there. The proof: a dense cell, then
  pigeonhole over the graphs.

Providers are statements about one object on one domain, so they are
satisfiable on good domains. That is the repair of the vacuous box-local
inputs.

`MultiplyLinearWith.localPieceFor` is in `Proofs16GlobalCoverProvidersSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **The global-to-local polynomial cover in dimension `l`.** -/
def PolyCoverAt (l : Nat) (Qb Eb : Real → Real → Real → Real) : Prop :=
  ∀ (N : Nat) [NeZero N] [Fact N.Prime] (gamma theta : Real), 0 < gamma → gamma ≤ 1 →
    0 < theta → theta ≤ 1 →
    ∀ Gamma : Finset (Point N l × ZMod N),
      (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l →
      RelationProductProperty gamma Gamma →
      ∃ J : Finset (Point N l), (1 - theta) * (N : Real) ^ l ≤ J.card ∧
        MultiplyLinearWith (Qb gamma theta) (Eb gamma theta) (restrictRelation Gamma J)

/-- **Dimension one is proved, with polynomial controls.** -/
theorem polyCoverAt_one :
    PolyCoverAt 1 (fun gamma theta _ => ((3 * section16BaseFamilyBound gamma theta : Nat) : Real))
      (fun gamma theta => cubicBaseExponent (section16BaseFamilyBound gamma theta)) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  obtain ⟨J, hJ, hML⟩ := section16_product_relation_cubic_cover hg hg1 ht ht1 Gamma
    (by simpa using hsize) hprod
  exact ⟨J, by simpa using hJ, hML⟩

/-- The width of a cover-derived provider. -/
def coverWidth (Eb : Real → Real) (theta : Real) (L : Nat) : Nat :=
  ⌈(L : Real) ^ max 0 (Eb (theta / 2))⌉₊

theorem coverWidth_mono (Eb : Real → Real) : ∀ t, Monotone (coverWidth Eb t) := by
  intro t L L' hLL'
  unfold coverWidth
  exact Nat.ceil_mono (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hLL')
    (le_max_left _ _))

/-- The good half of a box carries half of any dense subset. -/
theorem dense_inter_good {X : Type*} [DecidableEq X] {P H G : Finset X} (hHP : H ⊆ P) (hGP : G ⊆ P)
    {theta : Real} (hH : theta * P.card ≤ H.card) (hG : (1 - theta / 2) * P.card ≤ G.card) :
    theta / 2 * P.card ≤ (H ∩ G).card := by
  have hunion : (H ∪ G).card ≤ P.card := Finset.card_le_card (Finset.union_subset hHP hGP)
  have h := Finset.card_union_add_card_inter H G
  have hR : ((H ∪ G).card : Real) + (H ∩ G).card = H.card + G.card := by exact_mod_cast h
  have hu : ((H ∪ G).card : Real) ≤ P.card := by exact_mod_cast hunion
  nlinarith

/-- **A relation cover on a good set gives a local cover provider there.** -/
theorem MultiplyLinearWith.localRelationCoverFor {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {Gamma : Finset (Point N k × ZMod N)} {J : Finset (Point N k)}
    (hML : MultiplyLinearWith Qb Eb (restrictRelation Gamma J))
    (hEb : ∀ s, 0 < s → s ≤ 1 → 0 < Eb s) :
    LocalRelationCoverFor (fun theta => theta / 2) (fun theta => Qb (theta / 2))
      (coverWidth Eb) J Gamma := by
  intro theta hθ hθ1 P H hP hHP hHJ hHc
  obtain ⟨M, q, G, Q, mu, hGP, hGc, hQpart, hQprop, hq, hQw, hmu, hcov⟩ :=
    hML (theta / 2) (by positivity) (by linarith) P hP
  have hHG := dense_inter_good hHP hGP hHc hGc
  have hE := hEb (theta / 2) (by positivity) (by linarith)
  rcases (H ∩ G).eq_empty_or_nonempty with h0 | hne
  · -- an empty dense part forces an empty box of width zero
    rw [h0, Finset.card_empty, Nat.cast_zero] at hHG
    have hP0 : P.carrier.card = 0 := Nat.eq_zero_of_not_pos fun hc =>
      by linarith [mul_pos hθ (Nat.cast_pos.mpr hc : (0 : Real) < P.carrier.card)]
    have hw0 : P.width = 0 := Nat.eq_zero_of_not_pos fun hw => (Finset.card_pos.mpr
      (P.carrier_nonempty_of_axis_pos fun i => hw.trans_le (P.width_le_axis_length i))).ne' hP0
    refine ⟨P, ∅, 0, fun _ _ => 0, hP, Finset.Subset.refl _, ?_, Finset.empty_subset _,
      Finset.empty_subset _, by simp [hP0], (Nat.cast_le.2 (Nat.zero_le q)).trans hq,
      fun i => i.elim0, fun h hh => absurd hh (Finset.notMem_empty h)⟩
    simp [hw0, coverWidth, Real.zero_rpow (lt_max_of_lt_right (b := 0) hE).ne']
  · obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (Q j).carrier) _ hQpart (H ∩ G) id
      (fun x hx => hGP (Finset.mem_inter.mp hx).2) hne hHG
    refine ⟨Q j, (H ∩ G).filter fun x => id x ∈ (Q j).carrier, q, mu j, hQprop j,
      IsPartition.cell_subset hQpart j, Nat.ceil_le.mpr (by rw [max_eq_right hE.le]; exact hQw j),
      (Finset.filter_subset _ _).trans Finset.inter_subset_left,
      fun x hx => (Finset.mem_filter.mp hx).2, hj, hq, hmu j, fun h hh y hy => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_inter] at hh
    exact hcov j h hh.2 hh.1.2 y (by simpa [restrictRelation] using And.intro hy (hHJ hh.1.1))

/-- The fibre of a translated coordinate selection has `N^(n-l)` points. -/
theorem card_fibre_selected {N n l : Nat} [NeZero N] (f : Fin l ↪ Fin n) (c y : Point N l) :
    ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) = y).card =
      N ^ (n - l) := by
  let e : {z : Point N n // (fun i => z (f i) + c i) = y} ≃
      ({j : Fin n // j ∉ Set.range f} → ZMod N) :=
    { toFun := fun z j => z.1 j.1
      invFun := fun g => ⟨Function.extend f (y - c) fun j =>
          if h : j ∈ Set.range f then 0 else g ⟨j, h⟩,
        funext fun i => by simp [f.injective.extend_apply]⟩
      left_inv := fun z => Subtype.ext <| funext fun j => by
        by_cases hj : j ∈ Set.range f
        · obtain ⟨i, rfl⟩ := hj
          simp [f.injective.extend_apply, ← z.2]
        · simp only [Function.extend_apply' _ _ _ (Set.mem_range.not.mp hj), dif_neg hj]
      right_inv := fun g => funext fun j => by
        simp only [Function.extend_apply' _ _ _ (Set.mem_range.not.mp j.2), dif_neg j.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective f.injective,
    Fintype.card_fin]

/-- **Preimages of a translated coordinate selection.** -/
theorem card_filter_selected_mem {N n l : Nat} [NeZero N] (f : Fin l ↪ Fin n) (c : Point N l)
    (S : Finset (Point N l)) :
    ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) ∈ S).card =
      S.card * N ^ (n - l) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun z : Point N n => fun i => z (f i) + c i)
    (s := (Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) ∈ S)
    (t := S) (fun z hz => (Finset.mem_filter.mp hz).2)]
  rw [Finset.sum_congr rfl fun y hy => ?_, Finset.sum_const, smul_eq_mul]
  rw [← card_fibre_selected f c y]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨h ▸ hy, h⟩

/-- The complement of a dense set has a sparse preimage. -/
theorem card_filter_selected_not_mem_le {N n l : Nat} [NeZero N] (f : Fin l ↪ Fin n)
    (c : Point N l) (S : Finset (Point N l)) {theta : Real}
    (hS : (1 - theta) * (N : Real) ^ l ≤ S.card) (hln : l ≤ n) :
    (((Finset.univ : Finset (Point N n)).filter fun z =>
      (fun i => z (f i) + c i) ∉ S).card : Real) ≤ theta * (N : Real) ^ n := by
  have hcompl := card_filter_selected_mem f c (Finset.univ \ S)
  have heq : ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) ∉ S) =
      (Finset.univ.filter fun z => (fun i => z (f i) + c i) ∈ Finset.univ \ S) := by
    ext z; simp
  have hcard : Fintype.card (Point N l) = N ^ l := by simp [Point, ZMod.card]
  have hSle : S.card ≤ N ^ l := by
    have := Finset.card_le_univ S
    rwa [hcard] at this
  rw [heq, hcompl, Finset.card_univ_sdiff, hcard]
  push_cast [hSle]
  have hpow : (N : Real) ^ n = (N : Real) ^ l * (N : Real) ^ (n - l) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  have hN : (0 : Real) ≤ (N : Real) ^ (n - l) := by positivity
  nlinarith

end LeanProofs.GowersSzemeredi

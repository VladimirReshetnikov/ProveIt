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
inputs. -/
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
  rcases (H ∩ G).eq_empty_or_nonempty with h0 | hne
  · -- an empty dense part forces an empty box of width zero
    rw [h0, Finset.card_empty, Nat.cast_zero] at hHG
    have hP0 : (P.carrier.card : Real) = 0 := by
      have hnn := Nat.cast_nonneg (α := Real) P.carrier.card
      by_contra hne0
      have hpos : (0 : Real) < P.carrier.card := lt_of_le_of_ne hnn (Ne.symm hne0)
      have : (0 : Real) < theta / 2 * P.carrier.card := by positivity
      linarith
    have hPe : P.carrier = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hP0)
    have hw0 : P.width = 0 := by
      by_contra hw
      have hne' := P.carrier_nonempty_of_axis_pos fun i =>
        lt_of_lt_of_le (Nat.pos_of_ne_zero hw) (P.width_le_axis_length i)
      rw [hPe] at hne'
      exact Finset.not_nonempty_empty hne'
    have hQ0 : (0 : Real) ≤ Qb (theta / 2) := le_trans (Nat.cast_nonneg _) hq
    refine ⟨P, ∅, 0, fun _ _ => 0, hP, Finset.Subset.refl _, ?_, Finset.empty_subset _,
      Finset.empty_subset _, ?_, by simpa using hQ0, fun i => i.elim0,
      fun h hh => absurd hh (Finset.notMem_empty h)⟩
    · rw [hw0]
      unfold coverWidth
      rw [Nat.cast_zero, max_eq_right (hEb _ (by positivity) (by linarith)).le,
        Real.zero_rpow (hEb _ (by positivity) (by linarith)).ne']
      simp
    · rw [hP0, mul_zero, Finset.card_empty, Nat.cast_zero]
  · obtain ⟨j, hj⟩ := exists_dense_cell (fun j => (Q j).carrier) _ hQpart (H ∩ G) id
      (fun x hx => hGP (Finset.mem_inter.mp hx).2) hne hHG
    refine ⟨Q j, (H ∩ G).filter fun x => id x ∈ (Q j).carrier, q, mu j, hQprop j,
      IsPartition.cell_subset hQpart j, ?_, ?_, ?_, hj, hq, hmu j, ?_⟩
    · unfold coverWidth
      rw [max_eq_right (hEb _ (by positivity) (by linarith)).le]
      exact Nat.ceil_le.mpr (hQw j)
    · intro x hx; exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro h hh y hy
      obtain ⟨hhHG, hhQ⟩ := Finset.mem_filter.mp hh
      obtain ⟨hhH, hhG⟩ := Finset.mem_inter.mp hhHG
      refine hcov j h hhQ hhG y ?_
      simp only [restrictRelation, Finset.mem_filter]
      exact ⟨hy, hHJ hhH⟩

/-- **A function cover on a good set gives a piece provider there.** -/
theorem MultiplyLinearWith.localPieceFor {N k : Nat} [NeZero N]
    {Qb Eb : Real → Real} {B J : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearWith Qb Eb (restrictRelation (partialGraph B phi) J))
    (hQb : ∀ s, 0 < s → s ≤ 1 → 1 ≤ Qb s) (hEb : ∀ s, 0 < s → s ≤ 1 → 0 < Eb s) :
    LocalPieceFor (fun theta => theta / 2 / Qb (theta / 2)) (coverWidth Eb) (B ∩ J) phi := by
  intro theta hθ hθ1 P H hP hHP hHD hHc
  have hcov := hML.localRelationCoverFor hEb
  obtain ⟨R, G, q, mu, hR, hRP, hRw, hGH, hGR, hGc, hq, hmu, hGcov⟩ :=
    hcov theta hθ hθ1 P H hP hHP (fun x hx => (Finset.mem_inter.mp (hHD hx)).2) hHc
  have hQpos : (0 : Real) < Qb (theta / 2) :=
    lt_of_lt_of_le one_pos (hQb _ (by positivity) (by linarith))
  -- every point of `G` lies on one of the `q` graphs
  have hcov' : ∀ h ∈ G, ∃ i, phi h = mu i h := fun h hh =>
    hGcov h hh (phi h) (Finset.mem_image.mpr ⟨h, (Finset.mem_inter.mp (hHD (hGH hh))).1, rfl⟩)
  have hsum : (G.card : Real) ≤ ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
    have hsub : G ⊆ Finset.univ.biUnion fun i => G.filter fun h => phi h = mu i h := by
      intro h hh
      obtain ⟨i, hi⟩ := hcov' h hh
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hh, hi⟩⟩
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have hG0 : (G.card : Real) ≤ 0 := by simpa using hsum
    refine ⟨R, fun _ => 0, hR, hRP, hRw, ⟨fun _ => 0, fun x => by simp⟩, ?_⟩
    have : theta / 2 * R.carrier.card ≤ 0 := hGc.trans hG0
    calc theta / 2 / Qb (theta / 2) * R.carrier.card =
        (theta / 2 * R.carrier.card) / Qb (theta / 2) := by ring
      _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hQpos.le
      _ ≤ _ := Nat.cast_nonneg _
  · have hqR : (0 : Real) < q := by exact_mod_cast hq0
    have hne : (Finset.univ : Finset (Fin q)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hq0⟩⟩
    have hle : ∑ _i : Fin q, (G.card : Real) / q ≤
        ∑ i, ((G.filter fun h => phi h = mu i h).card : Real) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ hqR.ne']
      exact hsum
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne hle
    refine ⟨R, mu i, hR, hRP, hRw, hmu i, ?_⟩
    have hsub : (G.filter fun h => phi h = mu i h) ⊆
        H.filter fun x => x ∈ R.carrier ∧ phi x = mu i x := fun h hh => by
      obtain ⟨hhG, he⟩ := Finset.mem_filter.mp hh
      exact Finset.mem_filter.mpr ⟨hGH hhG, hGR hhG, he⟩
    calc theta / 2 / Qb (theta / 2) * R.carrier.card ≤ (G.card : Real) / Qb (theta / 2) := by
          rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right hGc hQpos.le
      _ ≤ (G.card : Real) / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqR hq
      _ ≤ _ := hi.trans (by exact_mod_cast Finset.card_le_card hsub)


/-- The fibre of a translated coordinate selection has `N^(n-l)` points. -/
theorem card_fibre_selected {N n l : Nat} [NeZero N] (f : Fin l ↪ Fin n) (c y : Point N l) :
    ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) = y).card =
      N ^ (n - l) := by
  classical
  let e : {z : Point N n // (fun i => z (f i) + c i) = y} ≃
      ({j : Fin n // j ∉ Set.range f} → ZMod N) :=
    { toFun := fun z j => z.1 j.1
      invFun := fun g => ⟨fun j => if h : ∃ i, f i = j then y h.choose - c h.choose
          else g ⟨j, fun ⟨i, hi⟩ => h ⟨i, hi⟩⟩, by
        funext i
        have h : ∃ i', f i' = f i := ⟨i, rfl⟩
        simp only [dif_pos h]
        have hi : h.choose = i := f.injective h.choose_spec
        rw [hi]
        ring⟩
      left_inv := by
        rintro ⟨z, hz⟩
        apply Subtype.ext
        funext j
        show (if h : ∃ i, f i = j then y h.choose - c h.choose else z j) = z j
        split_ifs with h
        · have h1 : z (f h.choose) + c h.choose = y h.choose := congrFun hz h.choose
          rw [← h1, h.choose_spec]
          ring
        · rfl
      right_inv := by
        intro g
        funext j
        simp only
        rw [dif_neg (fun ⟨i, hi⟩ => j.2 ⟨i, hi⟩)] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, ZMod.card]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective f.injective,
    Fintype.card_fin]

/-- **Preimages of a translated coordinate selection.** -/
theorem card_filter_selected_mem {N n l : Nat} [NeZero N] (f : Fin l ↪ Fin n) (c : Point N l)
    (S : Finset (Point N l)) :
    ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) ∈ S).card =
      S.card * N ^ (n - l) := by
  classical
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
  classical
  have hcompl := card_filter_selected_mem f c (Finset.univ \ S)
  have heq : ((Finset.univ : Finset (Point N n)).filter fun z => (fun i => z (f i) + c i) ∉ S) =
      (Finset.univ.filter fun z => (fun i => z (f i) + c i) ∈ Finset.univ \ S) := by
    ext z; simp
  have hcard : Fintype.card (Point N l) = N ^ l := by simp [Point, ZMod.card]
  have hSle : S.card ≤ N ^ l := by
    have := Finset.card_le_univ S
    rwa [hcard] at this
  rw [heq, hcompl, Finset.card_univ_diff, hcard]
  push_cast [hSle]
  have hpow : (N : Real) ^ n = (N : Real) ^ l * (N : Real) ^ (n - l) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  have hN : (0 : Real) ≤ (N : Real) ^ (n - l) := by positivity
  nlinarith

end LeanProofs.GowersSzemeredi

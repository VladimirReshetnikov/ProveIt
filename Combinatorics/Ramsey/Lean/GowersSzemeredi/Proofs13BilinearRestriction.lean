import GowersSzemeredi.Proofs13QuadraticRecurrence

/-!
# The final bilinear restriction in Section 13

The proof of Corollary 13.10 restricts the bilinear set produced by Lemma 13.9
to one cell of a square-grid partition of
`S × (U + y)`.  The live statement assumes only `IsStage139Data`.  That
predicate neither says that `J.D` is supported on this product nor supplies
the square-grid partition asserted in the paper.

This module isolates those two missing facts.  The support statement follows
from the full Stage 13.7--13.9 chain.  The remaining `Corollary1310Grid`
predicate is precisely the finite partition used by the final averaging
argument.  With these hypotheses made explicit, the conclusion (including
the paper's weakened `2^-137` density) follows without any further analytic
input.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The square-grid decomposition invoked in the proof of Corollary 13.10.
Every cell is a product of proper progressions having the same nonzero common
difference and the same length, with the required `sqrt (|U|) - 1` lower
bound. -/
def Corollary1310Grid {N : Nat} (G : Stage137Data N)
    (J : Stage139Data N) : Prop :=
  ∃ q : Nat, ∃ V W : Fin q → ModAP N,
    0 < q ∧
    IsPartition (fun i ↦ (V i).carrier.product (W i).carrier)
      (G.S.carrier.product (translateFinset J.U.carrier G.y)) ∧
    ∀ i,
      (V i).step != 0 ∧ (V i).step = (W i).step ∧
      (V i).IsProper ∧ (W i).IsProper ∧
      (V i).length = (W i).length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ (V i).length

/-- The two facts absent from the live `IsStage139Data` antecedent: support of
the bilinear set on the intended product and the square-grid decomposition of
that product. -/
def Corollary1310Compatibility {N : Nat} (G : Stage137Data N)
    (J : Stage139Data N) : Prop :=
  J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y) ∧
    Corollary1310Grid G J

/-- Corollary 13.10 with the support and progression-grid compatibility used
by its printed proof stated explicitly. -/
def corollary_13_10_with_compatibility : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (E : Stage135Data N)
      (G : Stage137Data N) (H : Stage138Data N) (J : Stage139Data N),
    IsStage139Data S E G H J → Corollary1310Compatibility G J →
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤
        E'.card ∧
      BilinearOn E' S.phi

private lemma cor1310_modAP_card_le_length {N : Nat} (P : ModAP N) :
    P.carrier.card ≤ P.length := by
  classical
  unfold ModAP.carrier
  calc
    (Finset.univ.image
        (fun i : Fin P.length ↦ P.start + (i : Nat) * P.step)).card ≤
        (Finset.univ : Finset (Fin P.length)).card := Finset.card_image_le
    _ = P.length := by simp

private lemma cor1310_translate_card {N : Nat} (A : Finset (ZMod N))
    (y : ZMod N) :
    (translateFinset A y).card = A.card := by
  classical
  unfold translateFinset
  exact Finset.card_image_of_injective A (add_right_injective y)

private lemma cor1310_inter_partition {X : Type*} [DecidableEq X]
    {q : Nat} (P : Fin q → Finset X) (T D : Finset X)
    (hP : IsPartition P T) (hD : D ⊆ T) :
    IsPartition (fun i ↦ D ∩ P i) D := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (hP.1 x).mp (hD hx)
      exact ⟨i, Finset.mem_inter.mpr ⟨hx, hi⟩⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_inter.mp hi).1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    exact (Finset.disjoint_left.mp (hP.2 i j hij))
      (Finset.mem_inter.mp hxi).2 (Finset.mem_inter.mp hxj).2

private lemma cor1310_bilinear_mono {N : Nat}
    {A B : Finset (Pair N)} {phi : Pair N → ZMod N}
    (hAB : A ⊆ B) (hB : BilinearOn B phi) : BilinearOn A phi := by
  obtain ⟨mu, hmu, hagree⟩ := hB
  exact ⟨mu, hmu, fun z hz ↦ hagree z (hAB hz)⟩

/-- The support relation omitted from `IsStage139Data` is recovered from the
actual Stage 13.7 and Stage 13.8 conclusions. -/
theorem stage139_support_of_stage137_stage138 {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (J : Stage139Data N)
    (h137 : IsStage137Data S D E F G)
    (h138 : IsStage138Data S D E G H)
    (h139 : IsStage139Data S E G H J) :
    J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y) := by
  classical
  rcases h137 with
    ⟨_hSstep, _hSproper, _hSsub, _hSlower, hBsupport,
      _hBlargeOne, _hBlargeTwo, _hlinear⟩
  rcases h138 with
    ⟨_hrows, _hJsub, _hfreiman, hCdef, _hClarge⟩
  rcases h139 with
    ⟨_hUstep, _hUproper, _hUsub, _hstepMultiple, _hUlower,
      hDdef, _hDlarge, _hbilinear⟩
  intro z hz
  rw [hDdef] at hz
  have hzD := Finset.mem_filter.mp hz
  have hzC : z ∈ H.C := hzD.1
  rw [hCdef] at hzC
  have hzB : z ∈ G.B := (Finset.mem_filter.mp hzC).1
  have hzProduct := Finset.mem_product.mp (hBsupport hzB)
  apply Finset.mem_product.mpr
  refine ⟨hzProduct.1, ?_⟩
  unfold translateFinset
  rw [Finset.mem_image]
  refine ⟨z.2 - G.y, (Finset.mem_inter.mp hzD.2).1, ?_⟩
  abel

/-- The finite averaging argument proving the faithfully repaired Corollary
13.10. -/
theorem corollary_13_10_with_compatibility_holds :
    corollary_13_10_with_compatibility := by
  classical
  intro N _inst S E G H J h139 hcompat
  rcases hcompat with ⟨hDsupport, q, V, W, hq, hpartition, hcell⟩
  rcases h139 with
    ⟨_hUstep, hUproper, _hUsub, _hstepMultiple, _hUlower,
      _hDdef, hDlarge, hDbilinear⟩
  let Box : Fin q → Finset (Pair N) :=
    fun i ↦ (V i).carrier.product (W i).carrier
  let Restricted : Fin q → Finset (Pair N) := fun i ↦ J.D ∩ Box i
  have hrestrictedPartition : IsPartition Restricted J.D := by
    exact cor1310_inter_partition Box
      (G.S.carrier.product (translateFinset J.U.carrier G.y)) J.D
      hpartition hDsupport
  have hrestrictedCardsNat : ∑ i, (Restricted i).card = J.D.card :=
    IsPartition.sum_card hrestrictedPartition
  have hrestrictedCards :
      ∑ i, ((Restricted i).card : Real) = (J.D.card : Real) := by
    exact_mod_cast hrestrictedCardsNat
  have hboxCard (i : Fin q) :
      (Box i).card = (V i).length * (W i).length := by
    rcases hcell i with
      ⟨_hiStep, _hiSteps, hViProper, hWiProper, _hiLength, _hiLower⟩
    calc
      (Box i).card = (V i).carrier.card * (W i).carrier.card := by
        simpa only [Box, Finset.product_eq_sprod] using
          Finset.card_product (V i).carrier (W i).carrier
      _ = (V i).length * (W i).length :=
        congrArg₂ (fun a b : Nat ↦ a * b) hViProper hWiProper
  have hboxCardsNat :
      ∑ i, (V i).length * (W i).length =
        (G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card := by
    calc
      ∑ i, (V i).length * (W i).length = ∑ i, (Box i).card := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (hboxCard i).symm
      _ = (G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card :=
        IsPartition.sum_card hpartition
  have hboxCards :
      ∑ i, ((V i).length : Real) * (W i).length =
        ((G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card : Real) := by
    exact_mod_cast hboxCardsNat
  have hambientNat :
      (G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card ≤
        G.S.length * J.U.length := by
    calc
      (G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card =
          G.S.carrier.card *
            (translateFinset J.U.carrier G.y).card :=
        Finset.card_product G.S.carrier
          (translateFinset J.U.carrier G.y)
      _ = G.S.carrier.card * J.U.carrier.card := by
        rw [cor1310_translate_card]
      _ ≤ G.S.length * J.U.length :=
        Nat.mul_le_mul (cor1310_modAP_card_le_length G.S)
          (le_of_eq hUproper)
  have hambient :
      ((G.S.carrier.product
          (translateFinset J.U.carrier G.y)).card : Real) ≤
        (G.S.length : Real) * J.U.length := by
    exact_mod_cast hambientNat
  let c : Real := (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hpow :
      (2 : Real) ^ (-(135 : Int)) =
        4 * (2 : Real) ^ (-(137 : Int)) := by
    calc
      (2 : Real) ^ (-(135 : Int)) =
          (2 : Real) ^ ((2 : Int) + (-(137 : Int))) := by norm_num
      _ = (2 : Real) ^ (2 : Int) * (2 : Real) ^ (-(137 : Int)) := by
        rw [zpow_add₀ (by norm_num : (2 : Real) ≠ 0)]
      _ = 4 * (2 : Real) ^ (-(137 : Int)) := by norm_num
  have hcoefficient :
      c ≤ (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704 := by
    rw [hpow]
    dsimp only [c]
    have hnonneg :
        0 ≤ (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 := by positivity
    nlinarith
  have hweighted :
      ∑ i, c * (((V i).length : Real) * (W i).length) ≤
        ∑ i, ((Restricted i).card : Real) := by
    calc
      ∑ i, c * (((V i).length : Real) * (W i).length) =
          c * ∑ i, (((V i).length : Real) * (W i).length) := by
            rw [Finset.mul_sum]
      _ = c *
          ((G.S.carrier.product
            (translateFinset J.U.carrier G.y)).card : Real) := by
            rw [hboxCards]
      _ ≤ c * ((G.S.length : Real) * J.U.length) :=
        mul_le_mul_of_nonneg_left hambient hc
      _ ≤ ((2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704) *
          ((G.S.length : Real) * J.U.length) := by
            exact mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704 *
          G.S.length * J.U.length := by ring
      _ ≤ (J.D.card : Real) := hDlarge
      _ = ∑ i, ((Restricted i).card : Real) := hrestrictedCards.symm
  have huniv : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨i, _hi, hiDense⟩ :=
    Finset.exists_le_of_sum_le huniv hweighted
  rcases hcell i with
    ⟨hiStep, hiSteps, hViProper, hWiProper, hiLength, hiLower⟩
  refine ⟨V i, W i, Restricted i, hiStep, hiSteps, hViProper, hWiProper,
    hiLength, hiLower, ?_, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_inter.mp hz).2
  · simpa only [c, mul_assoc] using hiDense
  · apply cor1310_bilinear_mono (B := J.D) _ hDbilinear
    intro z hz
    exact (Finset.mem_inter.mp hz).1

/-- A faithful stage-chain wrapper: Stages 13.7 and 13.8 provide the missing
support statement, while `Corollary1310Grid` supplies exactly the final
progression decomposition that is absent from all live stage predicates. -/
theorem corollary_13_10_of_stage_chain_and_grid {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N) (H : Stage138Data N)
    (J : Stage139Data N)
    (h137 : IsStage137Data S D E F G)
    (h138 : IsStage138Data S D E G H)
    (h139 : IsStage139Data S E G H J)
    (hgrid : Corollary1310Grid G J) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤
        E'.card ∧
      BilinearOn E' S.phi := by
  exact corollary_13_10_with_compatibility_holds N S E G H J h139
    ⟨stage139_support_of_stage137_stage138 S D E F G H J h137 h138 h139,
      hgrid⟩

end LeanProofs.GowersSzemeredi

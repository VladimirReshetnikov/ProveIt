import IPRADerivations.Analysis.Integration.Quadrature.SquareSubstitution.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSum
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannSplit

/-!
# Exact internal cut points for an original quadratic quadrature

The target interval has tuple (c*a^2,c*C*(2a+C),d*E^2).
Its uniform mesh count W*N^2 makes every mapped original node an exact
cut point of that mesh. The cut is a polynomial PR program; no floor,
search, choice or approximation is used. Positive width is explicit.
Zero width has separate exact degeneracy identities.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquarePartition

open_ipra
open GaussianCompactRiemannName (grid value fraction_congr)
open GaussianRationalQuadratureSquareCells (node cellWidth)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def lowerNumerator (c a : PTm n) : PTm n := c*a*a
def widthNumerator (c a C : PTm n) : PTm n := c*C*(two*a+C)
def intervalDenominator (d E : PTm n) : PTm n := d*E*E
def fineCount (N c a C : PTm n) : PTm n := widthNumerator c a C*N*N
def cellCap (c a C : PTm n) : PTm n := c*C*(two*a+two*C)
def cutValue (i N c a C : PTm n) : PTm n := c*C*i*(two*a*N+C*i)
def increment (i N c a C : PTm n) : PTm n := c*C*(two*a*N+C*(two*i+one))
def cutData (N c a C : PTm n) : PTm n := pairT N (pairT c (pairT a C))
def cutTerm (i x : PTm n) : PTm n := cutValue i (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def cutF : PR 2 := PTm.toPR (cutTerm (var 0) (var 1))
def cutGap (i N c a C : PTm n) : PTm n := monus (ap2 cutF (succ i) (cutData N c a C)) (ap2 cutF i (cutData N c a C))
def source (c d a C E N : PTm n) : Fm PTm n := le one c ⋏ (le one a ⋏ (le one C ⋏ GaussianRationalQuadratureSquareCells.source d E N))

ipra_subst lowerNumerator
ipra_subst widthNumerator
ipra_subst intervalDenominator
ipra_subst fineCount
ipra_subst cellCap
ipra_subst cutValue
ipra_subst increment
ipra_subst cutData
ipra_subst cutTerm
ipra_subst cutGap
ipra_subst source

theorem cut_at (i N c a C : PTm n) : Γ ⊢[PRAAx] ap2 cutF i (cutData N c a C) ≐ cutValue i N c a C := by
  have program : Γ ⊢[PRAAx] ap2 cutF i (cutData N c a C) ≐ cutTerm i (cutData N c a C) := by
    simpa [cutF,ap2] using toPR_eq (Γ := Γ) (cutTerm (var 0) (var 1) : PTm 2) ![i,cutData N c a C]
  have ht := snd_pair (Γ := Γ) N (pairT c (pairT a C))
  have hu := (congrSnd ht).eqTrans (snd_pair c (pairT a C))
  have hn := fst_pair (Γ := Γ) N (pairT c (pairT a C))
  have hc := (congrFst ht).eqTrans (fst_pair c (pairT a C))
  have ha := (congrFst hu).eqTrans (fst_pair a C)
  have hC := (congrSnd hu).eqTrans (snd_pair a C)
  exact program.eqTrans (congrMul (congrMul (congrMul hc hC) (.eqRefl i))
    (congrAdd (congrMul (congrMul (.eqRefl two) ha) hn) (congrMul hC (.eqRefl i))))

theorem cut_increment (i N c a C : PTm n) : Γ ⊢[PRAAx]
    cutValue (succ i) N c a C ≐ cutValue i N c a C+increment i N c a C := by
  unfold cutValue increment
  ipra_ring

theorem increasing (N c a C : PTm n) : Γ ⊢[PRAAx] GaussianPartitionedFiniteSum.increasing cutF (cutData N c a C) := by
  refine .allI ?_
  have raw : Γ.map Fm.shift ⊢[PRAAx] le (cutValue (var 0) (Syn.shift N) (Syn.shift c) (Syn.shift a) (Syn.shift C))
      (cutValue (succ (var 0)) (Syn.shift N) (Syn.shift c) (Syn.shift a) (Syn.shift C)) :=
    le_congr (.eqRefl _) (cut_increment _ _ _ _ _).eqSymm (le_add_right _ _)
  simpa only [GaussianPartitionedFiniteSum.increasing,subst_cutData,Syn.shift] using
    le_congr (cut_at (var 0) (Syn.shift N) (Syn.shift c) (Syn.shift a) (Syn.shift C)).eqSymm
      (cut_at (succ (var 0)) (Syn.shift N) (Syn.shift c) (Syn.shift a) (Syn.shift C)).eqSymm raw

theorem cut_zero (N c a C : PTm n) : Γ ⊢[PRAAx] ap2 cutF zero (cutData N c a C) ≐ zero :=
  (cut_at zero N c a C).eqTrans (by unfold cutValue; ipra_ring)

theorem cut_last (N c a C : PTm n) : Γ ⊢[PRAAx] ap2 cutF N (cutData N c a C) ≐ fineCount N c a C :=
  (cut_at N N c a C).eqTrans (by unfold cutValue fineCount widthNumerator; ipra_ring)

theorem cut_gap (i N c a C : PTm n) : Γ ⊢[PRAAx] cutGap i N c a C ≐ increment i N c a C :=
  (congrMonus (cut_at (succ i) N c a C) (cut_at i N c a C)).eqTrans
    ((congrMonus (cut_increment i N c a C) (.eqRefl _)).eqTrans (add_monus' _ _))

theorem cut_gap_bound (i N c a C : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] le (cutGap i N c a C) (cellCap c a C*N) := by
  have first : Γ ⊢[PRAAx] le (two*i+one) (two*succ i) := le_of_eq_add (d := one) (by ipra_ring)
  have second : Γ ⊢[PRAAx] le (two*succ i) (two*N) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two hi)
  have twice := le_trans first second
  have upper : Γ ⊢[PRAAx] le (increment i N c a C) (cellCap c a C*N) := by
    unfold increment cellCap
    ipra_le (𝔞(c*C*C))*sl twice
  exact le_congr (cut_gap i N c a C).eqSymm (.eqRefl _) upper

theorem width_positive (c d a C E N : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx] le one (widthNumerator c a C) :=
  positive_product _ _ (positive_product _ _ hs.andE₁ hs.andE₂.andE₂.andE₁)
    (le_trans hs.andE₂.andE₂.andE₁ (le_add_left _ _))

theorem fine_count_positive (c d a C E N : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx] le one (fineCount N c a C) :=
  positive_product _ _ (positive_product _ _ (width_positive c d a C E N hs) hs.andE₂.andE₂.andE₂.andE₂.andE₂) hs.andE₂.andE₂.andE₂.andE₂.andE₂

theorem point_at_cut (i N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    value (grid (ap2 cutF i (cutData N c a C)) (fineCount N c a C) (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E)) ≐
      node i N c d a C E := by
  have hW := width_positive c d a C E N hs
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  have numEq : Γ ⊢[PRAAx] lowerNumerator c a*fineCount N c a C+widthNumerator c a C*ap2 cutF i (cutData N c a C) ≐
      widthNumerator c a C*(c*GaussianRationalQuadratureSquareCells.nodeNumerator i N a C*GaussianRationalQuadratureSquareCells.nodeNumerator i N a C) :=
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (cut_at i N c a C))).eqTrans (by
      unfold lowerNumerator fineCount widthNumerator cutValue GaussianRationalQuadratureSquareCells.nodeNumerator
      ipra_ring)
  have denEq : Γ ⊢[PRAAx] intervalDenominator d E*fineCount N c a C ≐
      widthNumerator c a C*GaussianRationalQuadratureSquareCells.denominator d E N := by
    unfold intervalDenominator fineCount GaussianRationalQuadratureSquareCells.denominator
    ipra_ring
  exact (GaussianCompactRiemannName.value_grid _ _ _ _ _).eqTrans
    ((fraction_congr _ _ _ _ numEq denEq).eqTrans (GaussianCompactRiemannSplit.fraction_cancel _ _ _ hW hD))

theorem fine_weight (N c d a C E : PTm n) (hs : Γ ⊢[PRAAx] source c d a C E N) : Γ ⊢[PRAAx]
    GaussianRationalRiemannRefinement.weight (widthNumerator c a C) (intervalDenominator d E) (fineCount N c a C) ≐
      fraction one (GaussianRationalQuadratureSquareCells.denominator d E N) := by
  have hW := width_positive c d a C E N hs
  have hD := GaussianRationalQuadratureSquareCells.denominator_positive d E N hs.andE₂.andE₂.andE₂
  exact (fraction_congr _ _ _ _ (by ipra_ring) (by unfold intervalDenominator fineCount GaussianRationalQuadratureSquareCells.denominator; ipra_ring)).eqTrans
    (GaussianCompactRiemannSplit.fraction_cancel _ _ _ hW hD)

theorem cut_gap_cell_width (i N c d a C E : PTm n) : Γ ⊢[PRAAx]
    fraction (cutGap i N c a C) (GaussianRationalQuadratureSquareCells.denominator d E N) ≐ cellWidth i N c d a C E :=
  fraction_congr _ _ _ _ ((cut_gap i N c a C).eqTrans (by unfold increment GaussianRationalQuadratureSquareCells.nodeNumerator; ipra_ring)) (.eqRefl _)

theorem zero_width (c a : PTm n) : Γ ⊢[PRAAx] widthNumerator c a zero ≐ zero := by unfold widthNumerator; ipra_ring

theorem zero_width_count (N c a : PTm n) : Γ ⊢[PRAAx] fineCount N c a zero ≐ zero := by unfold fineCount widthNumerator; ipra_ring

theorem actual_quadratic_original_mesh_alignment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 1) ⟶
      value (grid (ap2 cutF (var 0) (cutData (var 1) (var 2) (var 4) (var 5))) (fineCount (var 1) (var 2) (var 4) (var 5))
        (lowerNumerator (var 2) (var 4)) (widthNumerator (var 2) (var 4) (var 5)) (intervalDenominator (var 3) (var 6))) ≐
        node (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (point_at_cut _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalQuadratureSquarePartition

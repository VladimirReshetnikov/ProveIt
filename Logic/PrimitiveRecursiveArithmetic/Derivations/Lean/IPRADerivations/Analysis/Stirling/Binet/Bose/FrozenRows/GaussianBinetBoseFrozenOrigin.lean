import IPRADerivations.Analysis.Stirling.Binet.Bose.FrozenRows.GaussianBinetBoseFrozenMatrix
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecaySharedTail
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff

/-!
# Exact zero-origin readback of the frozen Bose matrix

At zero origin the translated physical tags are the same tags used by
an individual frozen geometric row. Bringing the mesh weight inside
the outer sum gives the literal prefix used by the tail bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenOrigin

open_ipra
open GaussianBinetBoseFrozenMatrix (matrix matrix_at subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetBosePrefixTranspose (data)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianBinetSecondDecayGrid (rowBody rowData row_at value)
open GaussianBinetSecondDecayPointwise (row frozenPiNumerator subst_row)
open GaussianCompactRiemannName (grid)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini (column columnBody column_entry columnSumBody column_sum_at columnFirst)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "frozenBody" => GaussianBinetSecondDecayFrozenTail.body
local notation "frozenData" => GaussianBinetSecondDecaySharedTail.data

private theorem row_time_congr (q X Y D sign a a' b b' H J : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    row q X Y D sign a b H J ≐ row q X Y D sign a' b' H J := by
  let s (z : PTm n) := Syn.shift z
  have first : Γ ⊢[PRAAx] row q X Y D sign a b H J ≐ row q X Y D sign a' b H J := by
    simpa only [s,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (row (s q) (s X) (s Y) (s D) (s sign) (var 0) (s b) (s H) (s J)) ha
  have second : Γ ⊢[PRAAx] row q X Y D sign a' b H J ≐ row q X Y D sign a' b' H J := by
    simpa only [s,subst_row,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (row (s q) (s X) (s Y) (s D) (s sign) (s a') (var 0) (s H) (s J)) hb
  exact first.eqTrans second

theorem column_at (j q k M T X Y D sign : PTm n) : Γ ⊢[PRAAx]
    qmul (weight T one M) (column matrix j M (data q M k X Y D sign zero T one)) ≐
      value q M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign := by
  let x := data q M k X Y D sign zero T one
  let y := rowData q M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign
  have rows : Γ ⊢[PRAAx] termsEqual (columnBody matrix) rowBody M (pairT j x) y := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s M) :: Γ.map Fm.shift
    let d := data (s q) (s M) (s k) (s X) (s Y) (s D) (s sign) zero (s T) one
    let H := frozenPiNumerator (succ (s j)) (s k)
    let J := piDenominator (s k)
    let t := grid i (s M) (one+zero) (s T) one
    have cell := column_entry (Γ := Δ) matrix i (s j) d
    rw [matrix_at] at cell
    have frozen := cell.eqTrans (GaussianBinetBoseFrozenMatrix.cell_at i (s j) (s q) (s k) (s M) (s X) (s Y) (s D) (s sign) zero (s T) one)
    have tag := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Δ) i (s M) zero (s T) one
    have coord := row_time_congr (s q) (s X) (s Y) (s D) (s sign)
      (tagNumerator t) (s T*i) (sndT t) (s M) H J (tag.andE₁.eqTrans (by ipra_ring)) (tag.andE₂.eqTrans (one_mul _))
    simpa only [termsEqual,x,y,s,i,Δ,d,H,J,Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,
      GaussianBinetSecondDecayGrid.subst_rowData,subst_frozenPiNumerator,subst_piDenominator,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one] using
      frozen.eqTrans (coord.eqTrans (row_at i (s q) (s M) (s T) H J (s X) (s Y) (s D) (s sign)).eqSymm)
  exact qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows)

private theorem coefficient_at (j q k M T X Y D sign : PTm n) : Γ ⊢[PRAAx]
    value q M T (frozenPiNumerator (succ j) k) (piDenominator k) X Y D sign ≐
      inst2 frozenBody j (frozenData q M T k zero X Y D sign) := by
  let H := frozenPiNumerator (succ (zero+j)) k
  let J := piDenominator k
  let s (z : PTm n) := Syn.shift z
  have h : Γ ⊢[PRAAx] frozenPiNumerator (succ j) k ≐ H :=
    congrMul (congrSucc (zero_add j).eqSymm) (.eqRefl _)
  have e : Γ ⊢[PRAAx] value q M T (frozenPiNumerator (succ j) k) J X Y D sign ≐ value q M T H J X Y D sign := by
    simpa only [s,GaussianBinetSecondDecayGrid.subst_value,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (value (s q) (s M) (s T) (var 0) (s J) (s X) (s Y) (s D) (s sign)) h
  exact e.eqTrans (GaussianBinetSecondDecaySharedTail.row_at j q M T k zero X Y D sign).eqSymm

theorem zero_origin (q k N M X Y D sign T : PTm n) : Γ ⊢[PRAAx]
    GaussianBinetBoseFrozenMatrix.value q k N M X Y D sign zero T one ≐
      sum frozenBody N (frozenData q M T k zero X Y D sign) := by
  let x := data q M k X Y D sign zero T one
  let y := frozenData q M T k zero X Y D sign
  let w := weight T one M
  let f := columnSumBody matrix
  have entries : Γ ⊢[PRAAx] termsEqual (multiplyBody f) frozenBody N (pairT w (pairT M x)) y := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let j : PTm (n+1) := var 0
    let Δ := lt j (s N) :: Γ.map Fm.shift
    let d := data (s q) (s M) (s k) (s X) (s Y) (s D) (s sign) zero (s T) one
    let w' := weight (s T) one (s M)
    have cell := (multiply_body_at (Γ := Δ) f w' j (pairT (s M) d)).eqTrans
      (qmul_congr (.eqRefl _) (column_sum_at matrix j (s M) d))
    have orig := (column_at (Γ := Δ) j (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign)).eqTrans
      (coefficient_at j (s q) (s k) (s M) (s T) (s X) (s Y) (s D) (s sign))
    simpa only [termsEqual,w,x,y,s,j,Δ,d,w',Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,
      GaussianBinetSecondDecaySharedTail.subst_data,GaussianRationalRiemannRefinement.subst_weight,
      one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using cell.eqTrans orig
  exact (sum_multiply f w N (pairT M x)).eqSymm.eqTrans (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ entries)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenOrigin

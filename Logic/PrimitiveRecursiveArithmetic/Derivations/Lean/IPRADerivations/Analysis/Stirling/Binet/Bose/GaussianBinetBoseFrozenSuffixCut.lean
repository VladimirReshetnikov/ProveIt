import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenSuffix
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecaySuffixBound

/-!
# Trim the geometric tail on the actual frozen time suffix

Each offset column has the full positive majorant of its own damping
row. Cutting the geometric count therefore costs the reciprocal-square
tail independently of the lower time cutoff and discarded count.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenSuffixCut

open_ipra
open GaussianBinetBoseFrozenSuffix (geometry mesh_split fullMesh fullData full_weight columnSegment segmentData segmentBody segment_at suffixValue)
open GaussianBinetBoseFrozenMatrix (matrix matrix_at cell_at subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetBoseFrozenTimeRescale (coordinates)
open GaussianBinetSecondDecayFrozenTail (mesh)
open GaussianBinetSecondDecaySharedTail (clockFloor)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator)
open GaussianBinetSecondDecayTail (rowBounds finite_tail)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (grid)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply sum_canonical)
open GaussianRationalFubini (columnBody column_entry)
open GaussianRationalHorner (qmul qadd)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qadd_sub_cancel)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem column_at (j q k T E B C X Y D sign : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C) : Γ ⊢[PRAAx]
    qmul (weight one E B) (columnSegment j (C*B) B (fullData q k T E B X Y D sign)) ≐
      GaussianBinetSecondDecaySuffixBound.value q (fullMesh T E B) B (C*B) T (frozenPiNumerator (succ j) k)
        (piDenominator k) X Y D sign := by
  let M := fullMesh T E B
  let H := frozenPiNumerator (succ j) k
  let J := piDenominator k
  let f := columnBody matrix
  let g := GaussianBinetSecondDecayGrid.rowBody
  let x := fullData q k T E B X Y D sign
  let y := GaussianBinetSecondDecayGrid.rowData q M T H J X Y D sign
  have rows : Γ ⊢[PRAAx] termsEqual (offB f) (offB g) (C*B) (pairT B (pairT j x)) (pairT B y) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s C*s B)::Γ.map Fm.shift
    let d := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    let m := fullMesh (s T) (s E) (s B)
    let A := frozenPiNumerator (succ (s j)) (s k)
    let V := piDenominator (s k)
    let d' := GaussianBinetSecondDecayGrid.rowData (s q) m (s T) A V (s X) (s Y) (s D) (s sign)
    let l := s B+i
    let t := grid l m (one+zero) (s T) one
    have a := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) f (s B) i (pairT (s j) d)).eqTrans
      (column_entry matrix l (s j) d)
    rw [matrix_at] at a
    have first := a.eqTrans (cell_at l (s j) (s q) (s k) m (s X) (s Y) (s D) (s sign) zero (s T) one)
    have read := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Δ) l m zero (s T) one
    have b := coordinates (s q) (s X) (s Y) (s D) (s sign) (tagNumerator t) (s T*l) (sndT t) m A V
      (read.andE₁.eqTrans (by ipra_ring)) (read.andE₂.eqTrans (one_mul _))
    have last := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) g (s B) i d').eqTrans
      (GaussianBinetSecondDecayGrid.row_at l (s q) m (s T) A V (s X) (s Y) (s D) (s sign))
    simpa only [termsEqual,M,H,J,f,g,x,y,s,i,Δ,d,m,A,V,d',l,Syn.shift,subst_pairT,
      GaussianBinetBoseFrozenSuffix.subst_fullMesh,GaussianBinetBoseFrozenSuffix.subst_fullData,
      GaussianBinetSecondDecayGrid.subst_rowData,subst_frozenPiNumerator,subst_piDenominator,
      PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using first.eqTrans (b.eqTrans last.eqSymm)
  exact qmul_congr (full_weight T E B h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁.andE₁).eqSymm
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ rows)

theorem tail_gap (q k I r T E B C K X Y D sign : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign)
    (hI : Γ ⊢[PRAAx] le one I) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hm : Γ ⊢[PRAAx] le (mesh T (succ (I+r)) k) (fullMesh T E B))
    (hq : Γ ⊢[PRAAx] le (clockFloor (fullMesh T E B) T (succ (I+r)) k) (unit q)) : Γ ⊢[PRAAx]
    distanceBounded (suffixValue q k (I+r) T E B C X Y D sign) (suffixValue q k I T E B C X Y D sign) (num 11*K) I := by
  let f := multiplyBody segmentBody
  let x := segmentData (C*B) B (fullData q k T E B X Y D sign)
  let w := weight one E B
  let d := pairT w x
  let y := pairT I d
  let a := suffixValue q k (I+r) T E B C X Y D sign
  let b := suffixValue q k I T E B C X Y D sign
  let tail := sum (offB f) r y
  have rows : Γ ⊢[PRAAx] rowBounds (offB f) y (num 11*K) I r := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s r)::Γ.map Fm.shift
    let j := s I+i
    let M := succ (s I+s r)
    let u := fullMesh (s T) (s E) (s B)
    let v := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    let w' := weight one (s E) (s B)
    let d' := pairT w' (segmentData (s C*s B) (s B) v)
    have sh : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetBoseFrozenSuffix.subst_geometry] using h.shift.wk
    have sz : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have sk : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have sm : Δ ⊢[PRAAx] le (mesh (s T) M (s k)) u := by
      simpa only [Δ,M,u,s,Fm.shift,Syn.shift,subst_le,GaussianBinetSecondDecayFrozenTail.subst_mesh,
        GaussianBinetBoseFrozenSuffix.subst_fullMesh,PTm.subst_add,ConciseIPRA.PTm.subst_succ] using hm.shift.wk
    have sq : Δ ⊢[PRAAx] le (clockFloor u (s T) M (s k)) (unit (s q)) := by
      simpa only [Δ,M,u,s,Fm.shift,Syn.shift,subst_le,GaussianBinetSecondDecaySharedTail.subst_clockFloor,
        GaussianBinetBoseFrozenSuffix.subst_fullMesh,GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,
        ConciseIPRA.PTm.subst_succ] using hq.shift.wk
    have leJ : Δ ⊢[PRAAx] le j (s I+s r) := le_congr (add_comm i (s I)) (add_comm (s r) (s I))
      (add_le_add_right (s I) (le_of_lt Prf.hyp0))
    have above : Δ ⊢[PRAAx] le (succ j) M := le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
      (add_le_add_right one leJ)
    have estimate := GaussianBinetSecondDecaySuffixBound.frozen_window_bound (s q) u (s B) (s C*s B) (s T) M
      (s k) (succ j) (s K) (s X) (s Y) (s D) (s sign) sz sh.andE₁.andE₁ (zero_lt_succ _) above sk
      (mesh_split (s T) (s E) (s B) (s C) sh) sm sq
    have read := (GaussianRationalFiniteProduct.offset_at (Γ := Δ) f (s I) i d').eqTrans
      ((multiply_body_at segmentBody w' j (segmentData (s C*s B) (s B) v)).eqTrans
        (qmul_congr (.eqRefl _) (segment_at j (s C*s B) (s B) v)))
    have original := read.eqTrans (column_at j (s q) (s k) (s T) (s E) (s B) (s C) (s X) (s Y) (s D) (s sign) sh)
    simpa only [rowBounds,f,x,w,d,y,s,i,Δ,j,u,v,w',d',Syn.shift,subst_pairT,PTm.subst_mul,PTm.subst_num,
      GaussianBinetBoseFrozenSuffix.subst_fullData,GaussianBinetBoseFrozenSuffix.subst_segmentData,
      GaussianRationalRiemannRefinement.subst_weight,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
      bound_congr original.eqSymm (.eqRefl _) (.eqRefl _) estimate
  have small := finite_tail _ _ _ _ _ hI rows
  have split : Γ ⊢[PRAAx] a ≐ qadd b tail := (sum_multiply segmentBody w (I+r) x).eqSymm.eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_split f I r d).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (sum_multiply segmentBody w I x) (.eqRefl tail)))
  have diff : Γ ⊢[PRAAx] qsub a b ≐ tail := (qsub_congr split (.eqRefl b)).eqTrans (qadd_sub_cancel b tail (sum_canonical _ _ _))
  exact bound_congr diff.eqSymm (.eqRefl _) (.eqRefl _) small

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenSuffixCut

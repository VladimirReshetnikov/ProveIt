import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussShiftedProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductAppend

/-!
# Explicit two- and three-factor Gauss products

Appending the literal shifted Gamma rows exposes each factor at its
original rational embedding. The prefixes keep the original row program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussExplicitShiftedProducts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator)
open GaussianGammaGaussShiftedProduct
  (source rowF rowData rowRadius rowValue row_at row_bound_at row_distance_at row_source nameF data)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance)
open GaussianNamedFiniteProductAppend (append_cross empty_cross lastRow)
open GaussianNamedFiniteProductName (rowBounds rowRegular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def prefixData (K z R B m d : PTm n) : PTm n :=
  GaussianNamedFiniteProductName.data K (rowRadius R m d) one (rowData z R B m d)
def gammaRowData (r z R B m d : PTm n) : PTm n :=
  gammaData (shiftedNumerator z B m r) (R+one) (B*m) (d*m)

abbrev twoRowsF : PR 2 := multiplyF gammaF gammaF
def twoRowsData (z R B m d : PTm n) : PTm n :=
  multiplyData gammaF gammaF (gammaRowData zero z R B m d) (gammaRowData one z R B m d)

abbrev threeRowsF : PR 2 := multiplyF twoRowsF gammaF
def threeRowsData (z R B m d : PTm n) : PTm n :=
  multiplyData twoRowsF gammaF (twoRowsData z R B m d) (gammaRowData two z R B m d)

@[simp] theorem subst_gammaRowData {l : ℕ} (σ : Fin n → PTm l) (r z R B m d : PTm n) :
    Syn.subst σ (gammaRowData r z R B m d) = gammaRowData (Syn.subst σ r) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) := by
  simp [gammaRowData,shiftedNumerator,one,GaussianGammaReciprocalInverse.gammaData,
    GaussianGammaReciprocalInverse.gammaHeight]

theorem gamma_row_regular (r z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] pointCN gammaF (gammaRowData r z R B m d) :=
  gamma_regular _ _ _ _ _ (row_source z R B m r a d hs hr)

private theorem prefix_bounds (K z R B m a d : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hK : Γ ⊢[PRAAx] le K m) :
    Γ ⊢[PRAAx] rowBounds rowF K (rowRadius R m d) (rowData z R B m d) := by
  refine .allI (.allI (.impI ?_))
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (sh K) :: (Γ.map Fm.shift).map Fm.shift
  have hs' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.shift.wk
  have hK' : Δ ⊢[PRAAx] le (sh K) (sh m) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hK.shift.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := le_trans Prf.hyp0 hK'
  simpa [Δ,sh,rowBounds,rowBoundsAt,Syn.shift] using
    row_bound_at (var 1) (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) hs' hr

private theorem prefix_row_regular (K z R B m a d : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hK : Γ ⊢[PRAAx] le K m) :
    Γ ⊢[PRAAx] rowRegular rowF K one (rowData z R B m d) := by
  refine .allI (.allI (.allI (.impI ?_)))
  let sh (t : PTm n) := Syn.shift (Syn.shift (Syn.shift t))
  let Δ := lt (var 0) (sh K) :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hs' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.shift.shift.wk
  have hK' : Δ ⊢[PRAAx] le (sh K) (sh m) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hK.shift.shift.shift.wk
  have hr : Δ ⊢[PRAAx] lt (var 0) (sh m) := le_trans Prf.hyp0 hK'
  simpa [Δ,sh,rowRegular,rowDistance,Syn.shift,one] using
    row_distance_at (var 2) (var 1) (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) hs' hr

theorem prefix_regular (K z R B m a d : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hK : Γ ⊢[PRAAx] le K m) :
    Γ ⊢[PRAAx] pointCN nameF (prefixData K z R B m d) :=
  GaussianNamedFiniteProductName.name_regular _ _ _ _ _
    (prefix_bounds K z R B m a d hs hK) (prefix_row_regular K z R B m a d hs hK)

theorem append_shifted (K z R B m a d : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hK : Γ ⊢[PRAAx] le (succ K) m) :
    Γ ⊢[PRAAx] crossEquivalent nameF (multiplyF nameF gammaF) (prefixData (succ K) z R B m d)
      (multiplyData nameF gammaF (prefixData K z R B m d) (gammaRowData K z R B m d)) := by
  let x := rowData z R B m d
  let y := gammaRowData K z R B m d
  let T := rowRadius R m d
  have hP := le_trans (le_succ_self K) hK
  have read : Γ ⊢[PRAAx] lastRow rowF gammaF K x y := by
    refine .allI ?_
    let sh (t : PTm n) := Syn.shift t
    have eq : Γ.map Fm.shift ⊢[PRAAx]
        ap3 rowF (var 0) (sh K) (rowData (sh z) (sh R) (sh B) (sh m) (sh d)) ≐
          ap2 gammaF (var 0) (gammaRowData (sh K) (sh z) (sh R) (sh B) (sh m) (sh d)) :=
      row_at (var 0) (sh K) (sh z) (sh R) (sh B) (sh m) (sh d)
    simpa only [lastRow,x,y,sh,Syn.shift,GaussianGammaGaussShiftedProduct.subst_rowData,subst_gammaRowData] using eq
  exact append_cross rowF gammaF K T T one one x y
    (prefix_bounds K z R B m a d hs hP) (prefix_row_regular K z R B m a d hs hP)
    (prefix_bounds (succ K) z R B m a d hs hK) (prefix_row_regular (succ K) z R B m a d hs hK)
    (gamma_row_regular K z R B m a d hs hK) read

theorem singleton_prefix (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] crossEquivalent nameF gammaF (prefixData one z R B m d) (gammaRowData zero z R B m d) := by
  let x := prefixData zero z R B m d
  let y := gammaRowData zero z R B m d
  have hm := hs.andE₁.andE₁
  have h0 := prefix_regular zero z R B m a d hs (zero_le m)
  have hg := gamma_row_regular zero z R B m a d hs hm
  have e : Γ ⊢[PRAAx] crossEquivalent nameF oneF x y :=
    cross_trans _ _ _ _ _ _ (empty_cross rowF (rowRadius R m d) one (rowData z R B m d))
      (GaussianBoundedInverseApartness.ones_equivalent (rowData z R B m d) y)
  have lift := multiply_cross nameF oneF gammaF gammaF x y y y h0 (one_fast y) hg hg e (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (append_shifted zero z R B m a d hs hm)
    (cross_trans _ _ _ _ _ _ lift (multiply_one_left gammaF y hg))

theorem two_rows_regular (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] le two m) : Γ ⊢[PRAAx] pointCN twoRowsF (twoRowsData z R B m d) :=
  multiply_fast gammaF gammaF _ _ (gamma_row_regular zero z R B m a d hs hs.andE₁.andE₁)
    (gamma_row_regular one z R B m a d hs hm)

theorem three_rows_regular (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] le (succ two) m) : Γ ⊢[PRAAx] pointCN threeRowsF (threeRowsData z R B m d) :=
  multiply_fast twoRowsF gammaF _ _ (two_rows_regular z R B m a d hs (le_trans (le_succ_self two) hm))
    (gamma_row_regular two z R B m a d hs hm)

theorem two_prefix (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) (hm : Γ ⊢[PRAAx] le two m) :
    Γ ⊢[PRAAx] crossEquivalent nameF twoRowsF (prefixData two z R B m d) (twoRowsData z R B m d) := by
  let x := prefixData one z R B m d
  let u := gammaRowData zero z R B m d
  let v := gammaRowData one z R B m d
  have hx := prefix_regular one z R B m a d hs hs.andE₁.andE₁
  have hu := gamma_row_regular zero z R B m a d hs hs.andE₁.andE₁
  have hv := gamma_row_regular one z R B m a d hs hm
  have step := multiply_cross nameF gammaF gammaF gammaF x u v v hx hu hv hv
    (singleton_prefix z R B m a d hs) (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ (append_shifted one z R B m a d hs hm) step

theorem three_prefix (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d)
    (hm : Γ ⊢[PRAAx] le (succ two) m) :
    Γ ⊢[PRAAx] crossEquivalent nameF threeRowsF (prefixData (succ two) z R B m d) (threeRowsData z R B m d) := by
  let x := prefixData two z R B m d
  let u := twoRowsData z R B m d
  let v := gammaRowData two z R B m d
  have h2 := le_trans (le_succ_self two) hm
  have hx := prefix_regular two z R B m a d hs h2
  have hu := two_rows_regular z R B m a d hs h2
  have hv := gamma_row_regular two z R B m a d hs hm
  have step := multiply_cross nameF twoRowsF gammaF gammaF x u v v hx hu hv hv
    (two_prefix z R B m a d hs h2) (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ (append_shifted two z R B m a d hs hm) step

theorem two_factors (z R B a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B two a d) :
    Γ ⊢[PRAAx] crossEquivalent nameF twoRowsF (data z R B two d) (twoRowsData z R B two d) :=
  two_prefix z R B two a d hs (le_refl two)

theorem three_factors (z R B a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B (succ two) a d) :
    Γ ⊢[PRAAx] crossEquivalent nameF threeRowsF (data z R B (succ two) d) (threeRowsData z R B (succ two) d) :=
  three_prefix z R B (succ two) a d hs (le_refl _)

theorem actual_Gauss_two_shifted_factors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) two (var 3) (var 4) ⟶
      crossEquivalent nameF twoRowsF (data (var 0) (var 1) (var 2) two (var 4))
        (twoRowsData (var 0) (var 1) (var 2) two (var 4))) :=
  closeUniv 5 (.impI (two_factors _ _ _ _ _ Prf.hyp0))

theorem actual_Gauss_three_shifted_factors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (succ two) (var 3) (var 4) ⟶
      crossEquivalent nameF threeRowsF (data (var 0) (var 1) (var 2) (succ two) (var 4))
        (threeRowsData (var 0) (var 1) (var 2) (succ two) (var 4))) :=
  closeUniv 5 (.impI (three_factors _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussExplicitShiftedProducts

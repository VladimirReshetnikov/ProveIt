import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImageLattice

/-!
# Exact integer cuts of the corrected positive power chart

Literal chart numerators and denominators are the two programs supplied
to the common rational lattice. The resulting finite lattice has the
same endpoints as the corrected chart. Its cells are grouped by the
actual corrected nodes, with no rounding of endpoints or widths.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageCuts

open_ipra
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator imageFraction)
open GaussianEulerPositivePowerChartCorrectedPanel (native_order)
open GaussianEulerPositivePowerChartImage (reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianPartitionedFiniteSum (increasing)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def data (k e f d h Q S E T a C N : PTm n) : PTm n :=
  Foundations.BoundedSyntax.pack ![k,e,f,d,h,Q,S,E,T,a,C,N]

private def fields (i x : PTm n) : Fin 13 → PTm n :=
  Fin.cases i (fun j => Foundations.BoundedFormulas.at1 (Foundations.BoundedSyntax.projections 12 j) x)

private def numeratorTerm : PTm 13 :=
  imageNumerator (var 1) (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)
    (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)

private def denominatorTerm : PTm 13 :=
  imageDenominator (var 1) (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)
    (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)

def numeratorBody : PTm 2 := Syn.subst (fields (var 0) (var 1)) numeratorTerm
def denominatorBody : PTm 2 := Syn.subst (fields (var 0) (var 1)) denominatorTerm

ipra_subst data [Foundations.BoundedSyntax.subst_pack]

private theorem read_at (s : PTm 13) (i : PTm n) (args : Fin 12 → PTm n) :
    Γ ⊢[PRAAx] inst2 (Syn.subst (fields (var 0) (var 1)) s) i (Foundations.BoundedSyntax.pack args) ≐
      Syn.subst (Fin.cases i args) s := by
  let x := Foundations.BoundedSyntax.pack args
  have hw : inst2 (Syn.subst (fields (var 0) (var 1)) s) i x = Syn.subst (fields i x) s := by
    simp only [inst2,Syn.subst_subst]
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => simp [fields]
    | succ j =>
      simp only [fields,Fin.cases_succ,Foundations.BoundedFormulas.at1,Syn.subst_subst]
      congr 1
      funext l
      fin_cases l
      rfl
  rw [hw]
  exact Prf.eqCongr s (fun j => by
    cases j using Fin.cases with
    | zero => exact .eqRefl _
    | succ j => exact Foundations.BoundedSyntax.projections_pack args j)

theorem numerator_at (k i e f d h Q S E T a C N : PTm n) : Γ ⊢[PRAAx]
    inst2 numeratorBody i (data k e f d h Q S E T a C N) ≐ imageNumerator k i e f d h Q S E T a C N := by
  have hn := read_at (Γ := Γ) numeratorTerm i ![k,e,f,d,h,Q,S,E,T,a,C,N]
  change Γ ⊢[PRAAx] inst2 numeratorBody i (data k e f d h Q S E T a C N) ≐ _ at hn
  have rhs : Syn.subst (Fin.cases i ![k,e,f,d,h,Q,S,E,T,a,C,N]) numeratorTerm = imageNumerator k i e f d h Q S E T a C N := by
    simp only [numeratorTerm,GaussianEulerPositivePowerChartCorrectedImage.subst_imageNumerator,Syn.subst_var]
    rfl
  exact rhs ▸ hn

theorem denominator_at (k i e f d h Q S E T a C N : PTm n) : Γ ⊢[PRAAx]
    inst2 denominatorBody i (data k e f d h Q S E T a C N) ≐ imageDenominator k i e f d h Q S E T a C N := by
  have hd := read_at (Γ := Γ) denominatorTerm i ![k,e,f,d,h,Q,S,E,T,a,C,N]
  change Γ ⊢[PRAAx] inst2 denominatorBody i (data k e f d h Q S E T a C N) ≐ _ at hd
  have rhs : Syn.subst (Fin.cases i ![k,e,f,d,h,Q,S,E,T,a,C,N]) denominatorTerm = imageDenominator k i e f d h Q S E T a C N := by
    simp only [denominatorTerm,GaussianEulerPositivePowerChartCorrectedImage.subst_imageDenominator,Syn.subst_var]
    rfl
  exact rhs ▸ hd

theorem original_denominators (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    RationalProductWitness.denominatorGuard denominatorBody (succ N) (data k e f d h Q S E T a C N) := by
  let sh (t : PTm n) := Syn.shift t
  have sourceShift : Γ.map Fm.shift ⊢[PRAAx] input
      (sh k) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  refine .allI (.impI ?_)
  have bound : (lt (var 0) (succ (sh N))) :: Γ.map Fm.shift ⊢[PRAAx] le (var 0) (sh N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have domain := GaussianEulerPositivePowerChartCorrectedImage.corrected_domain (sh k) (var 0)
    (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N) sourceShift.wk bound
  simpa only [RationalProductWitness.denominatorGuard,subst_data,ConciseIPRA.PTm.subst_succ,Syn.shift,sh] using
    le_congr (.eqRefl _) (denominator_at (sh k) (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T)
      (sh a) (sh C) (sh N)).eqSymm domain.andE₁.andE₂

theorem original_ordered (k e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) : Γ ⊢[PRAAx]
    GaussianEulerPositivePowerChartImageLattice.ordered numeratorBody denominatorBody N (data k e f d h Q S E T a C N) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have sourceShift : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input
      (sh k) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift.shift
  refine .allI (.allI (.impI ?_))
  have hIndices : (le (var 1) (var 0) ⋏ le (var 0) (sh N)) :: (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      le (var 1) (var 0) ⋏ le (var 0) (sh N) := Prf.hyp0
  have order := native_order (sh k) (var 1) (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T)
    (sh a) (sh C) (sh N) sourceShift.wk.andE₁ hIndices.andE₁ hIndices.andE₂
  simpa only [GaussianEulerPositivePowerChartImageLattice.ordered,subst_data,Syn.shift,sh] using le_congr
    (congrMul (numerator_at (sh k) (var 1) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm
      (denominator_at (sh k) (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm)
    (congrMul (numerator_at (sh k) (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm
      (denominator_at (sh k) (var 1) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm) order

abbrev cutF : PR 2 := GaussianEulerPositivePowerChartImageLattice.cutF numeratorBody denominatorBody

abbrev start (N x J : PTm n) : PTm n := GaussianEulerPositivePowerChartImageLattice.start numeratorBody denominatorBody N x J

abbrev count (N x J : PTm n) : PTm n := ap2 cutF N (GaussianEulerPositivePowerChartImageLattice.cutData N x J)

abbrev denominator (N x J : PTm n) : PTm n := GaussianEulerPositivePowerChartImageLattice.meshDenominator denominatorBody N x J

def point (j N x J : PTm n) : PTm n := pairT (start N x J+j) (denominator N x J)

ipra_subst point [start, denominator]

theorem original_cut_increasing (k e f d h Q S E T a C N J : PTm n) (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) :
    Γ ⊢[PRAAx] increasing cutF (GaussianEulerPositivePowerChartImageLattice.cutData N (data k e f d h Q S E T a C N) J) :=
  GaussianEulerPositivePowerChartImageLattice.cut_increasing _ _ _ _ _ (original_denominators k e f d h Q S E T a C N hs) (original_ordered k e f d h Q S E T a C N hs)

theorem original_lattice_node (k i e f d h Q S E T a C N J : PTm n) (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N)
    (hi : Γ ⊢[PRAAx] le i N) (hJ : Γ ⊢[PRAAx] le one J) :
    Γ ⊢[PRAAx] fraction
      (start N (data k e f d h Q S E T a C N) J+ap2 cutF i (GaussianEulerPositivePowerChartImageLattice.cutData N (data k e f d h Q S E T a C N) J))
      (denominator N (data k e f d h Q S E T a C N) J) ≐ imageFraction k i e f d h Q S E T a C N := by
  let x := data k e f d h Q S E T a C N
  have hn := original_denominators k e f d h Q S E T a C N hs
  have ho := original_ordered k e f d h Q S E T a C N hs
  have e1 := GaussianEulerPositivePowerChartImageLattice.absolute_as_relative numeratorBody denominatorBody i N x J hn ho hi
  have e2 := GaussianEulerPositivePowerChartImageLattice.absolute_below (Γ := Γ) numeratorBody denominatorBody i N x J hi
  have e3 := GaussianEulerPositivePowerChartImageLattice.node_fraction numeratorBody denominatorBody i N x J hn hi hJ
  exact (GaussianEulerPositivePowerChartJacobian.fraction_congr (e1.eqTrans e2) (.eqRefl _)).eqTrans
    (e3.eqTrans (GaussianEulerPositivePowerChartJacobian.fraction_congr
      (numerator_at k i e f d h Q S E T a C N) (denominator_at k i e f d h Q S E T a C N)))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageCuts

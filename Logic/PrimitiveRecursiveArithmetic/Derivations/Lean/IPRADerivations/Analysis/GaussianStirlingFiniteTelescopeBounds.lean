import IPRADerivations.Analysis.GaussianStirlingTelescopeName
import IPRADerivations.Analysis.GaussianStirlingTailComparison
import IPRADerivations.Analysis.GaussianGammaShiftedDeflatedZero

/-!
# Rational bounds for the actual Stirling finite difference sum

Uniform observation errors on the local differences add linearly
under quantifier-free induction. The rational comparison values
telescope exactly at the translated endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingFiniteTelescopeBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qzero_canonical)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers
  (upperDifference geometricMain fraction_same upper_den_positive gap_positive small_numeral_positive)
open GaussianStirlingTelescope (shifted shifted_source rawSum dBody d_at sampleData)
open GaussianStirlingTailComparison (point_add_upper_same)
open GaussianEulerPositivePowerChartCorrectedImage (fraction_sum)
open GaussianPositiveRationalLogarithm (fraction)
open RationalValueBounds (upper upper_congr upper_of_order)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data

theorem upper_step (a b i : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (upperDifference a b i) (geometricMain (shifted a b i) b) ≐ upperDifference a b (succ i) := by
  let c := shifted a b i
  let d := shifted a b (succ i)
  let v := GaussianStirlingRationalTelescopers.gap c b
  have hc := le_trans ha (le_add_right a (b*i))
  have hd := le_trans ha (le_add_right a (b*succ i))
  have h₁ := positive_product _ _ (upper_den_positive a ha) hc
  have h₂ := positive_product _ _ (small_numeral_positive 2) (gap_positive c b hc)
  have h₃ := positive_product _ _ (upper_den_positive a ha) hd
  exact (fraction_sum (b*b*i) (num 12*a*c) (b*b) (num 3*v) h₁ h₂).eqTrans
    (fraction_same _ _ _ _ (positive_product _ _ h₁ h₂) h₃ (by dsimp [v,c,d,shifted,GaussianStirlingRationalTelescopers.gap]; ipra_ring))

theorem upper_zero (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] upperDifference a b zero ≐ qzero := by
  let c := a+b*zero
  let V := num 12*a*c
  have h := positive_product _ _ (upper_den_positive a ha) (le_trans ha (le_add_right a (b*zero)))
  have e : Γ ⊢[PRAAx] upperDifference a b zero ≐ fraction zero V :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)
  exact e.eqTrans (GaussianGammaShiftedDeflatedZero.zero_fraction _ V h
    ((ComplexLogarithmRemainder.normSq_scale zero ComplexLogarithmRemainder.oneCode).eqTrans (by ipra_ring)))

def localBounds (p a b : PTm n) : Fm PTm n :=
  upper (fstT qzero) (fstT (ap2 D p (DD a b))) one (unit p) ⋏
    upper (fstT (ap2 D p (DD a b))) (fstT (geometricMain a b)) one (unit p)
def rows (p a b : PTm n) : Fm PTm n := .all (localBounds (Syn.shift p) (shifted (Syn.shift a) (Syn.shift b) (var 0)) (Syn.shift b))
def sumBounds (p N a b : PTm n) : Fm PTm n :=
  upper (fstT qzero) (fstT (rawSum p N a b)) N (unit p) ⋏
    upper (fstT (rawSum p N a b)) (fstT (upperDifference a b N)) N (unit p)

@[simp] theorem subst_localBounds {l : ℕ} (σ : Fin n → PTm l) (p a b : PTm n) :
    (localBounds p a b).subst σ = localBounds (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [localBounds,one]
@[simp] theorem subst_rows {l : ℕ} (σ : Fin n → PTm l) (p a b : PTm n) :
    (rows p a b).subst σ = rows (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [rows,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_sumBounds {l : ℕ} (σ : Fin n → PTm l) (p N a b : PTm n) :
    (sumBounds p N a b).subst σ = sumBounds (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [sumBounds]

theorem row_at (p a b i : PTm n) (h : Γ ⊢[PRAAx] rows p a b) :
    Γ ⊢[PRAAx] localBounds p (shifted a b i) b := by
  simpa only [rows,subst_localBounds,GaussianStirlingTelescope.subst_shifted,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem sum_upper_step (p i a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] sumBounds p i a b) (row : Γ ⊢[PRAAx] localBounds p (shifted a b i) b) :
    Γ ⊢[PRAAx] sumBounds p (succ i) a b := by
  let x := rawSum p i a b
  let y := ap2 D p (DD (shifted a b i) b)
  have s := (GaussianRationalFiniteSum.sum_succ (Γ := Γ) dBody i (sampleData p a b)).eqTrans
    (qadd_congr (.eqRefl _) (d_at p a b i))
  have low := point_add_upper_same qzero x qzero y i one (unit p) (unit_positive p) h.andE₁ row.andE₁
  have hi := point_add_upper_same x (upperDifference a b i) y (geometricMain (shifted a b i) b)
    i one (unit p) (unit_positive p) h.andE₂ row.andE₂
  exact .andI
    (upper_congr (congrFst (GaussianRationalMonicReconstruction.zero_add_zero (Γ := Γ)))
      (congrFst s.eqSymm) (succ_eq_add_one i).eqSymm (.eqRefl _) low)
    (upper_congr (congrFst s.eqSymm) (congrFst (upper_step a b i ha))
      (succ_eq_add_one i).eqSymm (.eqRefl _) hi)

theorem sum_bounds (p N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (h : Γ ⊢[PRAAx] rows p a b) : Γ ⊢[PRAAx] sumBounds p N a b := by
  have all : Γ ⊢[PRAAx] .all (sumBounds (Syn.shift p) (var 0) (Syn.shift a) (Syn.shift b)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_sumBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have e := GaussianRationalFiniteSum.sum_zero (Γ := Γ) dBody (sampleData p a b)
      have o : Γ ⊢[PRAAx] upper (fstT qzero) (fstT qzero) zero (unit p) := upper_of_order _ _ _ _ (le_refl _)
      exact .andI (upper_congr (.eqRefl _) (congrFst e.eqSymm) (.eqRefl _) (.eqRefl _) o)
        (upper_congr (congrFst e.eqSymm) (congrFst (upper_zero a b ha).eqSymm) (.eqRefl _) (.eqRefl _) o)
    · simp only [subst_sumBounds,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let j : PTm (n+1) := var 0
      let a' := Syn.shift a
      let b' := Syn.shift b
      let p' := Syn.shift p
      let Δ := sumBounds p' j a' b' :: Γ.map Fm.shift
      have ha' : Δ ⊢[PRAAx] le one a' := by simpa [Fm.shift,Syn.shift,a',Δ,one] using ha.shift.wk
      have h' : Δ ⊢[PRAAx] rows p' a' b' := by simpa [Fm.shift,Syn.shift,p',a',b',Δ] using h.shift.wk
      exact sum_upper_step p' j a' b' ha' Prf.hyp0 (row_at p' a' b' j h')
  simpa only [subst_sumBounds,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

end LeanProofs.IPRA.Analysis.GaussianStirlingFiniteTelescopeBounds

import IPRADerivations.Analysis.GaussianDescentClockArithmetic
import IPRADerivations.Analysis.GaussianRationalMetric
import IPRADerivations.Analysis.GaussianRationalL1
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual finite rational-descent iterate and its residual clock

Source04's approximate-root corollary, conditional on the named local RD
contract from the human FTA packet. The fixed PR3 step receives degree,
coefficient-list code and current point. Polynomial evaluation is the actual
Gaussian-rational Horner program. No program-code evaluator is introduced.

Every step output is canonically recoded. Local RD is required only at
canonical rational points and compares actual squared residual values.
Global decay and the final residual bound are proved for the actual iterate.
The RD estimate itself, rather than root existence, is the explicit remaining
external mathematical obligation.
-/

set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDescentClock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im code normSq eval_re_code eval_im_code)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate canonical qzero)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (rateDenominator clock positive_product)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def valueDenominator (q : PTm n) : PTm n := GaussianRationalL1.rawDen q
def valueNumerator (q : PTm n) : PTm n := GaussianRationalL1.rawGaussian q
def canonicalize (q : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (valueNumerator q) (valueDenominator q)

@[simp] theorem subst_valueDenominator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (valueDenominator q) = valueDenominator (Syn.subst σ q) := by simp [valueDenominator]
@[simp] theorem subst_valueNumerator {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (valueNumerator q) = valueNumerator (Syn.subst σ q) := by simp [valueNumerator]
@[simp] theorem subst_canonicalize {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (canonicalize q) = canonicalize (Syn.subst σ q) := by simp [canonicalize]

theorem value_denominator_positive (q : PTm n) : Γ ⊢[PRAAx] le one (valueDenominator q) :=
  GaussianRationalL1.raw_den_positive q

theorem value_represents (q : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents q (valueNumerator q) (valueDenominator q) := GaussianRationalL1.raw_represents q

theorem canonicalize_canonical (q : PTm n) : Γ ⊢[PRAAx] canonical (canonicalize q) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ (value_denominator_positive q)

theorem canonicalize_exact (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] canonicalize q ≐ q :=
  (GaussianRationalHorner.canonical_unique _ _ _ _ hq (canonicalize_canonical q)
    (value_denominator_positive q) (value_represents q)
    (GaussianRationalHorner.ofGaussian_represents _ _ (value_denominator_positive q))).eqSymm

def residualNumerator (C z : PTm n) : PTm n := normSq (valueNumerator (evaluate C z))
def residualDenominator (C z : PTm n) : PTm n := valueDenominator (evaluate C z)

@[simp] theorem subst_residualNumerator {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (residualNumerator C z) = residualNumerator (Syn.subst σ C) (Syn.subst σ z) := by simp [residualNumerator]
@[simp] theorem subst_residualDenominator {m : ℕ} (σ : Fin n → PTm m) (C z : PTm n) :
    Syn.subst σ (residualDenominator C z) = residualDenominator (Syn.subst σ C) (Syn.subst σ z) := by simp [residualDenominator]

theorem residual_denominator_positive (C z : PTm n) : Γ ⊢[PRAAx] le one (residualDenominator C z) :=
  value_denominator_positive _

theorem residual_bound_iff (C z a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    Fm.iff (GaussianRationalMetric.bounded (evaluate C z) a b)
      (le ((b*b)*residualNumerator C z) ((a*a)*(residualDenominator C z*residualDenominator C z))) :=
  GaussianRationalMetric.bounded_iff _ _ _ _ _ (value_denominator_positive _) hb (value_represents _)

def advance (step : PR 3) (d C z : PTm n) : PTm n := canonicalize (ap3 step d C z)
def iterationStep (step : PR 3) : PTm 4 := advance step (var 2) (var 3) (var 1)
def iterationF (step : PR 3) : PR 3 := recDef (qzero : PTm 2) (iterationStep step)
def iterate (step : PR 3) (d C k : PTm n) : PTm n := ap3 (iterationF step) k d C

@[simp] theorem subst_advance {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C z : PTm n) :
    Syn.subst σ (advance step d C z) = advance step (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ z) := by simp [advance]
@[simp] theorem subst_iterate {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C k : PTm n) :
    Syn.subst σ (iterate step d C k) = iterate step (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ k) := by simp [iterate]

theorem iterate_zero (step : PR 3) (d C : PTm n) : Γ ⊢[PRAAx] iterate step d C zero ≐ qzero := by
  have h := rec_zero (Γ := Γ) (qzero : PTm 2) (iterationStep step) ![d,C]
  have e : (Fin.cases zero ![d,C] : Fin 3 → PTm n) = ![zero,d,C] := by funext i; fin_cases i <;> rfl
  rw [e] at h
  simpa only [iterate,iterationF,ap3,GaussianRationalHorner.subst_qzero] using h

theorem iterate_succ (step : PR 3) (d C k : PTm n) : Γ ⊢[PRAAx]
    iterate step d C (succ k) ≐ advance step d C (iterate step d C k) := by
  have h := rec_succ (Γ := Γ) (qzero : PTm 2) (iterationStep step) k ![d,C]
  have a : (Fin.cases (succ k) ![d,C] : Fin 3 → PTm n) = ![succ k,d,C] := by funext i; fin_cases i <;> rfl
  have b : (Fin.cases k (Fin.cases (PTm.app (recDef (qzero : PTm 2) (iterationStep step)) (Fin.cases k ![d,C])) ![d,C]) :
      Fin 4 → PTm n) = ![k,iterate step d C k,d,C] := by funext i; fin_cases i <;> rfl
  rw [a,b] at h
  simpa [iterate,iterationF,iterationStep,ap3] using h

theorem iterate_canonical (step : PR 3) (d C k : PTm n) : Γ ⊢[PRAAx] canonical (iterate step d C k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp3 (iterationF step) Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (iterate_zero step d C))
      (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp3 (iterationF step) Prf.hyp0 (.eqRefl _) (.eqRefl _)).eqTrans (iterate_succ step d C _))
      (canonicalize_canonical _)

def contractionSquare (d : PTm n) : PTm n := RationalIntegerNormalization.normalize
  (ZT.ofNat (pred (rateDenominator d)*pred (rateDenominator d))) (rateDenominator d*rateDenominator d)
def rdAt (step : PR 3) (d C z : PTm n) : Fm PTm n := RationalArgmin.rationalLE
  (GaussianRationalMetric.qnormSq (evaluate C (advance step d C z)))
  (RationalArithmetic.multiply (contractionSquare d) (GaussianRationalMetric.qnormSq (evaluate C z)))
def localRD (step : PR 3) (d C : PTm n) : Fm PTm n :=
  .all (canonical (var 0) ⟶ rdAt step (Syn.shift d) (Syn.shift C) (var 0))

@[simp] theorem subst_contractionSquare {m : ℕ} (σ : Fin n → PTm m) (d : PTm n) :
    Syn.subst σ (contractionSquare d) = contractionSquare (Syn.subst σ d) := by simp [contractionSquare]
@[simp] theorem subst_rdAt {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C z : PTm n) :
    (rdAt step d C z).subst σ = rdAt step (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ z) := by simp [rdAt]
@[simp] theorem subst_localRD {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C : PTm n) :
    (localRD step d C).subst σ = localRD step (Syn.subst σ d) (Syn.subst σ C) := by simp [localRD,Syn.subst_shift,Syn.shift_subst]

theorem local_rd_at (step : PR 3) (d C z : PTm n)
    (h : Γ ⊢[PRAAx] localRD step d C) (hz : Γ ⊢[PRAAx] canonical z) : Γ ⊢[PRAAx] rdAt step d C z := by
  have rule : Γ ⊢[PRAAx] canonical z ⟶ rdAt step d C z := by
    simpa only [localRD,Fm.subst_imp,GaussianRationalHorner.subst_canonical,subst_rdAt,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE z h
  exact .impE rule hz

/-- The genuine local rational comparison supplies this cleared inequality;
all residual denominators are computed from the actual Horner outputs. -/
theorem rd_to_cleared (step : PR 3) (d C z : PTm n) (h : Γ ⊢[PRAAx] rdAt step d C z) : Γ ⊢[PRAAx]
    le ((rateDenominator d*rateDenominator d)*residualNumerator C (advance step d C z)*
      (residualDenominator C z*residualDenominator C z))
      ((pred (rateDenominator d)*pred (rateDenominator d))*residualNumerator C z*
        (residualDenominator C (advance step d C z)*residualDenominator C (advance step d C z))) := by
  have rp := GaussianDescentClockArithmetic.rate_positive (Γ := Γ) d
  have factor : Γ ⊢[PRAAx] RationalArithmetic.represents (contractionSquare d)
      (ZT.ofNat (pred (rateDenominator d)*pred (rateDenominator d))) (rateDenominator d*rateDenominator d) :=
    RationalIntegerNormalization.normalize_preserves_value _ _ (positive_product _ _ rp rp)
  have old := GaussianRationalMetric.qnormSq_represents (Γ := Γ) (evaluate C z) (valueNumerator (evaluate C z))
    (residualDenominator C z) (residual_denominator_positive C z) (value_represents _)
  have next := GaussianRationalMetric.qnormSq_represents (Γ := Γ) (evaluate C (advance step d C z))
    (valueNumerator (evaluate C (advance step d C z))) (residualDenominator C (advance step d C z))
    (residual_denominator_positive C _) (value_represents _)
  have product := RationalRepresentations.represents_multiply _ _ _ _ _ _ factor old
  have product' : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.multiply (contractionSquare d) (GaussianRationalMetric.qnormSq (evaluate C z)))
      (ZT.ofNat ((pred (rateDenominator d)*pred (rateDenominator d))*residualNumerator C z))
      ((rateDenominator d*rateDenominator d)*(residualDenominator C z*residualDenominator C z)) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := product)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,residualNumerator]
    ipra_simps
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ next product' h
  change Γ ⊢[PRAAx] le
    ((rateDenominator d*rateDenominator d)*(residualDenominator C z*residualDenominator C z)*
      residualNumerator C (advance step d C z))
    ((pred (rateDenominator d)*pred (rateDenominator d))*residualNumerator C z*
      (residualDenominator C (advance step d C z)*residualDenominator C (advance step d C z))) at raw
  exact le_congr (by ipra_ring) (.eqRefl _) raw

/-- Multiplication of one local contraction and one prefix bound. The
current denominator is positive even when the current residual is zero. -/
theorem combine_step (M m L R x y c d : PTm n) (hc : Γ ⊢[PRAAx] le one c)
    (ih : Γ ⊢[PRAAx] le (L*x) (R*c))
    (rd : Γ ⊢[PRAAx] le ((M*M)*y*c) ((m*m)*x*d)) :
    Γ ⊢[PRAAx] le ((M*M)*L*y) ((m*m)*R*d) := by
  have p := mul_le_mul_right L rd
  have q := mul_le_mul_right (m*m*d) ih
  have comparison : Γ ⊢[PRAAx] le (c*((M*M)*L*y)) (c*((m*m)*R*d)) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) p)
      (le_congr (.eqRefl _) (by ipra_ring) q)
  exact RationalValueBounds.positive_cancel hc comparison

theorem residual_numerator_congr (C : PTm n) {z w : PTm n} (h : Γ ⊢[PRAAx] z ≐ w) :
    Γ ⊢[PRAAx] residualNumerator C z ≐ residualNumerator C w := by
  ipra_congr (residualNumerator (var 0) (var 1) : PTm 2) with [.eqRefl C, h]
theorem residual_denominator_congr (C : PTm n) {z w : PTm n} (h : Γ ⊢[PRAAx] z ≐ w) :
    Γ ⊢[PRAAx] residualDenominator C z ≐ residualDenominator C w := by
  ipra_congr (residualDenominator (var 0) (var 1) : PTm 2) with [.eqRefl C, h]

def decay (step : PR 3) (d C a b k : PTm n) : Fm PTm n :=
  le ((pw (rateDenominator d) k*pw (rateDenominator d) k)*(b*b)*residualNumerator C (iterate step d C k))
    ((pw (pred (rateDenominator d)) k*pw (pred (rateDenominator d)) k)*(a*a)*
      (residualDenominator C (iterate step d C k)*residualDenominator C (iterate step d C k)))

@[simp] theorem subst_decay {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C a b k : PTm n) :
    (decay step d C a b k).subst σ = decay step (Syn.subst σ d) (Syn.subst σ C)
      (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) := by simp [decay]

theorem decay_zero (step : PR 3) (d C a b : PTm n)
    (h : Γ ⊢[PRAAx] le ((b*b)*residualNumerator C qzero)
      ((a*a)*(residualDenominator C qzero*residualDenominator C qzero))) :
    Γ ⊢[PRAAx] decay step d C a b zero := by
  have p := natEq (pw_zero (Γ := Γ) (rateDenominator d))
  have q := natEq (pw_zero (Γ := Γ) (pred (rateDenominator d)))
  have num := natEq (residual_numerator_congr C (iterate_zero (Γ := Γ) step d C))
  have den := natEq (residual_denominator_congr C (iterate_zero (Γ := Γ) step d C))
  apply le_congr (h := h)
  · apply deriveNat; ipra_simps; rw [p,num]; ring
  · apply deriveNat; ipra_simps; rw [q,den]; ring

theorem decay_succ (step : PR 3) (d C a b k : PTm n)
    (hRD : Γ ⊢[PRAAx] localRD step d C) (ih : Γ ⊢[PRAAx] decay step d C a b k) :
    Γ ⊢[PRAAx] decay step d C a b (succ k) := by
  have hLocal := rd_to_cleared step d C (iterate step d C k)
    (local_rd_at _ _ _ _ hRD (iterate_canonical step d C k))
  have positive := positive_product _ _ (residual_denominator_positive (Γ := Γ) C (iterate step d C k))
    (residual_denominator_positive C (iterate step d C k))
  have combined := combine_step (rateDenominator d) (pred (rateDenominator d))
    (pw (rateDenominator d) k*pw (rateDenominator d) k*(b*b))
    (pw (pred (rateDenominator d)) k*pw (pred (rateDenominator d)) k*(a*a))
    (residualNumerator C (iterate step d C k)) (residualNumerator C (advance step d C (iterate step d C k)))
    (residualDenominator C (iterate step d C k)*residualDenominator C (iterate step d C k))
    (residualDenominator C (advance step d C (iterate step d C k))*residualDenominator C (advance step d C (iterate step d C k)))
    positive ih hLocal
  have p := natEq (pw_succ (Γ := Γ) (rateDenominator d) k)
  have q := natEq (pw_succ (Γ := Γ) (pred (rateDenominator d)) k)
  have num := natEq (residual_numerator_congr C (iterate_succ (Γ := Γ) step d C k))
  have den := natEq (residual_denominator_congr C (iterate_succ (Γ := Γ) step d C k))
  apply le_congr (h := combined)
  · apply deriveNat; ipra_simps; rw [p,num]; ring
  · apply deriveNat; ipra_simps; rw [q,den]; ring

/-- QF induction derives global decay solely from the local RD estimate and
the legitimate initial residual bound. No global decay law is supplied. -/
theorem iterate_decay (step : PR 3) (d C a b k : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hInitial : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (evaluate C qzero) a b)
    (hRD : Γ ⊢[PRAAx] localRD step d C) : Γ ⊢[PRAAx] decay step d C a b k := by
  have rdShift : Γ.map Fm.shift ⊢[PRAAx] localRD step (Syn.shift d) (Syn.shift C) := by
    simpa only [Fm.shift,subst_localRD,Syn.shift] using hRD.shift
  have all : Γ ⊢[PRAAx] .all (decay step (Syn.shift d) (Syn.shift C) (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_decay,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact decay_zero step d C a b ((residual_bound_iff _ _ _ _ hb).iffMp hInitial)
    · simp only [subst_decay,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact decay_succ _ _ _ _ _ _ rdShift.wk Prf.hyp0
  simpa only [subst_decay,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all

theorem clock_residual (step : PR 3) (d C a b e f : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (he : Γ ⊢[PRAAx] le one e) (hf : Γ ⊢[PRAAx] le one f)
    (hInitial : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (evaluate C qzero) a b)
    (hRD : Γ ⊢[PRAAx] localRD step d C) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (evaluate C (iterate step d C (clock d a b e f))) e f := by
  let J := clock d a b e f
  have decayed := iterate_decay step d C a b J hb hInitial hRD
  have budget := GaussianDescentClockArithmetic.clock_budget d a b e f hb he
  change Γ ⊢[PRAAx] le (pw (pred (rateDenominator d)) J*a*f) (pw (rateDenominator d) J*b*e) at budget
  have first := mul_le_mul_right (f*f) decayed
  have second := mul_le_mul_right
    (residualDenominator C (iterate step d C J)*residualDenominator C (iterate step d C J))
      (le_mul_mono budget budget)
  let L := (pw (rateDenominator d) J*pw (rateDenominator d) J)*(b*b)
  let U := (pw (pred (rateDenominator d)) J*a*f)*(pw (pred (rateDenominator d)) J*a*f)*
    (residualDenominator C (iterate step d C J)*residualDenominator C (iterate step d C J))
  have first' : Γ ⊢[PRAAx] le (L*((f*f)*residualNumerator C (iterate step d C J))) U :=
    le_congr (by unfold L; ipra_ring) (by unfold U; ipra_ring) first
  have comparison : Γ ⊢[PRAAx] le (L*((f*f)*residualNumerator C (iterate step d C J)))
      (L*((e*e)*(residualDenominator C (iterate step d C J)*residualDenominator C (iterate step d C J)))) := by
    exact le_trans first' (le_congr (.eqRefl _) (by unfold L; ipra_ring) second)
  have p := GaussianPolynomialPerturbation.power_positive (rateDenominator d) J (GaussianDescentClockArithmetic.rate_positive (Γ := Γ) d)
  have positive := positive_product _ _ (positive_product _ _ p p) (positive_product _ _ hb hb)
  exact (residual_bound_iff _ _ _ _ hf).iffMpr (RationalValueBounds.positive_cancel positive comparison)

/-! The source's initial B=max(1,L1(P(0))) is actually computed. -/

def initialBase (C : PTm n) : PTm n := GaussianRationalL1.baseBound (evaluate C qzero)
def initialNumerator (C : PTm n) : PTm n := RationalIntegerNormalization.positivePart (numeratorOf (initialBase C))
def initialDenominator (C : PTm n) : PTm n := denominatorOf (initialBase C)
def approximateRoot (step : PR 3) (d C e f : PTm n) : PTm n :=
  iterate step d C (clock d (initialNumerator C) (initialDenominator C) e f)

theorem initial_base_spec (C : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (initialBase C) (ZT.ofNat (initialNumerator C)) (initialDenominator C) ⋏
      (RationalArgmin.rationalLE GaussianRationalL1.oneCode (initialBase C) ⋏
        RationalArgmin.rationalLE (GaussianRationalL1.qL1 (evaluate C qzero)) (initialBase C)) :=
  .andI (GaussianRationalL1.base_natural_representation _) (GaussianRationalL1.base_bounds _)

@[simp] theorem subst_initialBase {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (initialBase C) = initialBase (Syn.subst σ C) := by simp [initialBase]
@[simp] theorem subst_initialNumerator {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (initialNumerator C) = initialNumerator (Syn.subst σ C) := by simp [initialNumerator]
@[simp] theorem subst_initialDenominator {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    Syn.subst σ (initialDenominator C) = initialDenominator (Syn.subst σ C) := by simp [initialDenominator]
@[simp] theorem subst_approximateRoot {m : ℕ} (σ : Fin n → PTm m) (step : PR 3) (d C e f : PTm n) :
    Syn.subst σ (approximateRoot step d C e f) = approximateRoot step (Syn.subst σ d) (Syn.subst σ C)
      (Syn.subst σ e) (Syn.subst σ f) := by simp [approximateRoot]

def result (C z e f : PTm n) : Fm PTm n := canonical z ⋏ GaussianRationalMetric.bounded (evaluate C z) e f
@[simp] theorem subst_result {m : ℕ} (σ : Fin n → PTm m) (C z e f : PTm n) :
    (result C z e f).subst σ = result (Syn.subst σ C) (Syn.subst σ z) (Syn.subst σ e) (Syn.subst σ f) := by simp [result]

/-- Only the local RD contraction remains a substantive contract. The
initial base, all clocks and the final residual bound are computed/proved. -/
theorem approximate_root (step : PR 3) (d C e f : PTm n)
    (hRD : Γ ⊢[PRAAx] localRD step d C) (he : Γ ⊢[PRAAx] le one e) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] result C (approximateRoot step d C e f) e f :=
  .andI (iterate_canonical _ _ _ _)
    (clock_residual step d C (initialNumerator C) (initialDenominator C) e f
      (RationalArgmin.denominator_positive _) he hf (GaussianRationalL1.initial_bounded _) hRD)

def approximateRootF (step : PR 3) : PR 4 := PTm.toPR (approximateRoot step (var 0) (var 1) (var 2) (var 3))
def run (step : PR 3) (d C e f : PTm n) : PTm n := PTm.app (approximateRootF step) ![d,C,e,f]

theorem program_at (step : PR 3) (d C e f : PTm n) : Γ ⊢[PRAAx] run step d C e f ≐ approximateRoot step d C e f := by
  simpa [run,approximateRootF] using toPR_eq (Γ := Γ) (approximateRoot step (var 0) (var 1) (var 2) (var 3) : PTm 4) ![d,C,e,f]

theorem program_correct (step : PR 3) (d C e f : PTm n)
    (hRD : Γ ⊢[PRAAx] localRD step d C) (he : Γ ⊢[PRAAx] le one e) (hf : Γ ⊢[PRAAx] le one f) :
    Γ ⊢[PRAAx] result C (run step d C e f) e f := by
  have p := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (result (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![C,approximateRoot step d C e f,e,f] ![C,run step d C e f,e,f]
    (fun i => by fin_cases i; exact .eqRefl _; exact (program_at step d C e f).eqSymm; exact .eqRefl _; exact .eqRefl _)
    (by simpa using approximate_root step d C e f hRD he hf)
  simpa using p

theorem conditional_approximate_root_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ localRD step (var 0) (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
      result (var 1) (run step (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (program_correct _ _ _ _ _ hyp2 Prf.hyp1 (le_trans Prf.hyp1 Prf.hyp0))))))

theorem approximate_root_program_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run step (var 0) (var 1) (var 2) (var 3) ≐ approximateRoot step (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _ _)

theorem computed_initial_base_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalArithmetic.represents (initialBase (var 0)) (ZT.ofNat (initialNumerator (var 0))) (initialDenominator (var 0)) ⋏
      (RationalArgmin.rationalLE GaussianRationalL1.oneCode (initialBase (var 0)) ⋏
        RationalArgmin.rationalLE (GaussianRationalL1.qL1 (evaluate (var 0) qzero)) (initialBase (var 0)))) :=
  closeUniv 1 (initial_base_spec _)

theorem computed_global_decay_closed (step : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (localRD step (var 0) (var 1) ⟶
      decay step (var 0) (var 1) (initialNumerator (var 1)) (initialDenominator (var 1)) (var 2)) :=
  closeUniv 3 (.impI (iterate_decay _ _ _ _ _ _ (RationalArgmin.denominator_positive _)
    (GaussianRationalL1.initial_bounded _) Prf.hyp0))

/-! The human RD routine returns an increment Δ. This fixed adapter makes
the actual iterate update literally z+Δ, without an update-law premise. -/

def incrementTerm (descent : PR 3) (d C z : PTm n) : PTm n := GaussianRationalHorner.qadd z (ap3 descent d C z)
@[simp] theorem subst_incrementTerm {m : ℕ} (σ : Fin n → PTm m) (descent : PR 3) (d C z : PTm n) :
    Syn.subst σ (incrementTerm descent d C z) = incrementTerm descent (Syn.subst σ d) (Syn.subst σ C) (Syn.subst σ z) := by
  simp [incrementTerm]
def incrementStep (descent : PR 3) : PR 3 := PTm.toPR (incrementTerm descent (var 0) (var 1) (var 2))

theorem increment_step_at (descent : PR 3) (d C z : PTm n) : Γ ⊢[PRAAx]
    ap3 (incrementStep descent) d C z ≐ GaussianRationalHorner.qadd z (ap3 descent d C z) := by
  change Γ ⊢[PRAAx] PTm.app (incrementStep descent) ![d,C,z] ≐ incrementTerm descent d C z
  simpa [incrementStep] using toPR_eq (Γ := Γ) (incrementTerm descent (var 0) (var 1) (var 2) : PTm 3) ![d,C,z]

theorem advance_increment (descent : PR 3) (d C z : PTm n) : Γ ⊢[PRAAx]
    advance (incrementStep descent) d C z ≐ GaussianRationalHorner.qadd z (ap3 descent d C z) := by
  have e := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (canonicalize (var 0) : PTm 1)
    (σ := ![ap3 (incrementStep descent) d C z]) (σ' := ![GaussianRationalHorner.qadd z (ap3 descent d C z)])
    (fun i => by fin_cases i; exact increment_step_at descent d C z)
  have same : Γ ⊢[PRAAx] advance (incrementStep descent) d C z ≐
      canonicalize (GaussianRationalHorner.qadd z (ap3 descent d C z)) := by simpa [advance] using e
  exact same.eqTrans (canonicalize_exact _ (GaussianRationalHorner.qadd_canonical _ _))

theorem actual_increment_iteration_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (iterate (incrementStep descent) (var 0) (var 1) (succ (var 2)) ≐
      GaussianRationalHorner.qadd (iterate (incrementStep descent) (var 0) (var 1) (var 2))
        (ap3 descent (var 0) (var 1) (iterate (incrementStep descent) (var 0) (var 1) (var 2)))) :=
  closeUniv 3 ((iterate_succ _ _ _ _).eqTrans (advance_increment _ _ _ _))

theorem conditional_descent_clock_closed (descent : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ localRD (incrementStep descent) (var 0) (var 1) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
      result (var 1) (run (incrementStep descent) (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) :=
  conditional_approximate_root_closed _

end LeanProofs.IPRA.Analysis.GaussianDescentClock

import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactorApartness
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadSplit
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductApartness
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Taylor.GaussianGammaShiftedDeflatedZero

/-!
# Constructive zero or apartness test for a finite Barnes product

The bounded test searches the native translated numerators at exactly
the factors in the original range. A hit forces every original head
observation to vanish. A failed test gives a uniform lower bound at a
specified observation of the same head program.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadApartness

open_ipra
open GaussianBarnesCanonicalHead (source parameters body factor_at nameF data)
open GaussianBarnesCanonicalFactorApartness (minimumClock denominator_positive)
open GaussianBarnesCanonicalBase (base_zero)
open GaussianGammaEulerHeadLower (translated)
open GaussianGammaPoleZeros (poleNumerator translated_pole_numerator)
open GaussianNamedFiniteProductFamily (rowF)
open GaussianNamedFiniteProductApartness (rowLowerAt sample_lower apartClock clock_budget weaken_margin)
open GaussianNameReciprocal (lower apart anchor lower_congr)
open GaussianCoefficientNameBounds (unit)
open ComplexLogarithmRemainder (normSq normSq_neg normSq_scale normSq_one zeroCode)
open GaussianRationalHorner (positive_product qzero)
open GaussianRootAlgebra (equal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Factor" => GaussianBarnesCanonicalFactor.nameF
local notation "rows" => rowF Factor body

def rowDenominator (R B N r : PTm n) : PTm n :=
  GaussianBarnesCanonicalFactorApartness.denominator R (B*succ (N+r)) (N+r)

def clock (R B N r : PTm n) : PTm n :=
  minimumClock R+apartClock r (rowDenominator R B N r)

def allNonzero (z B N r : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift r) ⟶ le one (normSq (translated (Syn.shift z) (Syn.shift B) (succ (Syn.shift N+var 0)))))

def allZero (z R B N r : PTm n) : Fm PTm n := .all
  (ap2 nameF (var 0) (data (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) (Syn.shift r)) ≐ qzero)

def testBody : PTm 4 := normSq (translated (var 1) (var 2) (succ (var 3+var 0)))
def search (z B N r : PTm n) : PTm n := Search.Finite.mu testBody r ![z,B,N]

def hit (z B N r : PTm n) : Fm PTm n :=
  lt (search z B N r) r ⋏ equal (translated z B (succ (N+search z B N r))) zeroCode

@[simp] theorem subst_search {m : ℕ} (σ : Fin n → PTm m) (z B N r : PTm n) :
    Syn.subst σ (search z B N r) = search (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp only [search,Search.Finite.subst_mu]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem subst_rowDenominator {m : ℕ} (σ : Fin n → PTm m) (R B N r : PTm n) :
    Syn.subst σ (rowDenominator R B N r) =
      rowDenominator (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [rowDenominator]

@[simp] theorem subst_allNonzero {m : ℕ} (σ : Fin n → PTm m) (z B N r : PTm n) :
    (allNonzero z B N r).subst σ = allNonzero (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [allNonzero,Syn.subst_shift,Syn.shift_subst,one]

private theorem row_den_positive (R B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (rowDenominator R B N r) :=
  denominator_positive _ _ _ (positive_product _ _ hB (zero_lt_succ _))

private theorem nonzero_at (z B N r i : PTm n)
    (h : Γ ⊢[PRAAx] allNonzero z B N r) (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] le one (normSq (translated z B (succ (N+i)))) := by
  have w : Γ ⊢[PRAAx] lt i r ⟶ le one (normSq (translated z B (succ (N+i)))) := by
    simpa [allNonzero,one] using h.allE i
  exact .impE w hi

private theorem row_lower (p z R B N r i : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] lt i r) (hz : Γ ⊢[PRAAx] le one (normSq (translated z B (succ (N+i)))))
    (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap3 rows p i (parameters z R B N)) (rowDenominator R B N r) := by
  let k := succ (N+i)
  have hK : Γ ⊢[PRAAx] le k (N+r) :=
    le_congr ((add_comm (succ i) N).eqTrans (add_succ N i)) (add_comm r N) (add_le_add_right N hi)
  have hD := positive_product _ _ h.andE₁ (zero_lt_succ (N+i))
  have hd' : Γ ⊢[PRAAx] le (B*k) (B*succ (N+r)) :=
    mul_le_mul_left B (le_trans hK (le_succ_self (N+r)))
  have order : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalFactorApartness.denominator R (B*k) k)
      (rowDenominator R B N r) := mul_le_mul_right (two*GaussianCyclicExponentialSamples.sampleBound
      (GaussianBarnesCanonicalFactor.exponentRadius R))
    (le_trans (pw_le_pw k hd')
      (GaussianFactorBudget.power_monotone_length (B*succ (N+r)) k (N+r)
        (positive_product _ _ h.andE₁ (zero_lt_succ _)) hK))
  have native := GaussianBarnesCanonicalFactorApartness.sample_lower p z R B k
    (.andI h.andE₁ (.andI (zero_lt_succ _) h.andE₂)) hz hp
  exact lower_congr (factor_at p i z R B N).eqSymm (.eqRefl _)
    (weaken_margin _ _ _ (denominator_positive R (B*k) k hD) order native)

theorem original_apart (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] allNonzero z B N r) : Γ ⊢[PRAAx] apart nameF (clock R B N r) (data z R B N r) := by
  let H := clock R B N r
  let D := rowDenominator R B N r
  let x := parameters z R B N
  let p := anchor H
  let s := GaussianNamedFiniteProductName.clock r (GaussianNamedFiniteProductFamily.radius Factor body r x) one p
  have hD := row_den_positive R B N r h.andE₁
  have hs : Γ ⊢[PRAAx] le (minimumClock R) s :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have low : Γ ⊢[PRAAx] rowLowerAt rows s r D x := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
    have h' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have hz' : Δ ⊢[PRAAx] allNonzero (sh z) (sh B) (sh N) (sh r) := by
      simpa only [Fm.shift,sh,Δ,Syn.shift,subst_allNonzero] using hz.shift.wk
    have hs' : Δ ⊢[PRAAx] le (minimumClock (sh R)) (sh s) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift.wk
    simpa only [Syn.shift,sh,Δ,x,D,subst_rowDenominator,GaussianBarnesCanonicalHead.subst_parameters] using
      row_lower (sh s) (sh z) (sh R) (sh B) (sh N) (sh r) (var 0) h' Prf.hyp0
        (nonzero_at _ _ _ _ _ hz' Prf.hyp0) hs'
  have hU : Γ ⊢[PRAAx] le (GaussianNamedFiniteProductApartness.denominator D r) (unit H) :=
    le_trans (clock_budget r D)
    (GaussianBalancedRadiusArithmetic.unit_monotone (apartClock r D) H (le_add_left _ _))
  exact weaken_margin _ _ _ (GaussianNamedFiniteProductApartness.denominator_positive D r hD) hU
    (lower_congr (GaussianBarnesCanonicalHead.sample_at p z R B N r).eqSymm (.eqRefl _)
      (sample_lower rows s r D x hD low))

private theorem test_at (z B N i : PTm n) :
    Search.Finite.applyBody testBody i ![z,B,N] = normSq (translated z B (succ (N+i))) := by
  simp [Search.Finite.applyBody,testBody]

private theorem returned_hit (z B N r : PTm n) (h : Γ ⊢[PRAAx] lt (search z B N r) r) :
    Γ ⊢[PRAAx] hit z B N r := by
  let i := search z B N r
  have w := Prf.impE (Search.Finite.search_spec (Γ := Γ) testBody r i ![z,B,N]).andE₂.andE₁ h
  rw [test_at] at w
  exact .andI h (GaussianGammaShiftedDeflatedZero.zero_native _ w)

private theorem failed_nonzero (z B N r : PTm n) (h : Γ ⊢[PRAAx] search z B N r ≐ r) :
    Γ ⊢[PRAAx] allNonzero z B N r := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have h' : Δ ⊢[PRAAx] search (sh z) (sh B) (sh N) (sh r) ≐ sh r := by
    simpa only [Fm.shift,Syn.shift,sh,Δ,Fm.subst_eq,subst_search] using h.shift.wk
  have hi : Δ ⊢[PRAAx] lt i (search (sh z) (sh B) (sh N) (sh r)) := lt_congr (.eqRefl _) h'.eqSymm Prf.hyp0
  have w := Prf.impE (Search.Finite.search_spec (Γ := Δ) testBody (sh r) i ![sh z,sh B,sh N]).andE₂.andE₂ hi
  rw [test_at] at w
  exact Foundations.BoundedReflection.compl_of_ne w

theorem original_zero (z R B N r : PTm n) (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] hit z B N r) :
    Γ ⊢[PRAAx] allZero z R B N r := by
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] hit (sh z) (sh B) (sh N) (sh r) := by
    simpa [hit,Fm.shift,Syn.shift,sh,Δ] using h.shift
  have hB' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hB.shift
  exact GaussianBarnesCanonicalHeadSplit.zero_at_factor (var 0) (sh z) (sh R) (sh B) (sh N) (sh r)
    (search (sh z) (sh B) (sh N) (sh r)) h'.andE₁ (base_zero _ _ _ hB' (zero_lt_succ _) h'.andE₂)

/-- An explicitly encoded negative integer vanishes whenever its index is in the range. -/
theorem negative_integer_at (p R B N r i : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] ap2 nameF p (data (poleNumerator B (succ (N+i))) R B N r) ≐ qzero :=
  GaussianBarnesCanonicalHeadSplit.zero_at_factor p _ R B N r i hi
    (base_zero _ B (succ (N+i)) hB (zero_lt_succ _) (translated_pole_numerator B (succ (N+i))))

/-- Every negative integer on the admitted disk has index at most its radius. -/
theorem negative_integer_index (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hz : Γ ⊢[PRAAx] equal z (poleNumerator B k)) : Γ ⊢[PRAAx] le k R := by
  have norm : Γ ⊢[PRAAx] normSq z ≐ (B*k)*(B*k) :=
    (GaussianRootAlgebra.normSq_equal hz).eqTrans ((normSq_neg _).eqTrans ((normSq_scale _ _).eqTrans
      ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))))
  have comparison := nat_sqrt_mono (le_congr norm (.eqRefl _) h.andE₂)
  exact RationalValueBounds.positive_cancel h.andE₁ (le_congr (.eqRefl _) (mul_comm _ _) comparison)

/-- A head covering the radius contains all negative integer inputs in the disk. -/
theorem initial_negative_integer_at (p z R B r k : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hR : Γ ⊢[PRAAx] le R r) (hk : Γ ⊢[PRAAx] le one k)
    (hz : Γ ⊢[PRAAx] equal z (poleNumerator B k)) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B zero r) ≐ qzero := by
  let i := pred k
  have e : Γ ⊢[PRAAx] k ≐ succ i := AnalyticNumberTheory.PNTStageStep.pos_of_one_le hk
  have hi : Γ ⊢[PRAAx] lt i r := le_congr e (.eqRefl _) (le_trans (negative_integer_index z R B k h hz) hR)
  have index := (congrSucc (zero_add i)).eqTrans e.eqSymm
  have v : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.base z B (succ (zero+i)) ≐ GaussianBarnesCanonicalFactor.base z B k := by
    simpa only [GaussianBarnesCanonicalFactor.subst_base,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianBarnesCanonicalFactor.base (Syn.shift z) (Syn.shift B) (var 0)) index
  exact GaussianBarnesCanonicalHeadSplit.zero_at_factor p z R B zero r i hi
    (v.eqTrans (GaussianBarnesCanonicalBase.base_at_negative_integer z B k h.andE₁ hk hz))

theorem original_zero_or_apart (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] ((hit z B N r ⋏ allZero z R B N r) ⋎ apart nameF (clock R B N r) (data z R B N r)) := by
  have spec := Search.Finite.search_spec (Γ := Γ) testBody r zero ![z,B,N]
  refine .orE (lt_or_eq_of_le spec.andE₁) ?_ ?_
  · have hs : lt (search z B N r) r :: Γ ⊢[PRAAx] hit z B N r := returned_hit z B N r Prf.hyp0
    exact .orI₁ (.andI hs (original_zero z R B N r h.andE₁.wk hs))
  · exact .orI₂ (original_apart z R B N r h.wk (failed_nonzero z B N r Prf.hyp0))

theorem actual_original_Barnes_finite_zero_or_apart_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) ⟶
      ((hit (var 0) (var 2) (var 3) (var 4) ⋏ allZero (var 0) (var 1) (var 2) (var 3) (var 4)) ⋎
        apart nameF (clock (var 1) (var 2) (var 3) (var 4)) (data (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (original_zero_or_apart _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadApartness

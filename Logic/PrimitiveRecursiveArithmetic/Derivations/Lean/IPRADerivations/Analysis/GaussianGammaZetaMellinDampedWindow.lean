import IPRADerivations.Analysis.GaussianGammaZetaMellinDampedExhaustion
import IPRADerivations.Analysis.GaussianGammaZetaMellinDampedImproper
import IPRADerivations.Analysis.GaussianGammaZetaMellinDampedStrip

/-!
# Shared damped window and the finite Gamma–Dirichlet product

Fix the finite count and a uniform scale gain first. The resulting Euler
cutoff determines the enclosing window. The common raw sample precision
and count can be chosen after that window. The estimate binds the
original transposed damped quadrature to the original finite improper
name and to the product of Gamma and the finite Dirichlet name.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedWindow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerCompactExhaustion (denominator)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinDampedExhaustion (gain gridCount gridPrecision)
open GaussianGammaZetaMellinDampedStrip (dampedBody dampedRow dampedValue damped_index_at)
open GaussianNamedFiniteSumFamily (finite term_at sample_at)
open GaussianNameEquivalence (cross_at)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "Damped" => GaussianEulerPositiveScalingImproper.nameF

def cutoff (p N G : PTm n) : PTm n := exponent (N*G) p
def rowClock (p N : PTm n) : PTm n := exponent N p
def clock (p N T : PTm n) : PTm n := gridPrecision (rowClock p N) T

def rowSource (N p z R B A a C E T G M i : PTm n) : Fm PTm n :=
  GaussianGammaZetaMellinDampedExhaustion.source z R B A (cutoff p N G) (succ i) a C E T ⋏
    (le (gain z R B A (succ i)) G ⋏ le (gridCount (rowClock p N) R (succ i) E T) M)

def source (N p z R B A a C E T G M : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    rowSource (Syn.shift N) (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
      (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift G) (Syn.shift M) (var 0))

@[simp] theorem subst_rowSource {m : ℕ} (σ : Fin n → PTm m) (N p z R B A a C E T G M i : PTm n) :
    (rowSource N p z R B A a C E T G M i).subst σ =
      rowSource (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
        (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T)
        (Syn.subst σ G) (Syn.subst σ M) (Syn.subst σ i) := by
  simp [rowSource,cutoff,rowClock,gain,gridCount,GaussianEulerCompactExhaustion.budget,
    GaussianEulerPositiveScalingConstant.inverseBound,one]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (N p z R B A a C E T G M : PTm n) :
    (source N p z R B A a C E T G M).subst σ =
      source (Syn.subst σ N) (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
        (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T)
        (Syn.subst σ G) (Syn.subst σ M) := by
  simp [source,Syn.subst_shift,Syn.shift_subst]

def rowNumerator (s k G : PTm n) : PTm n := G*unit s+num 8*denominator k
def rowDenominator (s k : PTm n) : PTm n := denominator k*unit s

private theorem row_error (s q M z R B A k c a C E T G : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaZetaMellinDampedExhaustion.source z R B A k c a C E T)
    (hM : Γ ⊢[PRAAx] le one M) (hq : Γ ⊢[PRAAx] le (gridPrecision s T) q)
    (hmesh : Γ ⊢[PRAAx] le (gridCount s R c E T) M)
    (hg : Γ ⊢[PRAAx] le (gain z R B A c) G) : Γ ⊢[PRAAx]
    distanceBounded
      (GaussianCompactRiemannName.quadrature GaussianEulerPositiveScalingIntegrand.evaluatorF q M a C E
        (GaussianEulerPositiveScalingIntegrand.fixedData z B c one))
      (ap2 Damped s (GaussianEulerPositiveScalingImproper.data z R B A c one))
      (rowNumerator s k G) (rowDenominator s k) := by
  let U := unit s
  let V := unit (s+num 6)
  let D := denominator k
  have hU : Γ ⊢[PRAAx] le U V :=
    GaussianCompactRiemannName.dyadic_monotone s (s+num 6) (le_add_right _ _)
  have hD : Γ ⊢[PRAAx] le one D := unit_positive _
  refine distance_radius_mono _ _ _ _ (rowNumerator s k G) (rowDenominator s k)
    (positive_product _ _ (unit_positive (s+num 6)) (GaussianNamedInverseRate.denominator_positive D s s hD))
    (positive_product _ _ hD (unit_positive s)) ?_
    (GaussianGammaZetaMellinDampedExhaustion.original_grid_observations s q s M z R B A k c a C E T h hM hq hmesh)
  change Γ ⊢[PRAAx] le ((num 6*(D*U*U)+(gain z R B A c*U*U+D*(U+U))*V)*(D*U))
    ((G*U+num 8*D)*(V*(D*U*U)))
  unfold num
  ipra_le 6*𝔞(D)*𝔞(D)*𝔞(U)*𝔞(U)*sl hU + 𝔞(V)*𝔞(D)*𝔞(U)*𝔞(U)*𝔞(U)*sl hg

private theorem row_source_at (N p z R B A a C E T G M i : PTm n)
    (h : Γ ⊢[PRAAx] source N p z R B A a C E T G M) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] rowSource N p z R B A a C E T G M i := by
  have openRow := h.allE i
  exact .impE (by simpa only [source,Fm.subst_imp,subst_lt,subst_rowSource,Syn.subst_var,Syn.inst_zero,
    Syn.subst_inst_shift] using openRow) hi

private theorem sum_budget (p N G : PTm n) : Γ ⊢[PRAAx]
    le ((N*rowNumerator (rowClock p N) (cutoff p N G) G)*unit p)
      (num 9*rowDenominator (rowClock p N) (cutoff p N G)) := by
  let s := rowClock p N
  let k := cutoff p N G
  let D := denominator k
  have first : Γ ⊢[PRAAx] le ((N*G)*unit p) D :=
    le_trans (query_budget (N*G) p) (GaussianCompactRiemannName.dyadic_monotone k (k+num 6) (le_add_right _ _))
  have second : Γ ⊢[PRAAx] le (N*unit p) (unit s) := query_budget N p
  change Γ ⊢[PRAAx] le (N*(G*unit s+num 8*D)*unit p) (num 9*(D*unit s))
  unfold num
  ipra_le 𝔞(unit s)*sl first + 8*𝔞(D)*sl second

theorem finite_improper_error (p N z R B A a C E T G M : PTm n)
    (h : Γ ⊢[PRAAx] source N p z R B A a C E T G M) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (dampedValue (clock p N T) z B M N a C E)
      (ap2 GaussianGammaZetaMellinDampedImproper.nameF p (GaussianGammaZetaMellinDampedImproper.data N z R B A)) (num 9) (unit p) := by
  let s := rowClock p N
  let k := cutoff p N G
  let L := GaussianGammaZetaMellinStrip.data (clock p N T) z B M N a C E
  let D := GaussianGammaZetaMellinDampedImproper.parameters z R B A
  let Body := GaussianNamedFiniteSumFamily.body Damped GaussianGammaZetaMellinDampedImproper.dampedBody
  let U := rowNumerator s k G
  let V := rowDenominator s k
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (unit_positive _) (unit_positive _)
  have rows : Γ ⊢[PRAAx] termsDistance dampedBody Body N L (pairT s D) U V := by
    refine .allI (.impI ?_)
    let sh (x : PTm n) := Syn.shift x
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    let j : PTm (n+1) := var 0
    have hs : Δ ⊢[PRAAx] source (sh N) (sh p) (sh z) (sh R) (sh B) (sh A)
        (sh a) (sh C) (sh E) (sh T) (sh G) (sh M) := by
      simpa only [Fm.shift,subst_source,Syn.shift,sh,Δ] using h.shift.wk
    have hMs : Δ ⊢[PRAAx] le one (sh M) := by
      simpa only [Fm.shift,subst_le,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
        using hM.shift.wk
    have row := row_source_at _ _ _ _ _ _ _ _ _ _ _ _ j hs (Prf.hyp0)
    let S := rowClock (sh p) (sh N)
    let Q := clock (sh p) (sh N) (sh T)
    let K := cutoff (sh p) (sh N) (sh G)
    have e := row_error S Q (sh M) (sh z) (sh R) (sh B) (sh A) K (succ j) (sh a) (sh C) (sh E) (sh T)
      (sh G) row.andE₁ hMs (le_refl Q) row.andE₂.andE₂ row.andE₂.andE₁
    have left := damped_index_at (Γ := Δ) j Q (sh z) (sh B) (sh M) (sh N) (sh a) (sh C) (sh E)
    have right := (term_at (Γ := Δ) Damped GaussianGammaZetaMellinDampedImproper.dampedBody j S (GaussianGammaZetaMellinDampedImproper.parameters (sh z) (sh R) (sh B) (sh A))).eqTrans
      (congrAp2 Damped (.eqRefl S) (GaussianGammaZetaMellinDampedImproper.damped_at j (sh z) (sh R) (sh B) (sh A)))
    change Δ ⊢[PRAAx] distanceBounded (inst2 dampedBody j (sh L)) (inst2 Body j (sh (pairT s D)))
      (sh U) (sh V)
    simpa only [Body,L,D,U,V,s,k,sh,Syn.shift,clock,gridPrecision,GaussianCompactRiemannName.precision,rowClock,cutoff,
      rowNumerator,rowDenominator,denominator,GaussianGammaZetaMellinStrip.subst_data,GaussianGammaZetaMellinDampedImproper.subst_parameters,
      GaussianFastValueCut.subst_exponent,GaussianCoefficientNameBounds.subst_unit,LeanProofs.IPRA.PTm.subst_num,
      subst_pairT,PTm.subst_mul,PTm.subst_add,j,Q,S,K,dampedRow] using
      distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) e
  have summed := sum_distance dampedBody Body N L (pairT s D) U V hV rows
  have narrowed := distance_radius_mono _ _ _ _ (num 9) (unit p) hV (unit_positive p) (sum_budget p N G) summed
  exact distance_congr (.eqRefl _) (sample_at Damped GaussianGammaZetaMellinDampedImproper.dampedBody p N D).eqSymm (.eqRefl _) (.eqRefl _) narrowed

/-- Compare the literal original strip sum to the genuine finite Dirichlet product name. -/
theorem finite_gamma_dirichlet_error (p r N z R B A a C E T G M : PTm n)
    (h : Γ ⊢[PRAAx] source N p z R B A a C E T G M) (hM : Γ ⊢[PRAAx] le one M)
    (hz : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A) :
    Γ ⊢[PRAAx] distanceBounded (dampedValue (clock p N T) z B M N a C E)
      (ap2 GaussianGammaZetaMellinDampedImproper.gammaProductF r (GaussianGammaZetaMellinDampedImproper.gammaProductData N z R B A))
      (num 9*(unit p*unit r)+(unit p+unit r)*unit p) (unit p*(unit p*unit r)) :=
  GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive _)
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (finite_improper_error p N z R B A a C E T G M h hM)
    (cross_at GaussianGammaZetaMellinDampedImproper.nameF GaussianGammaZetaMellinDampedImproper.gammaProductF _ _ p r (GaussianGammaZetaMellinDampedImproper.finite_gamma_dirichlet N z R B A hz))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedWindow

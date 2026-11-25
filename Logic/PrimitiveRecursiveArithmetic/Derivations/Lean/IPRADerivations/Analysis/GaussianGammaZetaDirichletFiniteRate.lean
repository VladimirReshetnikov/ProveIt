import IPRADerivations.Analysis.GaussianGammaZetaDirichletTail
import IPRADerivations.Analysis.GaussianNamedInverseRate

/-!
# Independent observations of sufficiently long Dirichlet prefixes

The actual prefix names retain their own row clocks. A separate late
common clock is used to sum the geometric tail. Finite rational
slack removal leaves only the two ordinary observation allowances.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletFiniteRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerPositiveScalingConstant (inverseF)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletRowDecay (block)
open GaussianGammaZetaDirichletBlock (value)
open GaussianGammaZetaMellinDampedImproper (dirichletF dirichletBody dirichlet_rows_regular parameters data)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def prefixData (N z R B A : PTm n) : PTm n := data N (shifted z B) (R+one) B A
def budget (A : PTm n) : PTm n := num 4*unit A

@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (N z R B A : PTm n) :
    Syn.subst σ (prefixData N z R B A) =
      prefixData (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [prefixData,one]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (A : PTm n) :
    Syn.subst σ (budget A) = budget (Syn.subst σ A) := by simp [budget]

theorem prefix_observation_error (p k N z R B A : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 dirichletF p (prefixData N z R B A)) (value k N z R B A)
      (unit k+N*unit p) (unit p*unit k) := by
  let x := parameters (shifted z B) (R+one) B A
  let s := GaussianFastValueCut.exponent N p
  let P := unit p
  let K := unit k
  let U := unit s
  have rows := dirichlet_rows_regular N (shifted z B) (R+one) B A
    (GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz)
  have d := GaussianNamedFiniteSumFamily.finite_distance inverseF dirichletBody s k N x rows
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  have g : Γ ⊢[PRAAx] le (N*P) U := GaussianFastValueCut.query_budget N p
  have norm := distance_radius_mono _ _ _ _ (K+N*P) (P*K)
    (positive_product _ _ (unit_positive s) hk) (positive_product _ _ hp hk)
    (by change Γ ⊢[PRAAx] le ((N*(U+K))*(P*K)) ((K+N*P)*(U*K)); ipra_le 𝔞(K*K)*sl g) d
  exact distance_congr (GaussianNamedFiniteSumFamily.sample_at inverseF dirichletBody p N x).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) norm

private theorem same_clock_error (k N M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) (hM : Γ ⊢[PRAAx] le (block A h) M) :
    Γ ⊢[PRAAx] distanceBounded (value k N z R B A) (value k M z R B A)
      (budget A*unit k+(num 3*N*N+num 3*M*M)*unit h) (unit h*unit k) := by
  let b := value k (block A h) z R B A
  let C := unit A
  let H := unit h
  let K := unit k
  let U := (two*C*K+num 3*N*N*H)+(two*C*K+num 3*M*M*H)
  let D := H*K
  have hd := positive_product _ _ (unit_positive (Γ := Γ) h) (unit_positive k)
  have hl := GaussianGammaZetaDirichletTail.tail_error k N z R B A h hz hN
  have hr := GaussianGammaZetaDirichletTail.tail_error k M z R B A h hz hM
  have d := distance_triangle_same _ b _ _ _ D hd hl (distance_symmetric _ _ _ _ hd hr)
  have e : Γ ⊢[PRAAx] U ≐ budget A*K+(num 3*N*N+num 3*M*M)*H := by unfold U budget; ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) e (.eqRefl _) d

private theorem prefix_slack (p q k N M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) (hM : Γ ⊢[PRAAx] le (block A h) M) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (qsub (ap2 dirichletF p (prefixData N z R B A)) (ap2 dirichletF q (prefixData M z R B A)))
      (rateNumerator (budget A) (unit h) p q) (rateDenominator (unit h) p q)
      (num 3*N*N+num 3*M*M+N+M) k := by
  let P := unit p
  let Q := unit q
  let K := unit k
  let H := unit h
  let L := budget A
  let C := num 3*N*N+num 3*M*M
  let X := ap2 dirichletF p (prefixData N z R B A)
  let Y := ap2 dirichletF q (prefixData M z R B A)
  let U := value k N z R B A
  let V := value k M z R B A
  let D := H*P*Q*K
  let a := (K+N*P)*(H*Q)
  let b := (L*K+C*H)*(P*Q)
  let c := (K+M*Q)*(H*P)
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hK := unit_positive (Γ := Γ) k
  have hH := unit_positive (Γ := Γ) h
  have hd := positive_product _ _ (positive_product _ _ (positive_product _ _ hH hP) hQ) hK
  have left := distance_radius_mono X U (K+N*P) (P*K) a D (positive_product _ _ hP hK) hd
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold a D; ipra_ring)) (prefix_observation_error p k N z R B A hz)
  have middle := distance_radius_mono U V (L*K+C*H) (H*K) b D (positive_product _ _ hH hK) hd
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold b D; ipra_ring)) (same_clock_error k N M z R B A h hz hN hM)
  have right := distance_radius_mono V Y (K+M*Q) (Q*K) c D (positive_product _ _ hQ hK) hd
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by unfold c D; ipra_ring))
    (distance_symmetric _ _ _ _ (positive_product _ _ hQ hK) (prefix_observation_error q k M z R B A hz))
  have ds := distance_triangle_same X V Y (a+b) c D hd (distance_triangle_same X U V a b D hd left middle) right
  have eq : Γ ⊢[PRAAx] a+b+c ≐ rateNumerator L H p q*K+(C+N+M)*(H*P*Q) := by
    unfold a b c rateNumerator
    change Γ ⊢[PRAAx] ((K+N*P)*(H*Q)+(L*K+C*H)*(P*Q)+(K+M*Q)*(H*P)) ≐
      (L*P*Q+H*(P+Q))*K+(C+N+M)*(H*P*Q)
    ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) eq (.eqRefl _) ds

theorem prefix_observations (p q N M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) (hM : Γ ⊢[PRAAx] le (block A h) M) :
    Γ ⊢[PRAAx] distanceBounded (ap2 dirichletF p (prefixData N z R B A)) (ap2 dirichletF q (prefixData M z R B A))
      (rateNumerator (budget A) (unit h) p q) (rateDenominator (unit h) p q) := by
  let x := qsub (ap2 dirichletF p (prefixData N z R B A)) (ap2 dirichletF q (prefixData M z R B A))
  let c := rateNumerator (budget A) (unit h) p q
  let d := rateDenominator (unit h) p q
  let k := num 3*N*N+num 3*M*M+N+M
  have hd : Γ ⊢[PRAAx] le one d :=
    positive_product _ _ (positive_product _ _ (unit_positive h) (unit_positive p)) (unit_positive q)
  exact GaussianRationalSlackRemoval.slack_removal_at x c d k hd
    (prefix_slack p q (GaussianRationalSlackRemoval.precision x c d k) N M z R B A h hz hN hM)

theorem prefix_rate (N M z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) (hM : Γ ⊢[PRAAx] le (block A h) M) :
    Γ ⊢[PRAAx] independentRate dirichletF dirichletF (prefixData N z R B A) (prefixData M z R B A) (budget A) (unit h) := by
  refine .allI (.allI ?_)
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) :=
    by simpa [Fm.shift,Syn.shift,sh] using hz.shift.shift
  have npos : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (block (sh A) (sh h)) (sh N) :=
    by simpa [Fm.shift,Syn.shift,sh] using hN.shift.shift
  have mpos : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (block (sh A) (sh h)) (sh M) :=
    by simpa [Fm.shift,Syn.shift,sh] using hM.shift.shift
  simpa [independentRate,Syn.shift,sh] using
    prefix_observations (var 1) (var 0) (sh N) (sh M) (sh z) (sh R) (sh B) (sh A) (sh h) hs npos mpos

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletFiniteRate

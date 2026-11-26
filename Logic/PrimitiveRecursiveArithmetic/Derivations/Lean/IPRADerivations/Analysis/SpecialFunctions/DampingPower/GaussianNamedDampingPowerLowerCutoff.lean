import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerLowerCutoffSource
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerLowerFinite
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactAlignedSplit
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth

/-!
# Actual named damping lower-cutoff convergence

The ordinary affine quadrature is compared with the existing cofinal
root subdivisions. The exact endpoint norm bounds apply uniformly to
all positive named damping parameters. The final estimate retains the
requested compact observation clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerCutoff

open_ipra
open GaussianNamedDampingPowerLowerCutoffSource (source compact_source rescaled_modulus right_bound)
open GaussianNamedDampingPowerCompact (evaluatorF fixedData nameF data lipschitz compact_input)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianEulerLowerTailRootGrid (timeNumerator timeDenominator)
open GaussianEulerLowerTailPartition (totalWidth)
open GaussianEulerLowerCofinalQuadrature (rootMesh transformed)
open GaussianCompactRiemannName (precision)
open GaussianNamedDampingPowerLowerFinite (rightBody rightEndpoints originalQuadrature original_native_lower_tail_bound)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (F G : PR 2) (s z Rz B A x y C R p q : PTm n) : PTm n :=
  ap2 (nameF F G) s (data z Rz B x y C R one (lowerWidth p q A) (etaDen q A Rz) (top q A Rz))
def radius (s p A Rz : PTm n) : PTm n := A*unit s+unit (height p A Rz)
def denominator (s p A Rz : PTm n) : PTm n := unit (height p A Rz)*unit s

@[simp] private theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (s z Rz B A x y C R p q : PTm n) :
    Syn.subst σ (point F G s z Rz B A x y C R p q) =
      point F G (Syn.subst σ s) (Syn.subst σ z) (Syn.subst σ Rz) (Syn.subst σ B) (Syn.subst σ A)
        (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ C) (Syn.subst σ R) (Syn.subst σ p) (Syn.subst σ q) := by
  simp [point,etaDen,top,height,GaussianGammaIntegralCutoffs.tailCoefficient,one]
@[simp] private theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (s p A Rz : PTm n) :
    Syn.subst σ (radius s p A Rz) = radius (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ Rz) := by
  simp [radius,height,GaussianGammaIntegralCutoffs.tailCoefficient]
@[simp] private theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s p A Rz : PTm n) :
    Syn.subst σ (denominator s p A Rz) = denominator (Syn.subst σ s) (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ Rz) := by
  simp [denominator,height,GaussianGammaIntegralCutoffs.tailCoefficient]

private theorem rights (F G : PR 2) (s N p q k z Rz B x y C₀ C R₀ R : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    rightEndpoints (evaluatorF F G) s N p q k Rz (fixedData z B x y) := by
  let sh (a : PTm n) := Syn.shift a
  have ss : Γ.map Fm.shift ⊢[PRAAx] source F G (sh z) (sh Rz) (sh B) (succ (sh k)) (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R) :=
    by simpa only [Fm.shift,Syn.shift,GaussianNamedDampingPowerLowerCutoffSource.subst_source,ConciseIPRA.PTm.subst_succ,sh] using hs.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hN.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] le (sh p) (sh q) := by simpa [Fm.shift,Syn.shift,sh] using hpq.shift
  refine .allI (.impI ?_)
  simpa only [rightEndpoints,GaussianNamedDampingPowerLowerFinite.subst_rightBody,GaussianNamedDampingPowerCompact.subst_fixedData,
    Syn.shift,sh,rightBody] using
    right_bound F G (var 0) (sh s) (sh N) (sh p) (sh q) (sh k) (sh z) (sh Rz) (sh B) (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R)
      ss.wk ns.wk ps.wk Prf.hyp0

private theorem native_bound (F G : PR 2) (t z Rz B k x y C₀ C R₀ R p q : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R) (hpq : Γ ⊢[PRAAx] lt p q) :
    let A := succ k
    let E := etaDen q A Rz
    let T := top q A Rz
    let L := lipschitz Rz C R E T
    Γ ⊢[PRAAx] bounded (transformed (evaluatorF F G) t A (lowerWidth p q A) E L T (fixedData z B x y))
      (GaussianEulerLowerTailFiniteBudget.numerator t p q k Rz L) (GaussianEulerLowerTailFiniteBudget.denominator t p k Rz) := by
  dsimp only
  let A := succ k
  let E := etaDen q A Rz
  let W := lowerWidth p q A
  let T := top q A Rz
  let L := lipschitz Rz C R E T
  let N := rootMesh t L T
  let K := pw N A
  let s := precision t T
  let X := fixedData z B x y
  let J := evaluatorF F G
  have hn := GaussianEulerLowerCofinalQuadrature.root_mesh_positive (Γ := Γ) t L T
  have width := GaussianEulerLowerTailRootGrid.time_width (Γ := Γ) N p q A
  have hK := GaussianPolynomialPerturbation.power_positive (Γ := Γ) N A hn
  have hA : Γ ⊢[PRAAx] le one A := hs.andE₁.andE₂.andE₁
  have hW := GaussianGammaCompactCutoffGeometry.lower_positive p q A hA hpq
  have hw : Γ ⊢[PRAAx] le one (totalWidth N p q A) := le_congr (.eqRefl _) width.eqSymm (positive_product W K hW hK)
  have src : Γ ⊢[PRAAx] GaussianNamedDampingPowerLowerFinite.source J s N p q k Rz L X :=
    .andI hn (.andI (le_of_lt hpq) (.andI hw (.andI
      (rescaled_modulus F G N p q k z Rz B x y C₀ C R₀ R hs hn (le_of_lt hpq))
      (rights F G s N p q k z Rz B x y C₀ C R₀ R hs hn (le_of_lt hpq)))))
  have hp : Γ ⊢[PRAAx] le (unit t) N := by
    unfold N rootMesh
    exact le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L T))
  have later : Γ ⊢[PRAAx] le (unit t) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right t T) (le_add_right _ _))
  have raw := original_native_lower_tail_bound J s t N p q k Rz L X src hp later
  have eq : Γ ⊢[PRAAx] originalQuadrature J s N p q k Rz X ≐ transformed J t A W E L T X :=
    GaussianCompactAlignedSplit.quadrature_congr J (.eqRefl _) width
      (GaussianEulerLowerTailRootGrid.time_first N p q A) width
      (GaussianEulerLowerTailRootGrid.time_denominator N q A Rz) (.eqRefl _)
  exact bound_congr eq (.eqRefl _) (.eqRefl _) raw

theorem original_strict_bound (F G : PR 2) (s z Rz B k x y C₀ C R₀ R p q : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    bounded (point F G s z Rz B (succ k) x y C R p q) (radius s p (succ k) Rz) (denominator s p (succ k) Rz) := by
  let A := succ k
  let E := etaDen q A Rz
  let W := lowerWidth p q A
  let T := top q A Rz
  let L := lipschitz Rz C R E T
  let X := fixedData z B x y
  let J := evaluatorF F G
  let H := unit (height p A Rz)
  let K := GaussianEulerLowerTailFiniteBudget.residual (GaussianEulerLowerTailFiniteBudget.scale p q k) L
  let t := GaussianRationalSlackRemoval.precision (point F G s z Rz B A x y C R p q) (radius s p A Rz) (denominator s p A Rz) (K+two)
  have hA : Γ ⊢[PRAAx] le one A := hs.andE₁.andE₂.andE₁
  have src := compact_source F G z Rz B A x y C₀ C R₀ R p q hs (le_of_lt hpq)
  have hW := GaussianGammaCompactCutoffGeometry.lower_positive p q A hA hpq
  have rn := GaussianCompactRiemannName.name_at (Γ := Γ) J s one W E L T X
  have near := GaussianEulerLowerCofinalQuadrature.observations J t s A W E L T X
    (.andI hA (.andI hW (compact_input F G z Rz B x y C₀ C R₀ R one W E T src)))
  have corr := distance_congr (.eqRefl _) rn.eqSymm (.eqRefl _) (.eqRefl _) near
  have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive s)
  have raw : Γ ⊢[PRAAx] slack (point F G s z Rz B A x y C R p q) (radius s p A Rz) (denominator s p A Rz) (K+two) t :=
    GaussianEulerNamedLowerTail.compared_bound_to_slack _ _ A H K s t (unit_positive (height p A Rz))
      (distance_symmetric _ _ _ _ den corr) (native_bound F G t z Rz B k x y C₀ C R₀ R p q hs hpq)
  exact slack_removal_at _ _ _ _ (positive_product _ _ (unit_positive _) (unit_positive s)) raw

private theorem coincident_bound (F G : PR 2) (s z Rz B A x y C R p q : PTm n) (eq : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] bounded (point F G s z Rz B A x y C R p q) (radius s p A Rz) (denominator s p A Rz) := by
  let E := etaDen q A Rz
  let T := top q A Rz
  let L := lipschitz Rz C R E T
  let X := fixedData z B x y
  let J := evaluatorF F G
  have width : Γ ⊢[PRAAx] lowerWidth p q A ≐ lowerWidth p p A := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (lowerWidth (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,q,A]) (σ' := ![p,p,A]) (fun i => by fin_cases i; exact .eqRefl _; exact eq.eqSymm; exact .eqRefl _)
  have hz := width.eqTrans (GaussianGammaCompactCutoffGeometry.same_lower p A)
  have e : Γ ⊢[PRAAx] point F G s z Rz B A x y C R p q ≐ qzero := by
    let f : Fm PTm (n+1) :=
      ap2 (GaussianCompactRiemannName.nameF J) (Syn.shift s) (GaussianCompactRiemannName.data (Syn.shift one) (var 0)
        (Syn.shift E) (Syn.shift L) (Syn.shift T) (Syn.shift X)) ≐ qzero
    have actual := GaussianCompactZeroWidth.observation_zero (Γ := Γ) J s one E L T X (GaussianGammaIntegralCutoffs.eta_den_positive q A Rz)
    have h : Γ ⊢[PRAAx] f.subst (Syn.inst zero) := by simpa [f] using actual
    simpa [f,point,data] using Prf.eqSubst1 f hz.eqSymm h
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerNamedUpperTail.zero_bound _ _ (positive_product _ _ (unit_positive _) (unit_positive s)))

theorem original_bound (F G : PR 2) (s z Rz B A x y C₀ C R₀ R p q : PTm n)
    (hs : Γ ⊢[PRAAx] source F G z Rz B A x y C₀ C R₀ R) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    bounded (point F G s z Rz B A x y C R p q) (radius s p A Rz) (denominator s p A Rz) := by
  refine .orE (lt_or_eq_of_le hpq) ?_ (coincident_bound F G s z Rz B A x y C R p q Prf.hyp0)
  let Δ := lt p q :: Γ
  let k := LeanProofs.IPRA.PTm.monus A one
  have e : Δ ⊢[PRAAx] succ k ≐ A :=
    (GaussianCompactRiemannName.positive_as_successor A hs.wk.andE₁.andE₂.andE₁).eqSymm
  let sh (a : PTm n) := Syn.shift a
  let f : Fm PTm (n+1) := source F G (sh z) (sh Rz) (sh B) (var 0) (sh x) (sh y) (sh C₀) (sh C) (sh R₀) (sh R) ⟶
    bounded (point F G (sh s) (sh z) (sh Rz) (sh B) (var 0) (sh x) (sh y) (sh C) (sh R) (sh p) (sh q))
      (radius (sh s) (sh p) (var 0) (sh Rz)) (denominator (sh s) (sh p) (var 0) (sh Rz))
  have rule : Δ ⊢[PRAAx] source F G z Rz B (succ k) x y C₀ C R₀ R ⟶
      bounded (point F G s z Rz B (succ k) x y C R p q) (radius s p (succ k) Rz) (denominator s p (succ k) Rz) :=
    .impI (original_strict_bound F G s z Rz B k x y C₀ C R₀ R p q Prf.hyp0 (Prf.hyp0 : Δ ⊢[PRAAx] lt p q).wk)
  have inst : Δ ⊢[PRAAx] f.subst (Syn.inst (succ k)) := by
    simpa only [f,Fm.subst_imp,GaussianNamedDampingPowerLowerCutoffSource.subst_source,GaussianRationalMetric.subst_bounded,
      subst_point,subst_radius,subst_denominator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using rule
  have go : Δ ⊢[PRAAx] source F G z Rz B A x y C₀ C R₀ R ⟶
      bounded (point F G s z Rz B A x y C R p q) (radius s p A Rz) (denominator s p A Rz) := by
    simpa only [f,Fm.subst_imp,GaussianNamedDampingPowerLowerCutoffSource.subst_source,GaussianRationalMetric.subst_bounded,
      subst_point,subst_radius,subst_denominator,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using Prf.eqSubst1 f e inst
  exact go.impE hs.wk

theorem actual_named_lower_cutoff_observations_bounded_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        le (var 11) (var 12) ⟶
        bounded (point F G (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 10) (var 11) (var 12))
          (radius (var 0) (var 11) (var 4) (var 2)) (denominator (var 0) (var 11) (var 4) (var 2))) :=
  closeUniv 13 (.impI (.impI (original_bound F G _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerLowerCutoff

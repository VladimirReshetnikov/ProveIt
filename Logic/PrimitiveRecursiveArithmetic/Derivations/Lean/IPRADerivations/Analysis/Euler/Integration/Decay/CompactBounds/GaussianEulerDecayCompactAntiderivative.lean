import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision

/-!
# Exact compact decay antiderivative

The original compact grid for exp(-t) defines the same name as the
difference of the two original endpoint decay names. This uses the
stated compact clocks and a positive width, with explicit rate
comparison at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactAntiderivative

open_ipra
open GaussianEulerDecayQuadrature (evaluatorF)
open GaussianEulerDecayQuadraturePrecision (endpointDifference independent_quadrature_endpoint numerator denominator)
open GaussianCompactRiemannName (mesh precision sample mesh_cost mesh_positive precision_lower)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def endpointData (a C E : PTm n) : PTm n := pairT a (pairT C E)
def endpointSample (p x : PTm n) : PTm n := endpointDifference (fstT x) (fstT (sndT x)) (sndT (sndT x)) (p+one)
def endpointF : PR 2 := PTm.toPR (endpointSample (var 0) (var 1))

ipra_subst endpointData
ipra_subst endpointSample [endpointDifference]

theorem endpoint_at (p a C E : PTm n) : Γ ⊢[PRAAx]
    ap2 endpointF p (endpointData a C E) ≐ endpointDifference a C E (p+one) := by
  let x := endpointData a C E
  have pg : Γ ⊢[PRAAx] ap2 endpointF p x ≐ endpointSample p x := by
    simpa [endpointF,ap2] using toPR_eq (Γ := Γ) (endpointSample (var 0) (var 1) : PTm 2) ![p,x]
  have aa : Γ ⊢[PRAAx] fstT x ≐ a := fst_pair _ _
  have cc : Γ ⊢[PRAAx] fstT (sndT x) ≐ C := (snd_pair _ _).fstE
  have ee : Γ ⊢[PRAAx] sndT (sndT x) ≐ E := (snd_pair _ _).sndE
  refine pg.eqTrans ?_
  ipra_congr (endpointDifference (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [aa, cc, ee, .eqRefl (p+one)] using [endpointSample, endpointDifference]

private theorem precision_boost (p : PTm n) : Γ ⊢[PRAAx] le (num 6*unit p) (unit (p+num 6)) := by
  have h : Γ ⊢[PRAAx] le (num 6 : PTm n) (unit (num 6)) :=
    le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow (num 6))
  exact le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (pw_add two p (num 6)).eqSymm)
    (mul_le_mul_right (unit p) h)

theorem compact_budget (p q C E L T : PTm n) (hC : Γ ⊢[PRAAx] le C (E*T)) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] le
      (numerator (precision p T) (q+one) (mesh p L T) C E*(unit p*unit q))
      ((unit p+unit q)*denominator (precision p T) (q+one) (mesh p L T) E) := by
  let P := unit p
  let Q := unit q
  let U := unit (precision p T)
  let V := unit (q+one)
  let K := unit (p+num 6)
  let N := mesh p L T
  let B := E*E*N
  have hK : Γ ⊢[PRAAx] le (num 6*P) K := precision_boost p
  have s : Γ ⊢[PRAAx] le (C*C) ((E*T)*(E*T)) := le_mul_mono hC hC
  have t : Γ ⊢[PRAAx] le (K*T*T) N := by
    have b : Γ ⊢[PRAAx] le (K*L*T*T) N := mesh_cost p L T
    ipra_le 𝔞(K*T*T)*sl hL+sl b
  have a : Γ ⊢[PRAAx] le (num 6*C*C*P) B := by
    unfold B
    ipra_le 𝔞(E*E)*sl t+𝔞(C*C)*sl hK+𝔞(K)*sl s
  have k₂ : Γ ⊢[PRAAx] le (two*P) K := by
    ipra_le sl hK+4*𝔞(P)
  have b : Γ ⊢[PRAAx] le (two*C*P) (E*U) := by
    have hU := precision_lower (Γ := Γ) p T
    ipra_le 𝔞(E)*sl hU+𝔞(C)*sl k₂+𝔞(K)*sl hC
  have part : Γ ⊢[PRAAx] le ((num 3*C*C*U*V+C*E*N*V)*P) (B*U*V) := by
    apply mul_le_cancel (d' := one)
    unfold B
    have first : Γ ⊢[PRAAx] le (num 6*C*C*P) (E*E*N) := a
    ipra_le 𝔞(U*V)*sl first+𝔞(E*N*V)*sl b
  have v : Γ ⊢[PRAAx] V ≐ Q*two :=
    (pw_add two q one).eqTrans (congrMul (.eqRefl Q) (pw_one two))
  have ve : 𝔞(V) = 𝔞(Q)*2 := calc
    𝔞(V) = 𝔞(Q*two) := natEq v
    _ = _ := by ipra_simps; ring
  have pBound : Γ ⊢[PRAAx] le ((num 3*C*C*U*V+C*E*N*V)*P) (E*E*N*U*V) := part
  unfold numerator denominator GaussianNameRingLaws.three
  change Γ ⊢[PRAAx] le
    (((two+one)*C*C*U*V+C*E*N*V+two*E*E*N*U)*(P*Q)) ((P+Q)*(E*E*N*U*V))
  ipra_le 𝔞(Q)*sl pBound using linear_combination (𝔞(E)*𝔞(E)*𝔞(N)*𝔞(U)*𝔞(P))*ve

theorem compact_observations (p q a C E L T x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le one L) (hwidth : Γ ⊢[PRAAx] le C (E*T))
    (hstep : Γ ⊢[PRAAx] le C (E*mesh p L T)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (GaussianCompactRiemannName.nameF evaluatorF) p (GaussianCompactRiemannName.data a C E L T x))
      (ap2 endpointF q (endpointData a C E)) (unit p+unit q) (unit p*unit q) := by
  let N := mesh p L T
  let U := precision p T
  let V := q+one
  have hN := mesh_positive (Γ := Γ) p L T
  have hD : Γ ⊢[PRAAx] le one (denominator U V N E) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _
      (positive_product E E hE hE) hN) (unit_positive U)) (unit_positive V)
  have h := independent_quadrature_endpoint U V N a C E x ha hN hE hC hstep
  exact distance_congr (GaussianCompactRiemannName.name_at evaluatorF p a C E L T x).eqSymm
    (endpoint_at q a C E).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive p) (unit_positive q))
      (compact_budget p q C E L T hwidth hL) h)

theorem mesh_covers_step (p C E L T : PTm n) (hC : Γ ⊢[PRAAx] le C (E*T))
    (hL : Γ ⊢[PRAAx] le one L) : Γ ⊢[PRAAx] le C (E*mesh p L T) := by
  have Q := GaussianCompactRiemannName.mesh_cost (Γ := Γ) p L T
  have u := unit_positive (Γ := Γ) (p+num 6)
  have h : Γ ⊢[PRAAx] le T (mesh p L T) := by
    refine .orE (le_total T one) ?_ ?_
    · exact le_trans Prf.hyp0 (mesh_positive _ _ _)
    · have T1 : (le one T :: Γ) ⊢[PRAAx] le one T := Prf.hyp0
      have t2 := le_congr (one_mul T) (.eqRefl _) (mul_le_mul_right T T1)
      have k : (le one T :: Γ) ⊢[PRAAx] le one (unit (p+num 6)*L) := positive_product _ _ u.wk hL.wk
      have r : (le one T :: Γ) ⊢[PRAAx] le (T*T) (unit (p+num 6)*L*T*T) :=
        le_congr (one_mul _) (by ipra_ring) (mul_le_mul_right (T*T) k)
      exact le_trans t2 (le_trans r Q.wk)
  exact le_trans hC (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E h))

theorem compact_antiderivative (a C E L T x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le one L) (hwidth : Γ ⊢[PRAAx] le C (E*T)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianCompactRiemannName.nameF evaluatorF) endpointF
      (GaussianCompactRiemannName.data a C E L T x) (endpointData a C E) := by
  have sa : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift a)) := by simpa [Fm.shift,Syn.shift] using ha.shift.shift
  have sc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift C)) := by simpa [Fm.shift,Syn.shift] using hC.shift.shift
  have se : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift E)) := by simpa [Fm.shift,Syn.shift] using hE.shift.shift
  have sl : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift L)) := by simpa [Fm.shift,Syn.shift] using hL.shift.shift
  have sw : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift E)*Syn.shift (Syn.shift T)) := by
    simpa [Fm.shift,Syn.shift] using hwidth.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,GaussianCompactRiemannName.subst_data,subst_endpointData,GaussianEuclideanPointDistance.unit] using
    compact_observations (var 1) (var 0) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift E))
      (Syn.shift (Syn.shift L)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift x)) sa sc se sl sw
      (mesh_covers_step (var 1) _ _ _ _ sw sl)

theorem compact_decay_regular (a C E L T x : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le one L) (hwidth : Γ ⊢[PRAAx] le C (E*T)) :
    Γ ⊢[PRAAx] pointCN (GaussianCompactRiemannName.nameF evaluatorF) (GaussianCompactRiemannName.data a C E L T x) := by
  have e := compact_antiderivative a C E L T x ha hC hE hL hwidth
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem original_compact_decay_antiderivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 0) ⋏ le one (var 1)) ⟶ (le one (var 2) ⋏ le one (var 3)) ⟶
      le (var 1) (var 2*var 4) ⟶ crossEquivalent (GaussianCompactRiemannName.nameF evaluatorF) endpointF
        (GaussianCompactRiemannName.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (endpointData (var 0) (var 1) (var 2))) :=
  closeUniv 6 (.impI (.impI (.impI (compact_antiderivative _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactAntiderivative

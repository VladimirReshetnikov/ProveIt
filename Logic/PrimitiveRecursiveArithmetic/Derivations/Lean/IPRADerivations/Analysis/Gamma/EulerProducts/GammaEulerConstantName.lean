import IPRADerivations.Analysis.Gamma.EulerProducts.GammaEulerMesh
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumName

/-!
# Actual regular Euler-constant and fixed-N mesh names

The fixed-N name observes H_N-(H_(KN)-H_K) at K=4·2^p. The constant
name observes the diagonal 2H_K-H_(K²) at that same explicit mesh.
Exact common-refinement comparisons and synchronous C1 give the named
C2 inequalities, with only the ordinary errors of the two independent
name observations. No unknown logarithm or convergence rate is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GammaEulerConstantName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero app)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (mesh_pair)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open GammaEulerMesh (numerator commonSample sample common_value common_canonical sample_at_common
  factorial_positive factorial_quotient synchronous_samples sample_range)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_mono upper_triangle upper_order_left radius radius_of_upper)
open RationalSupMetric (denominatorOf)
open GaussianRationalSyntheticBounds (natCode)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- An exact factorial quotient turns a cleared difference into the true rational budget. -/
theorem common_quotient_upper (c d : PTm n) (a b : ZT n) (L K : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hL : Γ ⊢[PRAAx] le K L)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c a (fact L))
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d b (fact L))
    (h : Γ ⊢[PRAAx] le (a.pos+b.neg) (a.neg+b.pos+quo (fact L) K)) :
    Γ ⊢[PRAAx] upper c d one K := by
  apply RationalCubeInfimumIntervals.upper_of_representations c d a b (fact L) (fact L) one K
    (factorial_positive L) (factorial_positive L) hc hd
  apply zle_of_toZ (K*fact L*LeanProofs.IPRA.PTm.monus (a.neg+b.pos+quo (fact L) K) (a.pos+b.neg))
  have e := natEq (eq_add_of_le h)
  have q := natEq (factorial_quotient K L hK hL)
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination -𝔞 K*𝔞 (fact L)*e+𝔞 (fact L)*q

/-- Comparing the SAME N at two independently computed meshes. -/
theorem cross_mesh (N K J : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hK : Γ ⊢[PRAAx] le one K) (hJ : Γ ⊢[PRAAx] le one J) : Γ ⊢[PRAAx]
    upper (sample N K) (sample N J) one K ⋏ upper (sample N J) (sample N K) one J := by
  let L := J*(K*N)
  have hkN : Γ ⊢[PRAAx] le (K*N) L := by dsimp only [L]; ipra_le 𝔞 (K*N)*sl hJ
  have hjN : Γ ⊢[PRAAx] le (J*N) L := by dsimp only [L]; ipra_le 𝔞 (J*N)*sl hK
  have kL : Γ ⊢[PRAAx] le K L := by dsimp only [L]; ipra_le 𝔞 K*sl hN+𝔞 (K*N)*sl hJ
  have jL : Γ ⊢[PRAAx] le J L := by dsimp only [L]; ipra_le 𝔞 J*sl hN+𝔞 (J*N)*sl hK
  have a := mesh_pair hK hN hJ (le_refl L)
  have b := mesh_pair (L := L) hJ hN hK (le_of_eq_add (d := zero) (by simp only [L]; ipra_ring))
  have ep : Γ ⊢[PRAAx] S (K*J) (fact L) ≐ S (J*K) (fact L) :=
    congrAp2 (sumF hB) (mul_comm _ _) (.eqRefl _)
  have ef : Γ ⊢[PRAAx] S (K*(J*N)) (fact L) ≐ S L (fact L) :=
    congrAp2 (sumF hB) (by simp only [L]; ipra_ring) (.eqRefl _)
  have b1 := le_congr (congrAdd (.eqRefl _) ep) (congrAdd ef (.eqRefl _)) b.andE₁
  have b2 := le_congr (congrAdd ef (.eqRefl _)) (congrAdd (congrAdd ep (.eqRefl _)) (.eqRefl _)) b.andE₂
  have first : Γ ⊢[PRAAx] upper (commonSample N K L) (commonSample N J L) one K := by
    apply common_quotient_upper _ _ _ _ L K hK kL (common_value N K L) (common_value N J L)
    dsimp only [numerator]
    ipra_le sl a.andE₂+sl b1
  have second : Γ ⊢[PRAAx] upper (commonSample N J L) (commonSample N K L) one J := by
    apply common_quotient_upper _ _ _ _ L J hJ jL (common_value N J L) (common_value N K L)
    dsimp only [numerator]
    ipra_le sl a.andE₁+sl b2
  have ea := sample_at_common N K L hN hK hkN
  have eb := sample_at_common N J L hN hJ hjN
  exact .andI (RationalValueBounds.upper_congr ea eb (.eqRefl _) (.eqRefl _) first)
    (RationalValueBounds.upper_congr eb ea (.eqRefl _) (.eqRefl _) second)

theorem relaxed_synchronous (N M K : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hNM : Γ ⊢[PRAAx] le N M) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] upper (sample N K) (sample M K) one N := by
  have hM := le_trans hN hNM
  have h := (synchronous_samples N M K hN hNM hK).andE₂
  have d : Γ ⊢[PRAAx] le (LeanProofs.IPRA.PTm.monus M N) M :=
    le_congr (.eqRefl _) (eq_add_of_le hNM).eqSymm (le_add_left _ _)
  exact upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product hN hM) h
    (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono d (le_refl N)))

/-- Finite C2 with independent N, diagonal cutoff M and mesh K. -/
theorem fixed_against_diagonal (N M K : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hM : Γ ⊢[PRAAx] le one M) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    upper (sample N K) (sample M M) (N+K) (N*K) ⋏
      upper (sample M M) (sample N K) two M := by
  refine .orE (le_total N M) ?_ ?_
  · have sync := synchronous_samples N M M hN.wk Prf.hyp0 hM.wk
    have mesh := cross_mesh (Γ := le N M :: Γ) N K M hN.wk hK.wk hM.wk
    have f := upper_triangle _ _ _ one K one N mesh.andE₁
      (relaxed_synchronous N M M hN.wk Prf.hyp0 hM.wk)
    have b := upper_order_left _ _ _ _ _ sync.andE₁ mesh.andE₂
    exact .andI (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm _ _) f)
      (upper_mono _ _ _ _ _ _ hM.wk b (le_of_eq_add (d := M) (by ipra_ring)))
  · have sync := synchronous_samples M N K hM.wk Prf.hyp0 hK.wk
    have mesh := cross_mesh (Γ := le M N :: Γ) M K M hM.wk hK.wk hM.wk
    have f := upper_order_left _ _ _ _ _ sync.andE₁ mesh.andE₁
    have b := upper_triangle _ _ _ one M one M mesh.andE₂
      (relaxed_synchronous M N K hM.wk Prf.hyp0 hK.wk)
    exact .andI (upper_mono _ _ _ _ _ _ hK.wk f (le_of_eq_add (d := K*K) (by ipra_ring)))
      (upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product hM.wk hM.wk) b
        (le_of_eq_add (d := zero) (by ipra_ring)))

def unit (p : PTm n) : PTm n := pw two p
def mesh (p : PTm n) : PTm n := num 4*unit p
def fixedValue (p N : PTm n) : PTm n := sample N (mesh p)
def gammaValue (p : PTm n) : PTm n := sample (mesh p) (mesh p)

@[simp] theorem subst_unit {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (unit p) = unit (Syn.subst σ p) := by simp [unit]
@[simp] theorem subst_mesh {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (mesh p) = mesh (Syn.subst σ p) := by simp [mesh]
@[simp] theorem subst_fixedValue {m : ℕ} (σ : Fin n → PTm m) (p N : PTm n) :
    Syn.subst σ (fixedValue p N) = fixedValue (Syn.subst σ p) (Syn.subst σ N) := by simp [fixedValue]
@[simp] theorem subst_gammaValue {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (gammaValue p) = gammaValue (Syn.subst σ p) := by simp [gammaValue]

theorem unit_positive (p : PTm n) : Γ ⊢[PRAAx] le one (unit p) :=
  GaussianFactorBudget.power_positive two p (le_succ_self one)
theorem mesh_positive (p : PTm n) : Γ ⊢[PRAAx] le one (mesh p) := by
  unfold mesh
  ipra_le 4*sl (unit_positive p)+3

theorem fixed_regularity (s t N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    radius (fixedValue s N) (fixedValue t N) (unit s+unit t) (unit s*unit t) := by
  have both := cross_mesh N (mesh s) (mesh t) hN (mesh_positive s) (mesh_positive t)
  apply radius_of_upper _ _ _ _
  · exact upper_mono _ _ _ _ _ _ (mesh_positive s) both.andE₁
      (le_of_eq_add (d := num 4*unit s*unit s+num 3*unit s*unit t) (by unfold mesh; ipra_ring))
  · exact upper_mono _ _ _ _ _ _ (mesh_positive t) both.andE₂
      (le_of_eq_add (d := num 4*unit t*unit t+num 3*unit s*unit t) (by unfold mesh; ipra_ring))

theorem diagonal_upper (N M : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] upper (sample N N) (sample M M) two N :=
  upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product hN hN)
    (fixed_against_diagonal N M N hN hM hN).andE₁ (le_of_eq_add (d := zero) (by ipra_ring))

theorem gamma_regularity (s t : PTm n) : Γ ⊢[PRAAx]
    radius (gammaValue s) (gammaValue t) (unit s+unit t) (unit s*unit t) := by
  apply radius_of_upper _ _ _ _
  · exact upper_mono _ _ _ _ _ _ (mesh_positive s)
      (diagonal_upper _ _ (mesh_positive s) (mesh_positive t))
      (le_of_eq_add (d := num 4*unit s*unit s+two*unit s*unit t) (by unfold mesh; ipra_ring))
  · exact upper_mono _ _ _ _ _ _ (mesh_positive t)
      (diagonal_upper _ _ (mesh_positive t) (mesh_positive s))
      (le_of_eq_add (d := num 4*unit t*unit t+two*unit s*unit t) (by unfold mesh; ipra_ring))

/-- Ordinary cross-observation C2, with its exact constant 1/N. -/
theorem C2_values (N p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper (gammaValue q) (fixedValue p N) (unit p+unit q) (unit p*unit q) ⋏
      upper (fixedValue p N) (gammaValue q)
        (unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) := by
  have bounds := fixed_against_diagonal N (mesh q) (mesh p) hN (mesh_positive q) (mesh_positive p)
  refine .andI ?_ ?_
  · exact upper_mono _ _ _ _ _ _ (mesh_positive q) bounds.andE₂
      (le_of_eq_add (d := two*unit p*unit q+num 4*unit q*unit q) (by unfold mesh; ipra_ring))
  · exact upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product hN (mesh_positive p)) bounds.andE₁
      (le_of_eq_add (d := num 4*N*N*unit p*unit p+num 3*N*N*unit p*unit q) (by unfold mesh; ipra_ring))

def fixedF : PR 2 := PTm.toPR (fixedValue (var 0) (var 1))
def fixedSample (p N : PTm n) : PTm n := ap2 fixedF p N
def gammaF : PR 2 := PTm.toPR (gammaValue (var 0) : PTm 2)
def gammaSample (p x : PTm n) : PTm n := ap2 gammaF p x

@[simp] theorem subst_fixedSample {m : ℕ} (σ : Fin n → PTm m) (p N : PTm n) :
    Syn.subst σ (fixedSample p N) = fixedSample (Syn.subst σ p) (Syn.subst σ N) := by simp [fixedSample]
@[simp] theorem subst_gammaSample {m : ℕ} (σ : Fin n → PTm m) (p x : PTm n) :
    Syn.subst σ (gammaSample p x) = gammaSample (Syn.subst σ p) (Syn.subst σ x) := by simp [gammaSample]

theorem fixed_at (p N : PTm n) : Γ ⊢[PRAAx] fixedSample p N ≐ fixedValue p N := by
  simpa [fixedSample,fixedF,ap2] using toPR_eq (Γ := Γ) (fixedValue (var 0) (var 1) : PTm 2) ![p,N]

theorem gamma_at (p x : PTm n) : Γ ⊢[PRAAx] gammaSample p x ≐ gammaValue p := by
  simpa [gammaSample,gammaF,ap2] using toPR_eq (Γ := Γ) (gammaValue (var 0) : PTm 2) ![p,x]

theorem fixed_samples_regularity (s t N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    radius (fixedSample s N) (fixedSample t N) (unit s+unit t) (unit s*unit t) :=
  RationalValueBounds.radius_congr (fixed_at s N).eqSymm (fixed_at t N).eqSymm (.eqRefl _) (.eqRefl _)
    (fixed_regularity s t N hN)

theorem gamma_samples_regularity (s t x : PTm n) : Γ ⊢[PRAAx]
    radius (gammaSample s x) (gammaSample t x) (unit s+unit t) (unit s*unit t) :=
  RationalValueBounds.radius_congr (gamma_at s x).eqSymm (gamma_at t x).eqSymm (.eqRefl _) (.eqRefl _)
    (gamma_regularity s t)

theorem fixed_name_regular (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] RationalCubeInfimumName.regular fixedF N := by
  refine .allI (.allI ?_)
  have h : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using hN.shift.shift
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,fixedSample,Syn.shift] using
    fixed_samples_regularity (var 1) (var 0) (Syn.shift (Syn.shift N)) h

theorem gamma_name_regular (x : PTm n) : Γ ⊢[PRAAx] RationalCubeInfimumName.regular gammaF x := by
  refine .allI (.allI ?_)
  simpa only [RationalCubeInfimumName.regular,RationalCubeGrid.scale,unit,gammaSample,Syn.shift] using
    gamma_samples_regularity (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (Syn.shift (Syn.shift x))

theorem fixed_sample_range (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (fixedSample p N) ⋏ rationalLE (fixedSample p N) (natCode one) := by
  have h := sample_range N (mesh p) hN (mesh_positive p)
  exact .andI (rationalLE_congr (.eqRefl _) (fixed_at p N).eqSymm h.andE₁)
    (rationalLE_congr (fixed_at p N).eqSymm (.eqRefl _) h.andE₂)

theorem gamma_sample_range (p x : PTm n) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (gammaSample p x) ⋏ rationalLE (gammaSample p x) (natCode one) := by
  have h := sample_range (mesh p) (mesh p) (mesh_positive (Γ := Γ) p) (mesh_positive p)
  exact .andI (rationalLE_congr (.eqRefl _) (gamma_at p x).eqSymm h.andE₁)
    (rationalLE_congr (gamma_at p x).eqSymm (.eqRefl _) h.andE₂)

theorem fixed_sample_canonical (p N : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (fixedSample p N) :=
  RationalCubeMinimum.well_formed_congr (fixed_at p N).eqSymm (common_canonical N (mesh p) (mesh p*N))

theorem gamma_sample_canonical (p x : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (gammaSample p x) :=
  RationalCubeMinimum.well_formed_congr (gamma_at p x).eqSymm (common_canonical (mesh p) (mesh p) (mesh p*mesh p))

def C2At (N p q x : PTm n) : Fm PTm n :=
  upper (gammaSample q x) (fixedSample p N) (unit p+unit q) (unit p*unit q) ⋏
    upper (fixedSample p N) (gammaSample q x)
      (unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q)

theorem C2_samples (N p q x : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] C2At N p q x := by
  have h := C2_values N p q hN
  exact .andI (RationalValueBounds.upper_congr (gamma_at q x).eqSymm (fixed_at p N).eqSymm (.eqRefl _) (.eqRefl _) h.andE₁)
    (RationalValueBounds.upper_congr (fixed_at p N).eqSymm (gamma_at q x).eqSymm (.eqRefl _) (.eqRefl _) h.andE₂)

def C1At (N M p q : PTm n) : Fm PTm n :=
  upper (fixedSample q M) (fixedSample p N) (unit p+unit q) (unit p*unit q) ⋏
    upper (fixedSample p N) (fixedSample q M)
      (LeanProofs.IPRA.PTm.monus M N*(unit p*unit q)+N*M*(unit p+unit q)) (N*M*unit p*unit q)

/-- Sharp C1 survives independent observations of the two fixed-N names. -/
theorem C1_samples (N M p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hNM : Γ ⊢[PRAAx] le N M) : Γ ⊢[PRAAx] C1At N M p q := by
  have hM := le_trans hN hNM
  have sync := synchronous_samples N M (mesh q) hN hNM (mesh_positive q)
  have both := cross_mesh N (mesh p) (mesh q) hN (mesh_positive p) (mesh_positive q)
  have lower := upper_order_left _ _ _ _ _ sync.andE₁ both.andE₂
  have upper := upper_triangle _ _ _ one (mesh p) (LeanProofs.IPRA.PTm.monus M N) (N*M) both.andE₁ sync.andE₂
  refine .andI ?_ ?_
  · exact RationalValueBounds.upper_congr (fixed_at q M).eqSymm (fixed_at p N).eqSymm (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (mesh_positive q) lower
        (le_of_eq_add (d := num 4*unit q*unit q+num 3*unit p*unit q) (by unfold mesh; ipra_ring)))
  · exact RationalValueBounds.upper_congr (fixed_at p N).eqSymm (fixed_at q M).eqSymm (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product (mesh_positive p) (RationalAlgebra.positive_product hN hM)) upper
        (le_of_eq_add (d := num 4*N*N*M*M*unit p*unit p+num 3*N*N*M*M*unit p*unit q) (by unfold mesh; ipra_ring)))

theorem actual_mesh_cross_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶
      upper (sample (var 0) (var 1)) (sample (var 0) (var 2)) one (var 1) ⋏
      upper (sample (var 0) (var 2)) (sample (var 0) (var 1)) one (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (cross_mesh _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_finite_C2_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ le one (var 2) ⟶
      upper (sample (var 0) (var 2)) (sample (var 1) (var 1)) (var 0+var 2) (var 0*var 2) ⋏
      upper (sample (var 1) (var 1)) (sample (var 0) (var 2)) two (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (fixed_against_diagonal _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_fixed_gamma_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fixedSample (var 0) (var 1) ≐ sample (var 1) (mesh (var 0))) := closeUniv 2 (fixed_at _ _)
theorem actual_gamma_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (gammaSample (var 0) (var 1) ≐ sample (mesh (var 0)) (mesh (var 0))) := closeUniv 2 (gamma_at _ _)
theorem original_fixed_gamma_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ RationalCubeInfimumName.regular fixedF (var 0)) :=
  closeUniv 1 (.impI (fixed_name_regular _ Prf.hyp0))
theorem original_euler_constant_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalCubeInfimumName.regular gammaF (var 0)) := closeUniv 1 (gamma_name_regular _)
theorem original_fixed_gamma_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ rationalLE (natCode zero) (fixedSample (var 0) (var 1)) ⋏
      rationalLE (fixedSample (var 0) (var 1)) (natCode one)) :=
  closeUniv 2 (.impI (fixed_sample_range _ _ Prf.hyp0))
theorem original_euler_constant_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (natCode zero) (gammaSample (var 0) (var 1)) ⋏
      rationalLE (gammaSample (var 0) (var 1)) (natCode one)) := closeUniv 2 (gamma_sample_range _ _)
theorem original_named_C2_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ C2At (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (C2_samples _ _ _ _ Prf.hyp0))
theorem original_named_C1_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le (var 0) (var 1) ⟶ C1At (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (C1_samples _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GammaEulerConstantName

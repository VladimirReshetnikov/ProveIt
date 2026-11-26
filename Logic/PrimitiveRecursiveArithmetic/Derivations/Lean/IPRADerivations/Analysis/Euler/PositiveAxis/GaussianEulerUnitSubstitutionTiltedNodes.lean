import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionImageGrid
import IPRADerivations.Analysis.Optimization.RationalCubeInfimumIntervals
import IPRADerivations.Core.CertificateTactics

/-!
# Exactly ordered rational approximations to the original unit chart

An affine tilt absorbs the two original observation errors in the
named decay order. Reversing the unchanged affine time grid and adding
2*i*eps gives actual rational node codes with exact adjacent order.
Every node moves by exactly its stated scalar error budget. No rounded
decay-cell positivity, floor partition, or quadrature law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionTiltedNodes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalArithmetic (add represents)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalLE denominator_positive)
open RationalValueBounds (upper radius crossLeft)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianEulerUnitSubstitutionImageGrid (node)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def tilt (a i A B : PTm n) : PTm n := add a (fraction (A*i) B)
def tiltNumerator (a i A B : PTm n) : ZT n :=
  numeratorOf a*ZT.ofNat B+ZT.ofNat (A*i)*ZT.ofNat (denominatorOf a)
def reverseNode (i p N a C E : PTm n) : PTm n := fstT (node (monus N i) p N a C E)
def correctedNode (i p N a C E : PTm n) : PTm n := tilt (reverseNode i p N a C E) i two (unit p)

@[simp] theorem subst_tilt {m : ℕ} (σ : Fin n → PTm m) (a i A B : PTm n) :
    Syn.subst σ (tilt a i A B) = tilt (Syn.subst σ a) (Syn.subst σ i) (Syn.subst σ A) (Syn.subst σ B) := by simp [tilt]
@[simp] theorem subst_reverseNode {m : ℕ} (σ : Fin n → PTm m) (i p N a C E : PTm n) :
    Syn.subst σ (reverseNode i p N a C E) = reverseNode (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [reverseNode]
@[simp] theorem subst_correctedNode {m : ℕ} (σ : Fin n → PTm m) (i p N a C E : PTm n) :
    Syn.subst σ (correctedNode i p N a C E) = correctedNode (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [correctedNode]

theorem tilt_represents (a i A B : PTm n) (hb : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (tilt a i A B) (tiltNumerator a i A B) (denominatorOf a*B) :=
  RationalRepresentations.represents_add _ _ _ _ _ _ (RationalRepresentations.represents_self a)
    (fraction_represents (A*i) B hb)

/-- A single actual upper-error inequality becomes exact order after
the stated affine tilt. All scalar input codes may be unreduced. -/
theorem tilt_step_order (a b i A B : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] upper a b A B) : Γ ⊢[PRAAx] rationalLE (tilt a i A B) (tilt b (succ i) A B) := by
  let U := denominatorOf a
  let V := denominatorOf b
  apply RationalArithmetic.order_of_representations _ _ _ _ (U*B) (V*B)
    (tilt_represents a i A B hb) (tilt_represents b (succ i) A B hb)
    (positive_product _ _ (denominator_positive a) hb) (positive_product _ _ (denominator_positive b) hb)
  apply zle_of_toZ (B*monus (B*crossLeft b a+A*U*V) (B*crossLeft a b))
  have eq := natEq (eq_add_of_le h)
  simp only [tiltNumerator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold crossLeft at eq ⊢
  dsimp only [U,V] at eq ⊢
  ipra_simps
  linear_combination -𝔞 B*eq

theorem tilt_error (a i A B : PTm n) (hb : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    radius (tilt a i A B) a (A*i) B := by
  let U := denominatorOf a
  have hu := denominator_positive (Γ := Γ) a
  have hd := positive_product _ _ hu hb
  have forward : Γ ⊢[PRAAx] upper (tilt a i A B) a (A*i) B := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ hd hu
      (tilt_represents a i A B hb) (RationalRepresentations.represents_self a)
    apply zle_of_toZ zero
    simp only [tiltNumerator,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have backward : Γ ⊢[PRAAx] upper a (tilt a i A B) (A*i) B := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ hu hd
      (RationalRepresentations.represents_self a) (tilt_represents a i A B hb)
    apply zle_of_toZ (two*A*i*U*U*B)
    simp only [tiltNumerator,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
    dsimp only [U]
    ipra_simps
    ring
  exact RationalValueBounds.radius_of_upper _ _ _ _ forward backward

theorem reverse_successor (N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    monus N i ≐ succ (monus N (succ i)) := by
  ipra_lc natEq (eq_add_of_le hi)-natEq (eq_add_of_le (le_trans (le_succ_self i) hi))

theorem original_reverse_upper (i p N a C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    upper (reverseNode i p N a C E) (reverseNode (succ i) p N a C E) two (unit p) := by
  let j := monus N (succ i)
  have raw := GaussianEulerUnitSubstitutionImageGrid.original_orientation_observations j p p N a C E hE hN
  have reduced := RationalValueBounds.upper_mono _ _ _ _ two (unit p)
    (positive_product _ _ (unit_positive p) (unit_positive p)) raw
    (le_of_eq_add (d := zero) (by ipra_ring))
  have same : Γ ⊢[PRAAx] node (monus N i) p N a C E ≐ node (succ j) p N a C E :=
    GaussianEulerDecayMesh.observation_numerator_congr _ _ (E*N) p
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (reverse_successor N i hi)))
  exact RationalValueBounds.upper_congr (congrFst same).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) reduced

theorem original_corrected_order (i p N a C E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    rationalLE (correctedNode i p N a C E) (correctedNode (succ i) p N a C E) :=
  tilt_step_order _ _ i two (unit p) (unit_positive p) (original_reverse_upper i p N a C E hE hN hi)

theorem original_correction_error (i p N a C E : PTm n) : Γ ⊢[PRAAx]
    radius (correctedNode i p N a C E) (reverseNode i p N a C E) (two*i) (unit p) :=
  tilt_error _ i two (unit p) (unit_positive p)

theorem original_uniform_correction_error (i p N a C E : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    radius (correctedNode i p N a C E) (reverseNode i p N a C E) (two*N) (unit p) :=
  RationalValueBounds.radius_mono _ _ _ _ _ _ (unit_positive p) (original_correction_error i p N a C E)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*unit p) hi))

private def body : PTm 6 := correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
def nodeF : PR 6 := PTm.toPR body
def run (i p N a C E : PTm n) : PTm n := PTm.app nodeF ![i,p,N,a,C,E]

theorem program_at (i p N a C E : PTm n) : Γ ⊢[PRAAx] run i p N a C E ≐ correctedNode i p N a C E := by
  have decode : Syn.subst (![i,p,N,a,C,E] : Fin 6 → PTm n) body = correctedNode i p N a C E := by
    simp only [body,subst_correctedNode,Syn.subst_var]
    rfl
  simpa only [run,nodeF,decode] using toPR_eq (Γ := Γ) body ![i,p,N,a,C,E]

theorem actual_original_corrected_unit_nodes_ordered_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ (le one (var 2) ⋏ lt (var 0) (var 2))) ⟶
      rationalLE (correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (correctedNode (succ (var 0)) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_corrected_order _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_unit_nodes_correction_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (radius (correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (reverseNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (two*var 0) (unit (var 1))) :=
  closeUniv 6 (original_correction_error _ _ _ _ _ _)

theorem actual_original_corrected_unit_nodes_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ correctedNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionTiltedNodes

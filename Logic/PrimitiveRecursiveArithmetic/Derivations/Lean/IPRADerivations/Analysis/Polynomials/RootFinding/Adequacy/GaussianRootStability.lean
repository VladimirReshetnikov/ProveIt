import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHornerPerturbation
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductWitness
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalStability

/-!
# Exact finite root stability for the actual reconstructed polynomials

Original coefficient distances of the two actual reverse Reconstruction
polynomials yield actual evaluation distances. At a listed root the source
evaluation is proved zero, and the true target factor fold supplies an
original target-list witness. Both directed covers use the exact rational
budget n R^(n-1) delta <= r^n, including zero delta or radius and repeated
roots. All lists, degrees, indices and rational tolerance data are internal.
No root-zero, factorization, evaluation or output-cover law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction (reconstruct product)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_symmetric distance_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalStability (pointsBounded point_bound_at subst_pointsBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalCover (cover close hit)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientErrors (S T N A B : PTm n) : Fm PTm n :=
  GaussianRationalHornerPerturbation.coefficientErrors (reconstruct S N N) (reconstruct T N N) N A B
def sourceBudget (N R A B p q : PTm n) : Fm PTm n :=
  le (pw q N*(N*pw R (PTm.pred N)*A)) (pw p N*B)
def basicInput (S T N R A B p q : PTm n) : Fm PTm n :=
  le one N ⋏ (le one R ⋏ (le one B ⋏ (le one q ⋏
    (length S ≐ N ⋏ (length T ≐ N ⋏ sourceBudget N R A B p q)))))
def stabilityInput (S T N R A B p q : PTm n) : Fm PTm n := basicInput S T N R A B p q ⋏
  (pointsBounded S R one ⋏ (pointsBounded T R one ⋏ coefficientErrors S T N A B))

@[simp] theorem subst_coefficientErrors {m : ℕ} (σ : Fin n → PTm m) (S T N A B : PTm n) :
    (coefficientErrors S T N A B).subst σ = coefficientErrors (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by simp [coefficientErrors]
@[simp] theorem subst_sourceBudget {m : ℕ} (σ : Fin n → PTm m) (N R A B p q : PTm n) :
    (sourceBudget N R A B p q).subst σ = sourceBudget (Syn.subst σ N) (Syn.subst σ R)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) := by simp [sourceBudget]
@[simp] theorem subst_basicInput {m : ℕ} (σ : Fin n → PTm m) (S T N R A B p q : PTm n) :
    (basicInput S T N R A B p q).subst σ = basicInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) := by simp [basicInput]
@[simp] theorem subst_stabilityInput {m : ℕ} (σ : Fin n → PTm m) (S T N R A B p q : PTm n) :
    (stabilityInput S T N R A B p q).subst σ = stabilityInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) := by simp [stabilityInput]

/-- Actual metric symmetry supplies the reverse coefficient condition,
without a common-denominator or canonical-input premise. -/
theorem coefficient_errors_symmetric (S T N A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (h : Γ ⊢[PRAAx] coefficientErrors S T N A B) :
    Γ ⊢[PRAAx] coefficientErrors T S N A B := by
  refine .allI (.impI ?_)
  have bShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using hB.shift
  have eShift : Γ.map Fm.shift ⊢[PRAAx] coefficientErrors (Syn.shift S) (Syn.shift T) (Syn.shift N) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,subst_coefficientErrors,Syn.shift] using h.shift
  have original := GaussianRationalHornerPerturbation.coefficient_error_at
    (reconstruct (Syn.shift S) (Syn.shift N) (Syn.shift N))
    (reconstruct (Syn.shift T) (Syn.shift N) (Syn.shift N))
    (Syn.shift N) (Syn.shift A) (Syn.shift B) (var 0) eShift.wk Prf.hyp0
  simpa only [Syn.shift,GaussianRationalReconstruction.subst_reconstruct] using
    distance_symmetric _ _ _ _ bShift.wk original

theorem reverse_input (S T N R A B p q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) : Γ ⊢[PRAAx] stabilityInput T S N R A B p q := by
  have basic := Prf.andE₁ h
  have r := Prf.andE₂ basic
  have b := Prf.andE₂ r
  have qpos := Prf.andE₂ b
  have shape := Prf.andE₂ qpos
  have target := Prf.andE₂ shape
  have swapped : Γ ⊢[PRAAx] basicInput T S N R A B p q :=
    .andI (Prf.andE₁ basic) (.andI (Prf.andE₁ r) (.andI (Prf.andE₁ b) (.andI (Prf.andE₁ qpos)
      (.andI (Prf.andE₁ target) (.andI (Prf.andE₁ shape) (Prf.andE₂ target))))))
  have points := Prf.andE₂ h
  have further := Prf.andE₂ points
  exact .andI swapped (.andI (Prf.andE₁ further) (.andI (Prf.andE₁ points)
    (coefficient_errors_symmetric _ _ _ _ _ (Prf.andE₁ b) (Prf.andE₂ further))))

/-- Original coefficient comparisons and the exact listed-zero theorem
derive the actual target product bound required by finite factor search. -/
theorem point_product_bound (S T N R A B p q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] bounded (product T N (entry S i)) (pw p N) (pw q N) := by
  have basic := Prf.andE₁ h
  have r := Prf.andE₂ basic
  have b := Prf.andE₂ r
  have qpos := Prf.andE₂ b
  have shape := Prf.andE₂ qpos
  have target := Prf.andE₂ shape
  have bounds := Prf.andE₂ h
  have index : Γ ⊢[PRAAx] lt i N := lt_congr (.eqRefl _) (Prf.andE₁ shape) hi
  have evalBound := GaussianRationalHornerPerturbation.monic_evaluation_bound
    (reconstruct S N N) (reconstruct T N N) (entry S i) N R A B
    (GaussianRationalReconstruction.reconstruct_length S N N) (GaussianRationalReconstruction.reconstruct_length T N N)
    (GaussianRationalReconstruction.reconstruct_monic S N N) (GaussianRationalReconstruction.reconstruct_monic T N N)
    (Prf.andE₁ r) (Prf.andE₁ b) (Prf.andE₂ (Prf.andE₂ bounds))
    (point_bound_at S R one i (Prf.andE₁ bounds) hi)
  have reversed := distance_symmetric _ _ _ _ (Prf.andE₁ b) evalBound
  have zeroDistance := distance_congr (.eqRefl _) (GaussianReconstructionRoots.listed_root_zero S N i index)
    (.eqRefl _) (.eqRefl _) reversed
  have targetBound := (GaussianReconstructionRoots.distance_zero_iff _ _ _ (Prf.andE₁ b)).iffMp zeroDistance
  have actual := bound_congr (GaussianRationalReconstruction.product_evaluation T N (entry S i))
    (.eqRefl _) (.eqRefl _) targetBound
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (Prf.andE₁ b)
    (GaussianPolynomialPerturbation.power_positive _ _ (Prf.andE₁ qpos))
    (le_congr (mul_comm _ _) (.eqRefl _) (Prf.andE₂ target)) actual

theorem point_witness (S T N R A B p q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx]
    GaussianRationalCover.hit (entry S i) T p q := by
  have basic := Prf.andE₁ h
  have qpos := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ basic))
  have target := Prf.andE₂ (Prf.andE₂ qpos)
  exact GaussianRationalProductWitness.product_hit T N (entry S i) p q (Prf.andE₁ basic) (Prf.andE₁ qpos)
    (le_congr (.eqRefl _) (Prf.andE₁ target).eqSymm (le_refl N)) (point_product_bound _ _ _ _ _ _ _ _ _ h hi)

theorem directed_cover (S T N R A B p q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) : Γ ⊢[PRAAx] cover S T p q := by
  refine .allI (.impI ?_)
  have hShift : Γ.map Fm.shift ⊢[PRAAx] stabilityInput (Syn.shift S) (Syn.shift T) (Syn.shift N) (Syn.shift R)
      (Syn.shift A) (Syn.shift B) (Syn.shift p) (Syn.shift q) := by
    simpa only [Fm.shift,subst_stabilityInput,Syn.shift] using h.shift
  simpa only [hit,Syn.shift,subst_entry,Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using
    point_witness _ _ _ _ _ _ _ _ (var 0) hShift.wk Prf.hyp0

/-- Both exact original-point covers, including repeated entries and p=0. -/
theorem product_stability (S T N R A B p q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) : Γ ⊢[PRAAx] close S T p q :=
  .andI (directed_cover _ _ _ _ _ _ _ _ h)
    (directed_cover _ _ _ _ _ _ _ _ (reverse_input _ _ _ _ _ _ _ _ h))

theorem checker_accepted (S T N R A B p q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) : Γ ⊢[PRAAx] GaussianRationalCover.check S T p q ≐ one :=
  (GaussianRationalCover.checker_reflection S T p q).iffMpr (product_stability _ _ _ _ _ _ _ _ h)

/-- The actual finite search returns a stored original target point. -/
def witness (S T N p q i : PTm n) : PTm n := GaussianRationalProductWitness.run T N (entry S i) p q
def witnessF : PR 6 := PTm.toPR (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))

@[simp] theorem subst_witness {m : ℕ} (σ : Fin n → PTm m) (S T N p q i : PTm n) :
    Syn.subst σ (witness S T N p q i) = witness (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ N)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ i) := by simp [witness]

theorem witness_program (S T N p q i : PTm n) : Γ ⊢[PRAAx]
    PTm.app witnessF ![S,T,N,p,q,i] ≐ witness S T N p q i := by
  simpa [witnessF] using toPR_eq (Γ := Γ) (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![S,T,N,p,q,i]

theorem witness_certificate (S T N R A B p q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx]
    lt (fstT (witness S T N p q i)) (length T) ⋏
      ((fstT (sndT (witness S T N p q i)) ≐ entry T (fstT (witness S T N p q i))) ⋏
        distanceBounded (entry S i) (fstT (sndT (witness S T N p q i))) p q) := by
  have basic := Prf.andE₁ h
  have qpos := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ basic))
  have target := Prf.andE₂ (Prf.andE₂ qpos)
  exact GaussianRationalProductWitness.output_certificate T N (entry S i) p q (Prf.andE₁ basic) (Prf.andE₁ qpos)
    (le_congr (.eqRefl _) (Prf.andE₁ target).eqSymm (le_refl N)) (point_product_bound _ _ _ _ _ _ _ _ _ h hi)

theorem program_certificate (S T N R A B p q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N R A B p q) (hi : Γ ⊢[PRAAx] lt i (length S)) : Γ ⊢[PRAAx]
    lt (fstT (PTm.app witnessF ![S,T,N,p,q,i])) (length T) ⋏
      ((fstT (sndT (PTm.app witnessF ![S,T,N,p,q,i])) ≐ entry T (fstT (PTm.app witnessF ![S,T,N,p,q,i]))) ⋏
        distanceBounded (entry S i) (fstT (sndT (PTm.app witnessF ![S,T,N,p,q,i]))) p q) := by
  have cert := witness_certificate S T N R A B p q i h hi
  have index := congrFst (witness_program (Γ := Γ) S T N p q i)
  have point := congrFst (congrSnd (witness_program (Γ := Γ) S T N p q i))
  exact .andI (lt_congr index.eqSymm (.eqRefl _) (Prf.andE₁ cert))
    (.andI (point.eqTrans ((Prf.andE₁ (Prf.andE₂ cert)).eqTrans (entry_congr (.eqRefl _) index.eqSymm)))
      (distance_congr (.eqRefl _) point.eqSymm (.eqRefl _) (.eqRefl _) (Prf.andE₂ (Prf.andE₂ cert))))

theorem reconstructed_product_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      close (var 0) (var 1) (var 6) (var 7)) :=
  closeUniv 8 (.impI (product_stability _ _ _ _ _ _ _ _ Prf.hyp0))

theorem reconstructed_product_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianRationalCover.check (var 0) (var 1) (var 6) (var 7) ≐ one) :=
  closeUniv 8 (.impI (checker_accepted _ _ _ _ _ _ _ _ Prf.hyp0))

theorem reconstructed_product_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      lt (var 8) (length (var 0)) ⟶
        (lt (fstT (PTm.app witnessF ![var 0,var 1,var 2,var 6,var 7,var 8])) (length (var 1)) ⋏
          ((fstT (sndT (PTm.app witnessF ![var 0,var 1,var 2,var 6,var 7,var 8])) ≐
            entry (var 1) (fstT (PTm.app witnessF ![var 0,var 1,var 2,var 6,var 7,var 8]))) ⋏
              distanceBounded (entry (var 0) (var 8))
                (fstT (sndT (PTm.app witnessF ![var 0,var 1,var 2,var 6,var 7,var 8]))) (var 6) (var 7)))) :=
  closeUniv 9 (.impI (.impI (program_certificate _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem reconstructed_witness_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (PTm.app witnessF ![var 0,var 1,var 2,var 3,var 4,var 5] ≐
      witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) := closeUniv 6 (witness_program _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRootStability

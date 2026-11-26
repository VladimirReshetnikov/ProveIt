import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootAlgebra
import IPRADerivations.Foundations.GapDecision

/-!
# Relative squared-norm triangle for actual coded Gaussian integers

Lagrange's identity for the actual signed coordinates yields a natural
Cauchy inequality for the absolute dot product. Natural square order then
removes the square from a common arbitrary relative norm budget R. The
actual addition program satisfies the exact relative triangle, including
R=0 and zero coefficient weights, without square roots or real arithmetic.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRelativeNormTriangle

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add scale zeroCode normSq normSq_eval normSq_code normSq_scale normSq_zero)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq subst_zabs)
open LeanProofs.IPRA.Probability.MedianWeighted (le_add_ad)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def dot (u v : PTm n) : ZT n := re u*re v+im u*im v
def determinant (u v : PTm n) : ZT n := re u*im v-im u*re v
def absDot (u v : PTm n) : PTm n := zabs (dot u v)
def absDeterminant (u v : PTm n) : PTm n := zabs (determinant u v)

ipra_subst dot
ipra_subst determinant
@[simp] theorem subst_absDot {m : ℕ} (σ : Fin n → PTm m) (u v : PTm n) :
    Syn.subst σ (absDot u v) = absDot (Syn.subst σ u) (Syn.subst σ v) := by simp only [absDot,subst_zabs,subst_dot]
@[simp] theorem subst_absDeterminant {m : ℕ} (σ : Fin n → PTm m) (u v : PTm n) :
    Syn.subst σ (absDeterminant u v) = absDeterminant (Syn.subst σ u) (Syn.subst σ v) := by simp only [absDeterminant,subst_zabs,subst_determinant]

theorem dot_value (u v : PTm n) : ZT.toZ Γ (dot u v) =
    ZT.toZ Γ (re u)*ZT.toZ Γ (re v)+ZT.toZ Γ (im u)*ZT.toZ Γ (im v) := by
  simp only [dot,ZT.toZ_add,ZT.toZ_mul]

theorem determinant_value (u v : PTm n) : ZT.toZ Γ (determinant u v) =
    ZT.toZ Γ (re u)*ZT.toZ Γ (im v)-ZT.toZ Γ (im u)*ZT.toZ Γ (re v) := by
  simp only [determinant,ZT.toZ_sub,ZT.toZ_mul]

/-- Literal natural Lagrange identity for arbitrary signed-pair inputs. -/
theorem lagrange (u v : PTm n) : Γ ⊢[PRAAx]
    absDot u v*absDot u v+absDeterminant u v*absDeterminant u v ≐ normSq u*normSq v := by
  apply deriveNat
  simp only [Q.mk_add,map_add]
  unfold absDot absDeterminant
  rw [zabs_sq,zabs_sq]
  simp only [Q.mk_mul,map_mul]
  rw [normSq_eval,normSq_eval,dot_value,determinant_value]
  ring

/-- The nonnegative determinant square is the explicit Cauchy remainder. -/
theorem cauchy (u v : PTm n) : Γ ⊢[PRAAx]
    le (absDot u v*absDot u v) (normSq u*normSq v) :=
  le_of_eq_add (d := absDeterminant u v*absDeterminant u v) (lagrange u v).eqSymm

/-- The exact common relative budget cancels by natural square order;
R need not be positive or itself the square of a natural number. -/
theorem relative_dot (u v A B R : PTm n)
    (hu : Γ ⊢[PRAAx] le (normSq u) (A*A*R))
    (hv : Γ ⊢[PRAAx] le (normSq v) (B*B*R)) : Γ ⊢[PRAAx]
    le (absDot u v) (A*B*R) :=
  nat_sqrt_mono (le_trans (cauchy u v)
    (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hu hv)))

theorem signed_le_absolute (s : ZT n) : Γ ⊢[PRAAx] zle s (ZT.ofNat (zabs s)) := by
  change Γ ⊢[PRAAx] le (s.pos+zero) (zabs s+s.neg)
  exact le_congr (add_zero _).eqSymm (add_comm _ _) (le_add_ad s.pos s.neg)

/-- Actual Gaussian addition expands with twice the dot product. Its
absolute value bounds that term even when the dot product is negative. -/
theorem triangle_absolute (u v : PTm n) : Γ ⊢[PRAAx]
    le (normSq (add u v)) (normSq u+normSq v+two*absDot u v) := by
  let s := dot u v
  let D : PTm n := PTm.monus ((ZT.ofNat (zabs s)).pos+s.neg) (s.pos+(ZT.ofNat (zabs s)).neg)
  have h : ZT.toZ Γ s+𝔞(D) = ZT.toZ Γ (ZT.ofNat (zabs s)) := zle_toZ (signed_le_absolute s)
  change ZT.toZ Γ (dot u v)+𝔞(D) = ZT.toZ Γ (ZT.ofNat (absDot u v)) at h
  rw [dot_value,ZT.toZ_ofNat] at h
  refine le_of_eq_add (d := two*D) ?_
  apply deriveNat
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul]
  rw [add,normSq_code,normSq_eval,normSq_eval]
  simp only [ZT.toZ_add]
  ipra_simps
  linear_combination -2*h

/-- Genuine relative squared-norm triangle. All five numerical inputs,
including a zero common relative budget, are internally quantified. -/
theorem relative_triangle (u v A B R : PTm n)
    (hu : Γ ⊢[PRAAx] le (normSq u) (A*A*R))
    (hv : Γ ⊢[PRAAx] le (normSq v) (B*B*R)) : Γ ⊢[PRAAx]
    le (normSq (add u v)) ((A+B)*(A+B)*R) := by
  have dotBound := le_mul_mono (le_refl two) (relative_dot u v A B R hu hv)
  have combined := add_le_add₂ (add_le_add₂ hu hv) dotBound
  exact le_trans (triangle_absolute u v) (le_congr (.eqRefl _) (by ipra_ring) combined)

theorem relative_scale (u A R C : PTm n) (hu : Γ ⊢[PRAAx] le (normSq u) (A*A*R)) : Γ ⊢[PRAAx]
    le (normSq (scale C u)) ((C*A)*(C*A)*R) :=
  le_congr (normSq_scale C u).eqSymm (by ipra_ring) (le_mul_mono (le_refl (C*C)) hu)

theorem relative_zero (R : PTm n) : Γ ⊢[PRAAx] le (normSq (zeroCode : PTm n)) (zero*zero*R) :=
  le_congr normSq_zero.eqSymm (by ipra_ring) (le_refl zero)

/-! Actual finite sums. The two fixed PR2 schemas compute the Gaussian
terms and their natural weights; every length, common budget and persistent
parameter remains a numerical object input. -/
def sumStep (f : PR 2) : PTm 3 := add (var 1) (ap2 f (var 0) (var 2))
def gaussianSumF (f : PR 2) : PR 2 := rec2 (zeroCode : PTm 1) (sumStep f)
def gaussianSum (f : PR 2) (k x : PTm n) : PTm n := ap2 (gaussianSumF f) k x
def weightBody (g : PR 2) : PTm 2 := ap2 g (var 0) (var 1)
def weightSum (g : PR 2) (k x : PTm n) : PTm n := ap2 (sumF (weightBody g)) k x

ipra_subst gaussianSum
ipra_subst weightSum

theorem gaussian_sum_zero (f : PR 2) (x : PTm n) : Γ ⊢[PRAAx] gaussianSum f zero x ≐ zeroCode := by
  simpa only [gaussianSum,gaussianSumF,ComplexLogarithmRemainder.subst_zeroCode] using
    rec2_zero (Γ := Γ) (zeroCode : PTm 1) (sumStep f) x

theorem gaussian_sum_succ (f : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    gaussianSum f (succ k) x ≐ add (gaussianSum f k x) (ap2 f k x) := by
  simpa only [gaussianSum,gaussianSumF,sumStep,ComplexLogarithmRemainder.subst_add,subst_ap2,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    rec2_succ (Γ := Γ) (zeroCode : PTm 1) (sumStep f) k x

theorem weight_body_at (g : PR 2) (k x : PTm n) : inst2 (weightBody g) k x = ap2 g k x := by simp [weightBody,inst2]
theorem weight_sum_zero (g : PR 2) (x : PTm n) : Γ ⊢[PRAAx] weightSum g zero x ≐ zero := sum_zero _ _
theorem weight_sum_succ (g : PR 2) (k x : PTm n) : Γ ⊢[PRAAx]
    weightSum g (succ k) x ≐ weightSum g k x+ap2 g k x := by
  simpa only [weightSum,weight_body_at] using sum_succ' (Γ := Γ) (weightBody g) k x

def termBounds (f g : PR 2) (N R x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ le (normSq (ap2 f (var 0) (Syn.shift x)))
    (ap2 g (var 0) (Syn.shift x)*ap2 g (var 0) (Syn.shift x)*Syn.shift R))
def prefixLaw (f g : PR 2) (N R x k : PTm n) : Fm PTm n := le k N ⟶
  le (normSq (gaussianSum f k x)) (weightSum g k x*weightSum g k x*R)

ipra_subst termBounds [Syn.subst_shift, Syn.shift_subst]
ipra_subst prefixLaw

theorem term_bound_at (f g : PR 2) (N R x k : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx]
    le (normSq (ap2 f k x)) (ap2 g k x*ap2 g k x*R) := by
  have rule : Γ ⊢[PRAAx] lt k N ⟶ le (normSq (ap2 f k x)) (ap2 g k x*ap2 g k x*R) := by
    simpa only [termBounds,Fm.subst_imp,subst_lt,subst_le,ComplexLogarithmRemainder.subst_normSq,subst_ap2,PTm.subst_mul,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE k
  exact .impE rule hk

theorem sum_prefix_zero (f g : PR 2) (R x : PTm n) : Γ ⊢[PRAAx]
    le (normSq (gaussianSum f zero x)) (weightSum g zero x*weightSum g zero x*R) :=
  le_congr (ComplexLogarithmRemainder.congr_normSq (gaussian_sum_zero f x)).eqSymm
    (congrMul (congrMul (weight_sum_zero g x) (weight_sum_zero g x)) (.eqRefl _)).eqSymm (relative_zero R)

theorem sum_prefix_step (f g : PR 2) (N R x k : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) (hk : Γ ⊢[PRAAx] lt k N)
    (ih : Γ ⊢[PRAAx] le (normSq (gaussianSum f k x)) (weightSum g k x*weightSum g k x*R)) : Γ ⊢[PRAAx]
    le (normSq (gaussianSum f (succ k) x)) (weightSum g (succ k) x*weightSum g (succ k) x*R) :=
  le_congr (ComplexLogarithmRemainder.congr_normSq (gaussian_sum_succ f k x)).eqSymm
    (congrMul (congrMul (weight_sum_succ g k x).eqSymm (weight_sum_succ g k x).eqSymm) (.eqRefl _))
    (relative_triangle _ _ _ _ R ih (term_bound_at f g N R x k h hk))

/-- Genuine QF induction on the actual two finite folds. The supplied
condition bounds only individual original terms, never a prefix or sum. -/
theorem sum_prefix (f g : PR 2) (N R x k : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    le (normSq (gaussianSum f k x)) (weightSum g k x*weightSum g k x*R) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] termBounds f g (Syn.shift N) (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,subst_termBounds,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f g (Syn.shift N) (Syn.shift R) (Syn.shift x) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_prefixLaw]
    · exact .impI (sum_prefix_zero f g R x).wk
    · refine .impI ?_
      exact sum_prefix_step f g _ _ _ _ hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw f g N R x k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk

theorem finite_sum_bound (f g : PR 2) (N R x : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) : Γ ⊢[PRAAx]
    le (normSq (gaussianSum f N x)) (weightSum g N x*weightSum g N x*R) := sum_prefix f g N R x N h (le_refl _)

/-- A finite computed weight budget transfers without square roots or
rounding. For the source off-dominant sum take C=3 and D=2 times its
common power denominator. -/
theorem finite_sum_budget (f g : PR 2) (N R x C D : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) (hWeights : Γ ⊢[PRAAx] le (C*weightSum g N x) D) : Γ ⊢[PRAAx]
    le (C*C*normSq (gaussianSum f N x)) (D*D*R) := by
  have first := le_mul_mono (le_refl (C*C)) (finite_sum_bound f g N R x h)
  have second := le_mul_mono (le_mul_mono hWeights hWeights) (le_refl R)
  exact le_trans first (le_congr (by ipra_ring) (.eqRefl _) second)

/-! Actual uniform PR3 output and literal returned-value/budget fields. -/
def output (f g : PR 2) (N R x : PTm n) : PTm n := pairT (gaussianSum f N x)
  (pairT (weightSum g N x) (weightSum g N x*weightSum g N x*R))
def outputF (f g : PR 2) : PR 3 := PTm.toPR (output f g (var 0) (var 1) (var 2))
def run (f g : PR 2) (N R x : PTm n) : PTm n := ap3 (outputF f g) N R x

ipra_subst output
ipra_subst run

theorem program_at (f g : PR 2) (N R x : PTm n) : Γ ⊢[PRAAx] run f g N R x ≐ output f g N R x := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output f g (var 0) (var 1) (var 2) : PTm 3) ![N,R,x]
theorem output_value (f g : PR 2) (N R x : PTm n) : Γ ⊢[PRAAx]
    fstT (run f g N R x) ≐ gaussianSum f N x := (program_at f g N R x).fstE
theorem output_weight (f g : PR 2) (N R x : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run f g N R x)) ≐ weightSum g N x :=
  (program_at f g N R x).sndE.fstE
theorem output_budget (f g : PR 2) (N R x : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run f g N R x)) ≐ weightSum g N x*weightSum g N x*R :=
  (program_at f g N R x).sndE.sndE

theorem program_certificate (f g : PR 2) (N R x : PTm n)
    (h : Γ ⊢[PRAAx] termBounds f g N R x) : Γ ⊢[PRAAx]
    le (normSq (fstT (run f g N R x))) (sndT (sndT (run f g N R x))) :=
  le_congr (ComplexLogarithmRemainder.congr_normSq (output_value f g N R x)).eqSymm (output_budget f g N R x).eqSymm
    (finite_sum_bound f g N R x h)

theorem relative_lagrange_cauchy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((absDot (var 0) (var 1)*absDot (var 0) (var 1)+absDeterminant (var 0) (var 1)*absDeterminant (var 0) (var 1) ≐
      normSq (var 0)*normSq (var 1)) ⋏
     le (absDot (var 0) (var 1)*absDot (var 0) (var 1)) (normSq (var 0)*normSq (var 1))) :=
  closeUniv 2 (.andI (lagrange _ _) (cauchy _ _))

theorem relative_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (normSq (var 0)) (var 2*var 2*var 4) ⟶ le (normSq (var 1)) (var 3*var 3*var 4) ⟶
      le (absDot (var 0) (var 1)) (var 2*var 3*var 4)) :=
  closeUniv 5 (.impI (.impI (relative_dot _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem relative_norm_triangle_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (normSq (var 0)) (var 2*var 2*var 4) ⟶ le (normSq (var 1)) (var 3*var 3*var 4) ⟶
      le (normSq (add (var 0) (var 1))) ((var 2+var 3)*(var 2+var 3)*var 4)) :=
  closeUniv 5 (.impI (.impI (relative_triangle _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem relative_norm_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (normSq (var 0)) (var 1*var 1*var 2) ⟶
      le (normSq (scale (var 3) (var 0))) ((var 3*var 1)*(var 3*var 1)*var 2)) :=
  closeUniv 4 (.impI (relative_scale _ _ _ _ Prf.hyp0))

theorem finite_relative_sum_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termBounds f g (var 0) (var 1) (var 2) ⟶
      le (normSq (gaussianSum f (var 0) (var 2))) (weightSum g (var 0) (var 2)*weightSum g (var 0) (var 2)*var 1)) :=
  closeUniv 3 (.impI (finite_sum_bound f g _ _ _ Prf.hyp0))

theorem finite_relative_sum_prefix_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (termBounds f g (var 0) (var 1) (var 2) ⟶ le (var 3) (var 0) ⟶
      le (normSq (gaussianSum f (var 3) (var 2))) (weightSum g (var 3) (var 2)*weightSum g (var 3) (var 2)*var 1)) :=
  closeUniv 4 (.impI (.impI (sum_prefix f g _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem finite_relative_sum_budget_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (termBounds f g (var 0) (var 1) (var 2) ⟶ le (var 3*weightSum g (var 0) (var 2)) (var 4) ⟶
      le (var 3*var 3*normSq (gaussianSum f (var 0) (var 2))) (var 4*var 4*var 1)) :=
  closeUniv 5 (.impI (.impI (finite_sum_budget f g _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem relative_sum_program_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run f g (var 0) (var 1) (var 2) ≐ output f g (var 0) (var 1) (var 2)) := closeUniv 3 (program_at f g _ _ _)

theorem relative_sum_certificate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (termBounds f g (var 0) (var 1) (var 2) ⟶
      le (normSq (fstT (run f g (var 0) (var 1) (var 2)))) (sndT (sndT (run f g (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (program_certificate f g _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRelativeNormTriangle

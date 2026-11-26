import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalMetric
import IPRADerivations.AnalyticNumberTheory.Multiplicative
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Core.LinearCombination

/-!
# Actual nearest signed coordinate on a protected rational mesh

The signed original coordinate is (P-Q)/D. Its numerical box conditions
place it in [-R,R]. An actual shifted quotient rounds it to the nearest
mesh index, including both endpoints. Division with remainder derives
both the protected index range and the half-mesh squared error. No
rounding, search or output law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalGridRounding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_sq)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def box (P Q D R : PTm n) : Fm PTm n := le Q (P+R*D) ⋏ le P (Q+R*D)
def shifted (P Q D R : PTm n) : PTm n := monus (P+R*D) Q
def dividend (P Q D R M : PTm n) : PTm n := two*M*shifted P Q D R+D
def index (P Q D R M : PTm n) : PTm n := quo (dividend P Q D R M) (two*D)
def coordinate (P Q D R M : PTm n) : ZT n := ZT.ofNat (index P Q D R M)-ZT.ofNat (R*M)
def error (P Q D R M : PTm n) : ZT n :=
  ZT.ofNat M*(ZT.ofNat P-ZT.ofNat Q)-ZT.ofNat D*coordinate P Q D R M

def residual (P Q D R M : PTm n) : PTm n := rem (dividend P Q D R M) (two*D)
@[simp] theorem subst_box {l : ℕ} (σ : Fin n → PTm l) (P Q D R : PTm n) :
    (box P Q D R).subst σ = box (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) := by simp [box]
@[simp] theorem subst_shifted {l : ℕ} (σ : Fin n → PTm l) (P Q D R : PTm n) :
    Syn.subst σ (shifted P Q D R) = shifted (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) := by simp [shifted]
@[simp] theorem subst_dividend {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    Syn.subst σ (dividend P Q D R M) = dividend (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [dividend]
@[simp] theorem subst_index {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    Syn.subst σ (index P Q D R M) = index (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [index]
@[simp] theorem subst_coordinate {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    (coordinate P Q D R M).subst σ = coordinate (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [coordinate]
@[simp] theorem subst_error {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    (error P Q D R M).subst σ = error (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [error]
@[simp] theorem subst_residual {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    Syn.subst σ (residual P Q D R M) = residual (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [residual]

theorem shifted_identity (P Q D R : PTm n) (h : Γ ⊢[PRAAx] box P Q D R) : Γ ⊢[PRAAx]
    P+R*D ≐ Q+shifted P Q D R := eq_add_of_le (.andE₁ h)

theorem signed_absolute (P Q : PTm n) : Γ ⊢[PRAAx]
    zabs (ZT.ofNat P-ZT.ofNat Q) ≐ monus P Q+monus Q P := by
  change Γ ⊢[PRAAx] monus (P+zero) (zero+Q)+monus (zero+Q) (P+zero) ≐ _
  exact congrAdd (congrMonus (add_zero P) (zero_add Q)) (congrMonus (zero_add Q) (add_zero P))

theorem box_of_absolute (P Q D R : PTm n)
    (h : Γ ⊢[PRAAx] le (zabs (ZT.ofNat P-ZT.ofNat Q)) (R*D)) : Γ ⊢[PRAAx] box P Q D R := by
  have total := le_congr (signed_absolute P Q) (.eqRefl _) h
  have pq := le_trans (le_add_right (monus P Q) (monus Q P)) total
  have qp := le_trans (le_add_left (monus Q P) (monus P Q)) total
  have q1 : Γ ⊢[PRAAx] le Q (monus Q P+P) := le_congr (.eqRefl _) (monus_max P Q) (le_add_left Q (monus P Q))
  have p1 : Γ ⊢[PRAAx] le P (monus P Q+Q) := le_congr (.eqRefl _) (monus_max P Q).eqSymm (le_add_left P (monus Q P))
  exact .andI (le_trans q1 (le_congr (.eqRefl _) (add_comm _ _) (add_le_add_right P qp)))
    (le_trans p1 (le_congr (.eqRefl _) (add_comm _ _) (add_le_add_right Q pq)))

theorem shifted_bound (P Q D R : PTm n) (h : Γ ⊢[PRAAx] box P Q D R) : Γ ⊢[PRAAx]
    le (shifted P Q D R) (two*R*D) := by
  apply le_of_eq_add (d := monus (Q+R*D) P)
  ipra_lc natEq (shifted_identity P Q D R h)+natEq (eq_add_of_le (.andE₂ h))

theorem division (P Q D R M : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    (dividend P Q D R M ≐ two*D*index P Q D R M+residual P Q D R M) ⋏
      lt (residual P Q D R M) (two*D) :=
  div_mod_at (x := dividend P Q D R M)
    (RationalIntegerNormalization.positive_form (positive_product two D (le_succ_self one) hD))

theorem dividend_bound (P Q D R M : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] box P Q D R) : Γ ⊢[PRAAx]
    lt (dividend P Q D R M) ((two*D)*succ (two*R*M)) := by
  have first : Γ ⊢[PRAAx] le (dividend P Q D R M) (two*M*(two*R*D)+D) :=
    add_le_add_right D (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (two*M) (shifted_bound P Q D R h)))
  have next : Γ ⊢[PRAAx] lt (two*M*(two*R*D)+D) ((two*D)*succ (two*R*M)) := by
    apply le_of_eq_add (d := monus D one)
    ipra_lc natEq (eq_add_of_le hD)
  exact lt_of_le_of_lt first next

theorem index_bound (P Q D R M : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] box P Q D R) : Γ ⊢[PRAAx]
    le (index P Q D R M) (two*R*M) := by
  have q := LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative.quo_lt
    (RationalIntegerNormalization.positive_form (positive_product two D (le_succ_self one) hD))
    (dividend_bound P Q D R M hD h)
  exact (succ_monus_succ (index P Q D R M) (two*R*M)).eqSymm.eqTrans q

/-- The doubled signed rounding error is the actual remainder minus D. -/
theorem error_value (P Q D R M : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] box P Q D R) :
    (2 : Groth (IPRA.Q Γ))*ZT.toZ Γ (error P Q D R M) = 𝔞(residual P Q D R M)-𝔞(D) := by
  have eq := natEq (.andE₁ (division P Q D R M hD))
  have shift := natEq (shifted_identity P Q D R h)
  simp only [dividend] at eq
  simp only [error,coordinate,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination eq+2*𝔞(M)*shift

/-- A derived half-mesh error: four times its square is at most D squared.
The mesh numerator, signed coordinate, radius and error may all vanish. -/
theorem error_square (P Q D R M : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] box P Q D R) : Γ ⊢[PRAAx]
    le ((two*two)*(zabs (error P Q D R M)*zabs (error P Q D R M))) (D*D) := by
  have twice := error_value P Q D R M hD h
  have bound := natEq (eq_add_of_le (le_of_lt (.andE₂ (division P Q D R M hD))))
  have square := zabs_sq (Γ := Γ) (error P Q D R M)
  apply le_of_eq_add (d := residual P Q D R M*(monus (two*D) (residual P Q D R M)))
  apply deriveNat
  ipra_simps
  rw [square]
  linear_combination -(𝔞(residual P Q D R M)-𝔞(D)+2*ZT.toZ Γ (error P Q D R M))*twice+
    𝔞(residual P Q D R M)*bound

def output (P Q D R M : PTm n) : PTm n := pairT (index P Q D R M)
  (pairT (shifted P Q D R) (residual P Q D R M))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (P Q D R M : PTm n) : PTm n := PTm.app outputF ![P,Q,D,R,M]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    Syn.subst σ (output P Q D R M) = output (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (P Q D R M : PTm n) :
    Syn.subst σ (run P Q D R M) = run (Syn.subst σ P) (Syn.subst σ Q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ M) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (P Q D R M : PTm n) : Γ ⊢[PRAAx] run P Q D R M ≐ output P Q D R M := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![P,Q,D,R,M]
theorem returned_index (P Q D R M : PTm n) : Γ ⊢[PRAAx] fstT (run P Q D R M) ≐ index P Q D R M :=
  (congrFst (program_at P Q D R M)).eqTrans (fst_pair _ _)
theorem returned_shifted (P Q D R M : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P Q D R M)) ≐ shifted P Q D R :=
  (congrFst (congrSnd (program_at P Q D R M))).eqTrans ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
theorem returned_residual (P Q D R M : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P Q D R M)) ≐ residual P Q D R M :=
  (congrSnd (congrSnd (program_at P Q D R M))).eqTrans ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem actual_nearest_coordinate_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ box (var 0) (var 1) (var 2) (var 3) ⟶
      le (index (var 0) (var 1) (var 2) (var 3) (var 4)) (two*var 3*var 4)) :=
  closeUniv 5 (.impI (.impI (index_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_nearest_coordinate_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ box (var 0) (var 1) (var 2) (var 3) ⟶
      le ((two*two)*(zabs (error (var 0) (var 1) (var 2) (var 3) (var 4))*zabs (error (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 2*var 2)) :=
  closeUniv 5 (.impI (.impI (error_square _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_coordinate_box_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (zabs (ZT.ofNat (var 0)-ZT.ofNat (var 1))) (var 3*var 2) ⟶ box (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (box_of_absolute _ _ _ _ Prf.hyp0))
theorem actual_nearest_coordinate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_returned_coordinate_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ box (var 0) (var 1) (var 2) (var 3) ⟶
      le (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (two*var 3*var 4)) :=
  closeUniv 5 (.impI (.impI (le_congr (returned_index _ _ _ _ _).eqSymm (.eqRefl _)
    (index_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRationalGridRounding

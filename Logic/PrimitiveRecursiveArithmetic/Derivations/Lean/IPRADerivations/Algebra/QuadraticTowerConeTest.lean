import IPRADerivations.Algebra.QuadraticTowerSignNegation

/-!
# Actual positive-coefficient cone test for a numerical tower extension

The original lower query tags certify two nonnegative coefficients,
with an explicit positive coefficient, and a positive radicand. A fixed
compiled Boolean test reflects exactly those conditions. The SAME
parent sign program is positive, with the original conditional d query
retained. Identifying this witness predicate with sign(a+b)>0, and cone
closure, require the separate lower ordered-domain provider.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.QuadraticTowerConeTest

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open QuadraticTowerArrayCodec (arrayHeight normalized code horizon)
open QuadraticTowerMultiplicationHeight (radicandsHeight)
open QuadraticTowerMultiplicationTable (budget leftHalf rightHalf)
open QuadraticTowerSignRecipe (read firstTag secondTag)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def tagCone (a b d : PTm n) : Fm PTm n := ((a ≐ zero) ⋎ (a ≐ one)) ⋏
  (((b ≐ zero) ⋎ (b ≐ one)) ⋏ (((a ≐ one) ⋎ (b ≐ one)) ⋏ (d ≐ one)))
@[simp] theorem subst_tagCone {k : ℕ} (σ : Fin n → PTm k) (a b d : PTm n) :
    (tagCone a b d).subst σ = tagCone (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ d) := by simp [tagCone]

def coneSyntax : BFm 3 := .and (.or (.eq (var 0) zero) (.eq (var 0) one))
  (.and (.or (.eq (var 1) zero) (.eq (var 1) one)) (.and (.or (.eq (var 0) one) (.eq (var 1) one)) (.eq (var 2) one)))
theorem cone_formula : formula coneSyntax = tagCone (var 0) (var 1) (var 2) := rfl
def tagBit (a b d : PTm n) : PTm n := Foundations.BoundedSyntax.bit coneSyntax ![a,b,d]
@[simp] theorem subst_tagBit {k : ℕ} (σ : Fin n → PTm k) (a b d : PTm n) :
    Syn.subst σ (tagBit a b d) = tagBit (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ d) := by
  unfold tagBit
  rw [Foundations.BoundedSyntax.bit_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem tag_bit_reflection (a b d : PTm n) : Γ ⊢[PRAAx] Fm.iff (tagBit a b d ≐ one) (tagCone a b d) := by
  simpa [tagBit,cone_formula] using Foundations.BoundedSyntax.bounded_reflection (Γ := Γ) coneSyntax ![a,b,d]
theorem tag_bit_cases (a b d : PTm n) : Γ ⊢[PRAAx] Foundations.BooleanBits.Bit (tagBit a b d) :=
  Foundations.BoundedSyntax.bit_cases coneSyntax ![a,b,d]

theorem tag_cone_congr {a a' b b' d d' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b')
    (hd : Γ ⊢[PRAAx] d ≐ d') (p : Γ ⊢[PRAAx] tagCone a b d) : Γ ⊢[PRAAx] tagCone a' b' d' := by
  have proof := Prf.eqSubst (Γ := Γ) (tagCone (var 0) (var 1) (var 2) : Fm PTm 3)
    ![a,b,d] ![a',b',d'] (fun i => by fin_cases i; exact ha; exact hb; exact hd) (by simpa using p)
  simpa using proof

theorem recipe_first_positive (h B D S A : PTm n) (ha : Γ ⊢[PRAAx] firstTag h B D S A ≐ one)
    (hb : Γ ⊢[PRAAx] (secondTag h B D S A ≐ zero) ⋎ (secondTag h B D S A ≐ one)) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D S A ≐ one := by
  refine .orE hb ?_ ?_
  · exact (QuadraticTowerSignRecipe.dispatch_b_zero _ _ _
      (QuadraticIntegerSignDispatch.nonzero_from_code ha.wk QuadraticIntegerSignDispatch.nonzero_one) Prf.hyp0).eqTrans ha.wk
  · exact (QuadraticTowerSignRecipe.dispatch_same _ _ _
      (QuadraticIntegerSignDispatch.nonzero_from_code ha.wk QuadraticIntegerSignDispatch.nonzero_one)
      (QuadraticIntegerSignDispatch.nonzero_from_code Prf.hyp0 QuadraticIntegerSignDispatch.nonzero_one)
      (ha.wk.eqTrans Prf.hyp0.eqSymm)).eqTrans ha.wk

theorem recipe_second_positive (h B D S A : PTm n)
    (ha : Γ ⊢[PRAAx] (firstTag h B D S A ≐ zero) ⋎ (firstTag h B D S A ≐ one))
    (hb : Γ ⊢[PRAAx] secondTag h B D S A ≐ one)
    (hd : Γ ⊢[PRAAx] read h (budget h B D) S (entry D h) ≐ one) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D S A ≐ one := by
  refine .orE ha ?_ ?_
  · exact (QuadraticTowerSignRecipe.recipe_a_zero h B D S A Prf.hyp0).eqTrans
      ((QuadraticTowerSignRecipe.tag_product_congr hb.wk hd.wk).eqTrans QuadraticIntegerSignDispatch.tag_product_one_one)
  · exact recipe_first_positive h B D S A Prf.hyp0 (.orI₂ hb.wk)

theorem recipe_cone (h B D S A : PTm n)
    (p : Γ ⊢[PRAAx] tagCone (firstTag h B D S A) (secondTag h B D S A) (read h (budget h B D) S (entry D h))) : Γ ⊢[PRAAx]
    QuadraticTowerSignRecipe.recipe h B D S A ≐ one :=
  .orE p.andE₂.andE₂.andE₁ (recipe_first_positive h B D S A Prf.hyp0 p.andE₂.andE₁.wk)
    (recipe_second_positive h B D S A p.andE₁.wk Prf.hyp0 p.andE₂.andE₂.andE₂.wk)

def lowerFirst (h B D A : PTm n) : PTm n := QuadraticTowerSignTable.query h (budget h B D) D (leftHalf h A)
def lowerSecond (h B D A : PTm n) : PTm n := QuadraticTowerSignTable.query h (budget h B D) D (rightHalf h A)
def lowerRadicand (h B D : PTm n) : PTm n := QuadraticTowerSignTable.query h (budget h B D) D (entry D h)
def flag (h B D A : PTm n) : PTm n := tagBit (lowerFirst h B D A) (lowerSecond h B D A) (lowerRadicand h B D)
@[simp] theorem subst_lowerFirst {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (lowerFirst h B D A) = lowerFirst (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [lowerFirst]
@[simp] theorem subst_lowerSecond {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (lowerSecond h B D A) = lowerSecond (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [lowerSecond]
@[simp] theorem subst_lowerRadicand {k : ℕ} (σ : Fin n → PTm k) (h B D : PTm n) :
    Syn.subst σ (lowerRadicand h B D) = lowerRadicand (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) := by simp [lowerRadicand]
@[simp] theorem subst_flag {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (flag h B D A) = flag (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [flag]

theorem flag_reflection (h B D A : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (flag h B D A ≐ one) (tagCone (lowerFirst h B D A) (lowerSecond h B D A) (lowerRadicand h B D)) :=
  tag_bit_reflection _ _ _
theorem flag_cases (h B D A : PTm n) : Γ ⊢[PRAAx] Foundations.BooleanBits.Bit (flag h B D A) := tag_bit_cases _ _ _

theorem first_normalized (h B D A : PTm n) : Γ ⊢[PRAAx]
    firstTag h B D (QuadraticTowerSignTable.table h (budget h B D) D) (normalized (succ h) A) ≐ lowerFirst h B D A :=
  (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerArrayNormalization.left_half_normalized h A)).eqTrans
    (QuadraticTowerSignCoherence.read_values_proper _ _ _ _ _ (QuadraticTowerOperandProperness.normalized_values h (leftHalf h A)))
theorem second_normalized (h B D A : PTm n) : Γ ⊢[PRAAx]
    secondTag h B D (QuadraticTowerSignTable.table h (budget h B D) D) (normalized (succ h) A) ≐ lowerSecond h B D A :=
  (QuadraticTowerSignRecipe.read_operand_congr _ _ _ _ _ (QuadraticTowerArrayNormalization.right_half_normalized h A)).eqTrans
    (QuadraticTowerSignCoherence.read_values_proper _ _ _ _ _ (QuadraticTowerOperandProperness.normalized_values h (rightHalf h A)))

/-- Success of the actual Boolean test implies positivity of the SAME
actual parent query. No parent-sign law is an input. -/
theorem query_positive (h B D A : PTm n) (ha : Γ ⊢[PRAAx] arrayHeight (succ h) A B)
    (hf : Γ ⊢[PRAAx] flag h B D A ≐ one) : Γ ⊢[PRAAx] QuadraticTowerSignTable.query (succ h) B D A ≐ one := by
  have actual := tag_cone_congr (first_normalized h B D A).eqSymm (second_normalized h B D A).eqSymm (.eqRefl _)
    (.impE (flag_reflection h B D A).andE₁ hf)
  exact (QuadraticTowerSignTable.query_succ h B D A ha).eqTrans (recipe_cone _ _ _ _ _ actual)


def source (h B D A b : PTm n) : Fm PTm n := le b B ⋏ (radicandsHeight D (succ h) b ⋏ arrayHeight (succ h) A b)
def thirdCode (h B D A : PTm n) : PTm n := code h
  (QuadraticTowerSignRecipe.thirdInput h B D (QuadraticTowerSignTable.table h (budget h B D) D) (normalized (succ h) A)) (budget h B D)
def addresses (h B D A : PTm n) : Fm PTm n :=
  lt (code h (leftHalf h A) (budget h B D)) (horizon h (budget h B D)) ⋏
    (lt (code h (rightHalf h A) (budget h B D)) (horizon h (budget h B D)) ⋏
      (lt (code h (entry D h) (budget h B D)) (horizon h (budget h B D)) ⋏
        lt (thirdCode h B D A) (horizon h (budget h B D))))
@[simp] theorem subst_source {k : ℕ} (σ : Fin n → PTm k) (h B D A b : PTm n) :
    (source h B D A b).subst σ = source (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) (Syn.subst σ b) := by simp [source]
@[simp] theorem subst_thirdCode {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (thirdCode h B D A) = thirdCode (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [thirdCode]
@[simp] theorem subst_addresses {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    (addresses h B D A).subst σ = addresses (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [addresses]

theorem source_addresses (h B D A b : PTm n) (p : Γ ⊢[PRAAx] source h B D A b) : Γ ⊢[PRAAx] addresses h B D A := by
  have bK := le_trans p.andE₁ (QuadraticTowerSignEmbedding.budget_inflation h B D)
  have first := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.left_height h A b p.andE₂.andE₂) bK
  have second := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.right_height h A b p.andE₂.andE₂) bK
  have rad := QuadraticTowerMultiplicationHeight.array_mono _ _ _ _
    (QuadraticTowerMultiplicationHeight.radicand_at D (succ h) b h p.andE₂.andE₁ (le_refl _)) bK
  exact .andI (QuadraticTowerArrayCodec.code_bound _ _ _ first)
    (.andI (QuadraticTowerArrayCodec.code_bound _ _ _ second)
      (.andI (QuadraticTowerArrayCodec.code_bound _ _ _ rad)
        (QuadraticTowerSignTable.successor_third_address h B D A
          (QuadraticTowerMultiplicationHeight.radicands_mono _ _ _ _ p.andE₂.andE₁ p.andE₁)
          (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ p.andE₂.andE₂ p.andE₁))))

theorem source_certificate (h B D A b : PTm n) (p : Γ ⊢[PRAAx] source h B D A b)
    (hf : Γ ⊢[PRAAx] flag h B D A ≐ one) : Γ ⊢[PRAAx]
    (QuadraticTowerSignTable.query (succ h) B D A ≐ one) ⋏ addresses h B D A :=
  .andI (query_positive h B D A (QuadraticTowerMultiplicationHeight.array_mono _ _ _ _ p.andE₂.andE₂ p.andE₁) hf)
    (source_addresses h B D A b p)

/-! Actual fixed-arity test/parent/lower-tag output. -/
def output (h B D A : PTm n) : PTm n := pairT (flag h B D A)
  (pairT (QuadraticTowerSignTable.query (succ h) B D A)
    (pairT (lowerFirst h B D A) (pairT (lowerSecond h B D A) (pairT (lowerRadicand h B D) (budget h B D)))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (h B D A : PTm n) : PTm n := PTm.app outputF ![h,B,D,A]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (output h B D A) = output (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (h B D A : PTm n) :
    Syn.subst σ (run h B D A) = run (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ A) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (h B D A : PTm n) : Γ ⊢[PRAAx] run h B D A ≐ output h B D A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![h,B,D,A]
theorem returned_flag (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (run h B D A) ≐ flag h B D A :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (run h B D A) ≐
    pairT (QuadraticTowerSignTable.query (succ h) B D A)
      (pairT (lowerFirst h B D A) (pairT (lowerSecond h B D A) (pairT (lowerRadicand h B D) (budget h B D)))) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_parent (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run h B D A)) ≐ QuadraticTowerSignTable.query (succ h) B D A :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_lower (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run h B D A)) ≐
    pairT (lowerFirst h B D A) (pairT (lowerSecond h B D A) (pairT (lowerRadicand h B D) (budget h B D))) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_first (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run h B D A))) ≐ lowerFirst h B D A :=
  (congrFst (returned_lower _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_last (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run h B D A))) ≐ pairT (lowerSecond h B D A) (pairT (lowerRadicand h B D) (budget h B D)) :=
  (congrSnd (returned_lower _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_second (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run h B D A)))) ≐ lowerSecond h B D A :=
  (congrFst (returned_last _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_rad_pair (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run h B D A)))) ≐ pairT (lowerRadicand h B D) (budget h B D) :=
  (congrSnd (returned_last _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_radicand (h B D A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (run h B D A))))) ≐ lowerRadicand h B D :=
  (congrFst (returned_rad_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_cap (h B D A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (run h B D A))))) ≐ budget h B D :=
  (congrSnd (returned_rad_pair _ _ _ _)).eqTrans (snd_pair _ _)

theorem returned_success (h B D A b : PTm n) (p : Γ ⊢[PRAAx] source h B D A b)
    (hf : Γ ⊢[PRAAx] fstT (run h B D A) ≐ one) : Γ ⊢[PRAAx]
    (fstT (sndT (run h B D A)) ≐ one) ⋏ addresses h B D A :=
  .andI ((returned_parent _ _ _ _).eqTrans (source_certificate h B D A b p ((returned_flag _ _ _ _).eqSymm.eqTrans hf)).andE₁)
    (source_addresses h B D A b p)

theorem actual_positive_coefficient_cone_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (tagBit (var 0) (var 1) (var 2) ≐ one) (tagCone (var 0) (var 1) (var 2))) := closeUniv 3 (tag_bit_reflection _ _ _)
theorem actual_positive_coefficient_cone_flag_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Foundations.BooleanBits.Bit (flag (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (flag_cases _ _ _ _)
theorem actual_original_cone_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (arrayHeight (succ (var 0)) (var 3) (var 1) ⟶ flag (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3) ≐ one) :=
  closeUniv 4 (.impI (.impI (query_positive _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_actual_cone_addresses_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ addresses (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (source_addresses _ _ _ _ (var 4) Prf.hyp0))
theorem original_actual_cone_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ flag (var 0) (var 1) (var 2) (var 3) ≐ one ⟶
      (QuadraticTowerSignTable.query (succ (var 0)) (var 1) (var 2) (var 3) ≐ one) ⋏ addresses (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (source_certificate _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))
theorem actual_cone_test_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_cone_test_returned_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sndT (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))))) ≐ budget (var 0) (var 1) (var 2)) := closeUniv 4 (returned_cap _ _ _ _)
theorem original_returned_cone_test_success_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ one ⟶
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ one) ⋏ addresses (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (returned_success _ _ _ _ (var 4) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticTowerConeTest

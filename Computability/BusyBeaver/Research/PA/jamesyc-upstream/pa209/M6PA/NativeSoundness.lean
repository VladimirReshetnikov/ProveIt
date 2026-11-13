module
public import M6PA.NativeHFS
@[expose] public section

/-! Soundness direction of native/PA calibration, using the concrete HFS
interpretation in every PA model. This does NOT supply the reverse four-pass
PA-to-native compiler or its internal primitive-recursive proof translation. -/
namespace M6.PA.NativeHFS
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open NativeCalculus
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] in
@[simp] theorem assign_overwrite (env : Nat → V) (a : Nat) (x y : V) :
    assign (assign env a x) a y = assign env a y := by
  funext v
  by_cases hv : v = a <;> simp [assign,hv]

theorem rho1_valid (a b : Nat) (env : Nat → V) : evalCode (rho1 a b) env := by
  simp only [rho1,evalCode_ex,evalCode_eq]
  refine ⟨env b,?_⟩
  by_cases hab : b = a <;> simp [assign,hab]

theorem rho2_valid (a b c : Nat) (env : Nat → V) : evalCode (rho2 a b c) env := by
  simp only [rho2,evalCode_imp,evalCode_all]
  intro h hp x
  exact h x (hp x)

theorem rho3_valid (a b c : Nat) (env : Nat → V) : evalCode (rho3 a b c) env := by
  simp only [rho3,evalCode_imp,evalCode_mem,evalCode_eq]
  intro hm he
  exact he ▸ hm

theorem rho4_valid (a b c : Nat) (env : Nat → V) : evalCode (rho4 a b c) env := by
  simp only [rho4,evalCode_imp,evalCode_all]
  by_cases hab : a = b
  · subst b
    exact id
  · intro h x y
    rw [← assign_comm env hab]
    exact h y x

theorem rho5_valid (a b c : Nat) (env : Nat → V) : evalCode (rho5 a b c) env := by
  simp only [rho5,evalCode_imp,evalCode_eq,evalCode_mem]
  intro he hm
  exact he ▸ hm

theorem rho6_valid (a b : Nat) (env : Nat → V) : evalCode (rho6 a b) env := by
  simp only [rho6,evalCode_imp,evalCode_ex,evalCode_all]
  rintro ⟨x,hx⟩
  simpa only [assign_overwrite,assign_restore] using hx (env a)

theorem rho7_valid (a b c : Nat) (env : Nat → V) : evalCode (rho7 a b c) env := by
  simp only [rho7,evalCode_imp,evalCode_eq]
  intro hab hac
  exact hab.symm.trans hac

theorem rho8_valid (a b c u : Nat) (env : Nat → V) : evalCode (rho8 a b c u) env := by
  simp only [rho8,evalCode_imp]
  intro h hac _
  by_contra hc
  exact hc (hac (h (fun hct => False.elim (hc hct))))

/-- Structural induction on real finite native derivation trees. -/
theorem derivation_sound {n : Nat} (d : Derivation n) (env : Nat → V) : evalCode n env := by
  induction d generalizing env with
  | truth => exact evalCode_zero env
  | mp da dab iha ihab => exact (evalCode_imp _ _ env).mp (ihab env) (iha env)
  | all a d ih =>
    rw [evalCode_all]
    intro x
    exact ih (assign env a x)
  | r1 a b => exact rho1_valid a b env
  | r2 a b c => exact rho2_valid a b c env
  | r3 a b c => exact rho3_valid a b c env
  | r4 a b c => exact rho4_valid a b c env
  | r5 a b c => exact rho5_valid a b c env
  | r6 a b => exact rho6_valid a b env
  | r7 a b c => exact rho7_valid a b c env
  | r8 a b c u _ => exact rho8_valid a b c u env
  | guardedBundle a b c ha hb => exact bundle_valid a b c ha hb env

/-- Every native proof gives a genuine PA derivation of its universally closed
HFS interpretation. This external theorem does not claim a PR internal compiler. -/
theorem derivation_PA_proof {n : Nat} (d : Derivation n) :
    theory ⊢ (codeFormula n).univCl := by
  apply Arithmetic.complete.{0} theory _
  intro W _ _
  simp only [models_iff,Semiformula.eval_univCl]
  intro env
  exact (codeFormula_correct _ env).mpr (derivation_sound d env)

theorem native_refutation_PA_bottom (h : Proved 1) : theory ⊢ (⊥ : ArithmeticSentence) := by
  rcases h with ⟨d⟩
  apply Arithmetic.complete.{0} theory _
  intro W _ _
  have hf := evalCode_one (V := W) (fun _ => 0) (derivation_sound d (fun _ => 0))
  exact False.elim hf

#print axioms derivation_sound
#print axioms derivation_PA_proof
#print axioms native_refutation_PA_bottom
end M6.PA.NativeHFS


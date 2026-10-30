import BusyBeaver.ZFC.ArithmeticProofConstructors222
import BusyBeaver.ZFC.ArithmeticHistory222Nat

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! The fixed Σ₁ theorem predicate of the actual represented C222 checker.
The rule closures contain numeric proof witnesses from the new history.
Generic finite Lukasiewicz certificates supply propositional logic, and the
unchanged rho6 supplies ex falso at false code1. No old-calculus soundness,
seed validity, formula induction, runtime, or HA equivalence is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorProvability222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticHistory222
open ArithmeticProofConstructors222
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho8)
open scoped LO.FirstOrder.Arithmetic

/-- Fixed syntax, chosen before the ambient arithmetic model. -/
def cProvDef : 𝚺₁.Semisentence 1 := .mkSigma
  “conclusion. ∃ code, !ArithmeticHistory222.checkDef code conclusion”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CProv (conclusion : V) : Prop := ∃ code : V, value code = conclusion + 1

instance cProv_defined : 𝚺₁-Predicate[V] CProv via cProvDef :=
  .mk fun e => by simp [cProvDef, CProv]
instance cProv_definable : 𝚺₁-Predicate[V] CProv := cProv_defined.to_definable

theorem cProv_truth : CProv (0 : V) := ⟨1, by simpa using value_truth (V := V)⟩

/-- Major premise first; the actual MP node stores conclusion, minor code,
then major code. Both supplied witnesses are checked by the actual row. -/
theorem cProv_mp {a b : V} (hi : CProv (wim a b)) (ha : CProv a) : CProv b := by
  obtain ⟨di, hi⟩ := hi
  obtain ⟨da, ha⟩ := ha
  exact ⟨node 1 (cantor b (cantor da di)), value_mp b a (wim a b) da di ha hi rfl⟩

theorem cProv_gen (a : V) {p : V} (hp : CProv p) : CProv (wal a p) := by
  obtain ⟨d, hd⟩ := hp
  exact ⟨node 2 (cantor a d), value_gen a p d hd⟩

theorem cProv_rho1 (a b : V) : CProv (rho1 a b) :=
  ⟨node 3 (cantor a b), value_r1 a b⟩
theorem cProv_rho2 (a b c : V) : CProv (rho2 a b c) :=
  ⟨node 4 (cantor a (cantor b c)), value_r2 a b c⟩
theorem cProv_rho3 (a b c : V) : CProv (rho3 a b c) :=
  ⟨node 5 (cantor a (cantor b c)), value_r3 a b c⟩
theorem cProv_rho4 (a b c : V) : CProv (rho4 a b c) :=
  ⟨node 6 (cantor a (cantor b c)), value_r4 a b c⟩
theorem cProv_rho5 (a b c : V) : CProv (rho5 a b c) :=
  ⟨node 7 (cantor a (cantor b c)), value_r5 a b c⟩
theorem cProv_rho6 (a b : V) : CProv (rho6 a b) :=
  ⟨node 8 (cantor a b), value_r6 a b⟩

/-- The changed equality row is growG; rho7 is not an assumed rule. -/
theorem cProv_growG (a b c : V) : CProv (ArithmeticTemplates222.growG a b c) :=
  ⟨node 9 (cantor a (cantor b c)), value_growG a b c⟩

theorem cProv_rho8 (a b c u : V) : CProv (rho8 a b c u) :=
  ⟨node 10 (cantor a (cantor b (cantor c u))), value_r8 a b c u⟩

theorem cProv_bundle (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    CProv (ArithmeticSeedTemplates222.bundle222 a b c) :=
  ⟨node 11 (cantor a (cantor b c)), value_bundle a b c ha hb⟩

/-- Instantiate the generic finite row8 certificate, without any numeric
constructor injectivity or standardness assumption. -/
theorem cProv_implicational : Lukasiewicz.Implicational (wim : V → V → V) CProv where
  mp := cProv_mp
  rho8 := by
    intro c u a b
    simpa only [ArithmeticTemplates254.rho8, ArithmeticTemplates254.rho8Circuit,
      ArithmeticTemplates254.Circuit.r8, ArithmeticTemplates254.Circuit.eval_im,
      ArithmeticTemplates254.Circuit.eval_input0, ArithmeticTemplates254.Circuit.eval_input1,
      ArithmeticTemplates254.Circuit.eval_input2, ArithmeticTemplates254.Circuit.eval_input3] using
      cProv_rho8 a b c u

theorem cProv_k (a b : V) : CProv (wim a (wim b a)) :=
  Lukasiewicz.k cProv_implicational a b
theorem cProv_s (a b c : V) :
    CProv (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  Lukasiewicz.s cProv_implicational a b c
theorem cProv_peirce (a b : V) : CProv (wim (wim (wim a b) a) a) :=
  Lukasiewicz.peirce cProv_implicational a b
theorem cProv_composition (a b c : V) :
    CProv (wim (wim a b) (wim (wim b c) (wim a c))) :=
  Lukasiewicz.composition cProv_implicational a b c

/-- A fixed finite deduction from the new checker's rho6 and row8. -/
theorem cProv_ex_falso (a : V) : CProv (wim 1 a) := by
  let x : V := wal 0 (wim (wal 0 a) 1)
  let e : V := wim x 1
  have hr : CProv (wim e a) := by
    simpa only [ArithmeticTemplates254.rho6, ArithmeticTemplates254.rho6Circuit,
      ArithmeticTemplates254.Circuit.r6, ArithmeticTemplates254.Circuit.ex,
      ArithmeticTemplates254.Circuit.neg, ArithmeticTemplates254.Circuit.eval_im,
      ArithmeticTemplates254.Circuit.eval_al, ArithmeticTemplates254.Circuit.eval_input0,
      ArithmeticTemplates254.Circuit.eval_input1, ArithmeticTemplates254.Circuit.eval_one,
      e, x] using cProv_rho6 (0 : V) a
  have hbe : CProv (wim 1 e) := cProv_k 1 x
  have hbea : CProv (wim 1 (wim e a)) := cProv_mp (cProv_k (wim e a) 1) hr
  exact cProv_mp (cProv_mp (cProv_s 1 e a) hbea) hbe

theorem cProv_classical : Kalmar.Classical (wim : V → V → V) 1 CProv where
  mp := cProv_mp
  k := cProv_k
  s := cProv_s
  peirce := cProv_peirce
  efq := cProv_ex_falso

/-- Standard-input binding to the actual C222 relation, not to C254. -/
theorem cProv_nat_iff (n : Nat) : CProv (V := Nat) n ↔ KCode222.C222 n := by
  rw [ArithmeticHistory222Nat.c222_iff_represented]
  change (∃ code : Nat, value code = n + 1) ↔ _
  exact exists_congr fun code => by
    have h := (check_defined (V := Nat)).df ![code, n]
    change checkDef.val.Evalb ![code, n] ↔ value code = n + 1 at h
    exact h.symm

end LeanProofs.ZFCinPA.ValidatorProvability222

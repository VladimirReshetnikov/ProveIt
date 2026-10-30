import BusyBeaver.ZFC.ArithmeticProofConstructors254

set_option autoImplicit false
noncomputable section

/-!
The literal validator's Sigma1 theorem predicate, with the original twelve
rule closures supplied by existing numeric proof constructors. A polymorphic
finite Lukasiewicz certificate supplies K/S/Peirce without a syntax-code or
standardness assumption; rho6 supplies ex falso at the literal false code1.
This is a target interface for a later internal sequent translation, not
that translation or a reverse consistency theorem.
-/
namespace LeanProofs.ZFCinPA.ValidatorProvability254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticHistory254
open ArithmeticProofConstructors254
open ArithmeticTemplates254 (rho2 rho3 rho4 rho5 rho6 rho7 rho8 bundle)
open scoped LO.FirstOrder.Arithmetic

/-- The fixed arithmetic graph is chosen before any ambient model. -/
def cProvDef : 𝚺₁.Semisentence 1 := .mkSigma
  “conclusion. ∃ code, !ArithmeticHistory254.checkDef code conclusion”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CProv (conclusion : V) : Prop := ∃ code : V, value code = conclusion+1

instance cProv_defined : 𝚺₁-Predicate[V] CProv via cProvDef :=
  .mk fun e => by simp [cProvDef,CProv]
instance cProv_definable : 𝚺₁-Predicate[V] CProv := cProv_defined.to_definable

lemma cProv_truth : CProv (0 : V) := ⟨1,by simpa using value_truth (V := V)⟩

/-- Major premise first, as in the target propositional interface; the literal
MP node itself stores conclusion, minor-code, major-code in that order. -/
lemma cProv_mp {a b : V} (hi : CProv (wim a b)) (ha : CProv a) : CProv b := by
  obtain ⟨di,hi⟩ := hi
  obtain ⟨da,ha⟩ := ha
  exact ⟨node 1 (cantor b (cantor da di)),value_mp b a (wim a b) da di ha hi rfl⟩

lemma cProv_gen (a : V) {p : V} (hp : CProv p) : CProv (wal a p) := by
  obtain ⟨d,hd⟩ := hp
  exact ⟨node 2 (cantor a d),value_gen a p d hd⟩

lemma cProv_rho1 (a b : V) : CProv (rho1 a b) :=
  ⟨node 3 (cantor a b),value_r1 a b⟩
lemma cProv_rho2 (a b c : V) : CProv (rho2 a b c) :=
  ⟨node 4 (cantor a (cantor b c)),value_r2 a b c⟩
lemma cProv_rho3 (a b c : V) : CProv (rho3 a b c) :=
  ⟨node 5 (cantor a (cantor b c)),value_r3 a b c⟩
lemma cProv_rho4 (a b c : V) : CProv (rho4 a b c) :=
  ⟨node 6 (cantor a (cantor b c)),value_r4 a b c⟩
lemma cProv_rho5 (a b c : V) : CProv (rho5 a b c) :=
  ⟨node 7 (cantor a (cantor b c)),value_r5 a b c⟩
lemma cProv_rho6 (a b : V) : CProv (rho6 a b) :=
  ⟨node 8 (cantor a b),value_r6 a b⟩
lemma cProv_rho7 (a b c : V) : CProv (rho7 a b c) :=
  ⟨node 9 (cantor a (cantor b c)),value_r7 a b c⟩
lemma cProv_rho8 (a b c u : V) : CProv (rho8 a b c u) :=
  ⟨node 10 (cantor a (cantor b (cantor c u))),value_r8 a b c u⟩
lemma cProv_bundle (a b c : V) (ha : c ≠ a) (hb : c ≠ b) : CProv (bundle a b c) :=
  ⟨node 11 (cantor a (cantor b c)),value_bundle a b c ha hb⟩

/-- These finite certificates are polymorphic in V and the implication
operation. No injectivity of the numeric constructor is needed. -/
lemma cProv_implicational : Lukasiewicz.Implicational (wim : V → V → V) CProv where
  mp := cProv_mp
  rho8 := by
    intro c u a b
    simpa only [ArithmeticTemplates254.rho8,ArithmeticTemplates254.rho8Circuit,
      ArithmeticTemplates254.Circuit.r8,ArithmeticTemplates254.Circuit.eval_im,
      ArithmeticTemplates254.Circuit.eval_input0,ArithmeticTemplates254.Circuit.eval_input1,
      ArithmeticTemplates254.Circuit.eval_input2,ArithmeticTemplates254.Circuit.eval_input3] using
      cProv_rho8 a b c u

lemma cProv_k (a b : V) : CProv (wim a (wim b a)) :=
  Lukasiewicz.k cProv_implicational a b
lemma cProv_s (a b c : V) :
    CProv (wim (wim a (wim b c)) (wim (wim a b) (wim a c))) :=
  Lukasiewicz.s cProv_implicational a b c
lemma cProv_peirce (a b : V) : CProv (wim (wim (wim a b) a) a) :=
  Lukasiewicz.peirce cProv_implicational a b
lemma cProv_composition (a b c : V) :
    CProv (wim (wim a b) (wim (wim b c) (wim a c))) :=
  Lukasiewicz.composition cProv_implicational a b c

/-- Copy only the fixed propositional argument, using actual rho6. -/
lemma cProv_ex_falso (a : V) : CProv (wim 1 a) := by
  let x : V := wal 0 (wim (wal 0 a) 1)
  let e : V := wim x 1
  have hr : CProv (wim e a) := by
    simpa only [ArithmeticTemplates254.rho6,ArithmeticTemplates254.rho6Circuit,
      ArithmeticTemplates254.Circuit.r6,ArithmeticTemplates254.Circuit.ex,
      ArithmeticTemplates254.Circuit.neg,ArithmeticTemplates254.Circuit.eval_im,
      ArithmeticTemplates254.Circuit.eval_al,ArithmeticTemplates254.Circuit.eval_input0,
      ArithmeticTemplates254.Circuit.eval_input1,ArithmeticTemplates254.Circuit.eval_one,
      e,x] using cProv_rho6 (0 : V) a
  have hbe : CProv (wim 1 e) := cProv_k 1 x
  have hbea : CProv (wim 1 (wim e a)) := cProv_mp (cProv_k (wim e a) 1) hr
  exact cProv_mp (cProv_mp (cProv_s 1 e a) hbea) hbe

lemma cProv_classical : Kalmar.Classical (wim : V → V → V) 1 CProv where
  mp := cProv_mp
  k := cProv_k
  s := cProv_s
  peirce := cProv_peirce
  efq := cProv_ex_falso

/-- Standard-input adapter only; the closure laws above are all-internal. -/
lemma cProv_nat_iff (n : Nat) : CProv (V := Nat) n ↔ Code254.C254 n := by
  rw [ArithmeticHistory254.c254_iff_represented]
  change (∃ code : Nat, value code = n+1) ↔ _
  exact exists_congr fun code => by
    have h := (check_defined (V := Nat)).df ![code,n]
    change checkDef.val.Evalb ![code,n] ↔ value code = n+1 at h
    exact h.symm

end LeanProofs.ZFCinPA.ValidatorProvability254

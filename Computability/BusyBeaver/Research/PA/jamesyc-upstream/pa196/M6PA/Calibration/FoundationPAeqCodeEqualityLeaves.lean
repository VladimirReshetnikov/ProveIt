module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeEqualitySyntax
public import M6PA.Calibration.PAInterpretedFixedClosure
@[expose] public section
/-! Exact finite equality axiom instances for arbitrary model-valued terms.
Proof strategy follows Foundation Bootstrapping/DerivabilityCondition/EquationalTheory
(Apache-2.0), specialized additively to PAeq's distinct signature. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
@[simp] theorem typed_quote_raw_all {n : Nat} (p : Semiproposition Presentation.language (n+1)) :
    (⌜FFL.FirstOrder.Semiformula.all p⌝ : Bootstrapping.Semiformula V Presentation.language n)=∀¹⌜p⌝ := by
  change (⌜∀¹ p⌝ : Bootstrapping.Semiformula V Presentation.language n)=_
  simp
@[simp] theorem typed_quote_raw_or {n : Nat} (p q : Semiproposition Presentation.language n) :
    (⌜FFL.FirstOrder.Semiformula.or p q⌝ : Bootstrapping.Semiformula V Presentation.language n)=⌜p⌝ ⋎ ⌜q⌝ := by
  change (⌜p ⋎ q⌝ : Bootstrapping.Semiformula V Presentation.language n)=_
  simp

local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V:=V) (L:=Presentation.language)
local infix:50 " ≐ₚ " => typedEq

theorem fixed_internal (p : Proposition Presentation.language) (hp : p∈Presentation.fixedAxioms) :
    (U).internalize V ⊢ (⌜p⌝ : Bootstrapping.Formula V Presentation.language) := by
  apply (tprovable_iff_provable (T:=U)).mpr
  apply Derivable.toProvable
  apply Derivable.by_axm (by simp) (⌜p⌝ : V) (by simp [Semiformula.quote_def])
  apply (ordinaryPAeq_mem_iff (⌜p⌝ : V)).mpr
  left; refine ⟨p,hp,?_⟩
  rw [←Sentence.quote_eq_encode,Sentence.quote_def,ForwardRelational.fixedAxiom_univCl p hp]

theorem equality_refl (t : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ t ≐ₚ t := by
  have h : (U).internalize V ⊢ ∀¹ (#'0 ≐ₚ #'0) := by
    simpa [Presentation.reflexivity] using fixed_internal (V:=V) Presentation.reflexivity (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize! h t

theorem equality_symm (t u : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ (t ≐ₚ u) 🡒 (u ≐ₚ t) := by
  have h : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (#'0 ≐ₚ #'1)) := by
    simpa [Presentation.symmetry,Presentation.implies,←Semiformula.neg_eq,Bootstrapping.Semiformula.imp_def] using
      fixed_internal (V:=V) Presentation.symmetry (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize₂! h u t

theorem equality_trans (t u v : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ (t ≐ₚ u) 🡒 (u ≐ₚ v) 🡒 (t ≐ₚ v) := by
  have h : (U).internalize V ⊢ ∀¹ ∀¹ ∀¹ ((#'2 ≐ₚ #'1) 🡒 (#'1 ≐ₚ #'0) 🡒 (#'2 ≐ₚ #'0)) := by
    simpa [Presentation.transitivity,Presentation.implies,←Semiformula.neg_eq,Bootstrapping.Semiformula.imp_def] using
      fixed_internal (V:=V) Presentation.transitivity (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize₃! h v u t

theorem equality_succ (t u : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ (t ≐ₚ u) 🡒 (typedSucc t ≐ₚ typedSucc u) := by
  have h : (U).internalize V ⊢ ∀¹ ∀¹ ((#'0 ≐ₚ #'1) 🡒 (typedSucc #'0 ≐ₚ typedSucc #'1)) := by
    simpa [Presentation.succCongruence,Presentation.implies,←Semiformula.neg_eq,Bootstrapping.Semiformula.imp_def] using
      fixed_internal (V:=V) Presentation.succCongruence (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize₂! h t u

theorem equality_add (t u v w : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ (t ≐ₚ u) 🡒 (v ≐ₚ w) 🡒 (typedAdd t v ≐ₚ typedAdd u w) := by
  have h : (U).internalize V ⊢ ∀¹ ∀¹ ∀¹ ∀¹ ((#'0 ≐ₚ #'1) 🡒 (#'2 ≐ₚ #'3) 🡒 (typedAdd #'0 #'2 ≐ₚ typedAdd #'1 #'3)) := by
    simpa [Presentation.addCongruence,Presentation.implies,←Semiformula.neg_eq,Bootstrapping.Semiformula.imp_def] using
      fixed_internal (V:=V) Presentation.addCongruence (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize₄! h t u v w

theorem equality_mul (t u v w : Bootstrapping.Term V Presentation.language) :
    (U).internalize V ⊢ (t ≐ₚ u) 🡒 (v ≐ₚ w) 🡒 (typedMul t v ≐ₚ typedMul u w) := by
  have h : (U).internalize V ⊢ ∀¹ ∀¹ ∀¹ ∀¹ ((#'0 ≐ₚ #'1) 🡒 (#'2 ≐ₚ #'3) 🡒 (typedMul #'0 #'2 ≐ₚ typedMul #'1 #'3)) := by
    simpa [Presentation.mulCongruence,Presentation.implies,←Semiformula.neg_eq,Bootstrapping.Semiformula.imp_def] using
      fixed_internal (V:=V) Presentation.mulCongruence (by simp [Presentation.fixedAxioms])
  simpa using TProof.specialize₄! h t u v w

#print axioms typed_quote_raw_all
#print axioms typed_quote_raw_or
#print axioms fixed_internal
#print axioms equality_refl
#print axioms equality_symm
#print axioms equality_trans
#print axioms equality_succ
#print axioms equality_add
#print axioms equality_mul
end M6.PA.FoundationPAeqCode

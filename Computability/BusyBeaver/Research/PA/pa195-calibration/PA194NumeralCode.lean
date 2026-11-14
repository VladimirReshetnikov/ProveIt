import DiophantineConsistency.PRAHistoryPairCode

/-! Explicit finite PR constants for fixed syntax tags and symbol codes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194NumeralCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def numeralCode (m : Nat) : Nat → Code m
  | 0 => .zero m
  | n+1 => .comp Code.succ (.cons (numeralCode m n) (.nil m))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelNumeralCode (m n : Nat) (e : Fin m → M) :
    Structure.func (L := language) (numeralCode m n) e = (n : M) := by
  induction n with
  | zero => exact PRAMultiplication.modelZero e
  | succ n ih =>
    rw [numeralCode,modelComposition]
    have he : (fun i : Fin 1 => Structure.func (L := language)
        (getCode (.cons (numeralCode m n) (.nil m)) i) e) = (fun _ : Fin 1 => (n : M)) := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.elim0 j) i
      exact ih
    rw [he, ←modelAddOne]
    change (n : M) + 1 = ((n+1 : Nat) : M)
    simp
end models

/-- All arity variants of the same fixed numeral agree in candidate PRA. -/
def numeralGraphSentence (m n : Nat) : Sentence language := ∀⁰*
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func (numeralCode m n) Semiterm.bvar,.func (numeralCode 0 n) Fin.elim0] : Semisentence language m)

theorem PRA_proves_numeralGraph (m n : Nat) : PRA ⊢ numeralGraphSentence m n := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, numeralGraphSentence, Semiformula.eval_allClosure]
  intro e
  simp only [Semiformula.eval_rel, eqRel, Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Semiterm.val_func]
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ Semiterm.bvar) = e := by
    funext i
    rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have he0 : (fun i : Fin 0 => Semiterm.val (L := language) e Empty.elim (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [Semiterm.val_bvar, he0]
  exact (modelNumeralCode m n e).trans (modelNumeralCode 0 n Fin.elim0).symm

#print axioms PRA_proves_numeralGraph
#print axioms modelNumeralCode
end PA194NumeralCode

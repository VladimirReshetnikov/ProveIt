import PA194TargetLeaves
import PA194TargetHead1Standard
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetLeavesStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PA194NumeralCode PA194TargetCantor PA194TargetHead1Standard PA194TargetLeaves
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem localThree_eq : (3 : M) = F (numeralCode 0 3) Fin.elim0 := by
  symm; simpa using modelNumeralCode 0 3 (Fin.elim0 : Fin 0 → M)
end models

local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA

theorem primitive_standard (a b : Nat) :
    impValue a b = PA196.Commands.Code.I a b ∧
    allValue a b = PA196.Commands.Code.U a b ∧
    negValue a = PA196.Commands.Code.N a ∧
    exValue a b = PA196.Commands.Code.ex a b ∧
    memValue a b = PA196.Commands.Code.M a b ∧
    eqValue a b = PA196.Commands.Code.E a b := by
  have hp (x y : Nat) := modelCantorSelected (M := Nat) fixedCantor fixedCantor_certified x y
  have heval (x y : Nat) : Structure.func (L := language) fixedCantor ![x,y] = M6.Source.Cantor.pair x y := by
    change eval fixedCantor (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_fixedCantor x y
  have hpair := fun x y => (hp x y).symm.trans (heval x y)
  have hadd (x y : Nat) := localAdd_eq (M := Nat) x y
  have hmul (x y : Nat) := localMul_eq (M := Nat) x y
  have hA (x y : Nat) : Structure.func (L := language) addCode ![x,y] = x+y := by
    change eval addCode (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_addCode x y
  have hM (x y : Nat) : Structure.func (L := language) mulCode ![x,y] = x*y := by
    change eval mulCode (List.Vector.ofFn ![x,y]) = _
    rw [ofFn_two]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using eval_mulCode x y
  have hadd' := fun x y => (hadd x y).trans (hA x y)
  have hmul' := fun x y => (hmul x y).trans (hM x y)
  have h1 := localOne_eq (M := Nat)
  have h2 := localTwo_eq (M := Nat)
  have h4 := localFour_eq (M := Nat)
  change _ = eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) at h1
  change _ = eval (numeralCode 0 2) (List.Vector.ofFn Fin.elim0) at h2
  change _ = eval (numeralCode 0 4) (List.Vector.ofFn Fin.elim0) at h4
  have e1 : eval (numeralCode 0 1) (List.Vector.ofFn Fin.elim0) = 1 := by decide
  have e2 : eval (numeralCode 0 2) (List.Vector.ofFn Fin.elim0) = 2 := by decide
  have e4 : eval (numeralCode 0 4) (List.Vector.ofFn Fin.elim0) = 4 := by decide
  rw [e1] at h1
  rw [e2] at h2
  rw [e4] at h4
  have h3 := localThree_eq (M := Nat)
  change _ = eval (numeralCode 0 3) (List.Vector.ofFn Fin.elim0) at h3
  have e3 : eval (numeralCode 0 3) (List.Vector.ofFn Fin.elim0) = 3 := by decide
  rw [e3] at h3
  simp only [impValue,allValue,negValue,exValue,memValue,eqValue,hpair,
    PA196.Commands.Code.I,PA196.Commands.Code.U,PA196.Commands.Code.N,
    PA196.Commands.Code.ex,PA196.Commands.Code.M,PA196.Commands.Code.E]
  simp only [hadd',hmul',h1,h2,h3,h4]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem ofFn_three (a b c : Nat) : List.Vector.ofFn (![a,b,c] : Fin 3 → Nat) =
    a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun z => Fin.elim0 z) k

theorem ofFn_four (a b c d : Nat) : List.Vector.ofFn (![a,b,c,d] : Fin 4 → Nat) =
    a ::ᵥ b ::ᵥ c ::ᵥ d ::ᵥ List.Vector.nil := by
  ext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun l => ?_) k
  exact Fin.cases rfl (fun z => Fin.elim0 z) l

theorem eval_head2 (d a h : Nat) : eval head2 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil) = PA196.Commands.Code.head2 d a h := by
  have hh := head2_model (M := Nat) d a h
  change eval head2 (List.Vector.ofFn ![d,a,h]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [head2Value,PA196.Commands.Code.head2,(primitive_standard _ _).1,(primitive_standard _ _).2.1]

theorem eval_head3 (d a h : Nat) : eval head3 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil) = PA196.Commands.Code.head3 d a h := by
  have hh := head3_model (M := Nat) d a h
  change eval head3 (List.Vector.ofFn ![d,a,h]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [head3Value,PA196.Commands.Code.head3,(primitive_standard _ _).1,
    (primitive_standard _ _).2.2.2.2.1,(primitive_standard _ _).2.2.2.2.2]

theorem eval_head4 (d a h : Nat) : eval head4 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil) = PA196.Commands.Code.head4 d a h := by
  have hh := head4_model (M := Nat) d a h
  change eval head4 (List.Vector.ofFn ![d,a,h]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [head4Value,PA196.Commands.Code.head4,(primitive_standard _ _).1,
    (primitive_standard _ _).2.2.2.2.1,(primitive_standard _ _).2.2.2.2.2]

theorem eval_head5 (d h : Nat) : eval head5 (d ::ᵥ h ::ᵥ List.Vector.nil) = PA196.Commands.Code.head5 d h := by
  have hh := head5_model (M := Nat) d h
  change eval head5 (List.Vector.ofFn ![d,h]) = _ at hh
  rw [ofFn_two] at hh
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [hh]
  simp only [head5Value,PA196.Commands.Code.head5,(primitive_standard _ _).2.2.2.1,
    (primitive_standard _ _).2.2.2.2.2]

theorem eval_head6 (d a h : Nat) : eval head6 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil) = PA196.Commands.Code.head6 d a h := by
  have hh := head6_model (M := Nat) d a h
  change eval head6 (List.Vector.ofFn ![d,a,h]) = _ at hh
  rw [ofFn_three] at hh
  rw [hh]
  simp only [head6Value,PA196.Commands.Code.head6,(primitive_standard _ _).1,(primitive_standard _ _).2.1]

theorem eval_rho8 (a b c u : Nat) : eval rho8 (a ::ᵥ b ::ᵥ c ::ᵥ u ::ᵥ List.Vector.nil) = PA196.Commands.Code.rho8 a b c u := by
  have hh := rho8_model (M := Nat) a b c u
  change eval rho8 (List.Vector.ofFn ![a,b,c,u]) = _ at hh
  rw [ofFn_four] at hh
  rw [hh]
  simp only [rho8Value,PA196.Commands.Code.rho8,(primitive_standard _ _).1]

theorem eval_diagonal (c : Nat) : eval diagonal (c ::ᵥ List.Vector.nil) = PA194AXSymbolic.diagonal c := by
  have hh := diagonal_model (M := Nat) c
  change eval diagonal (List.Vector.ofFn ![c]) = _ at hh
  have ho : List.Vector.ofFn (![c] : Fin 1 → Nat) = c ::ᵥ List.Vector.nil := by
    ext i
    exact Fin.cases rfl (fun z => Fin.elim0 z) i
  rw [ho] at hh
  rw [hh]
  simp only [diagonalValue,PA194AXSymbolic.diagonal,(primitive_standard _ _).1,(primitive_standard _ _).2.1]

noncomputable def head2_derivation (d a h : Nat) :
    PA194DerivationCompiler.Derivation (eval head2 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil)) := by
  rw [eval_head2]
  exact .h2 d a h

noncomputable def head3_derivation (d a h : Nat) :
    PA194DerivationCompiler.Derivation (eval head3 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil)) := by
  rw [eval_head3]
  exact .h3 h d a

noncomputable def head4_derivation (d a h : Nat) :
    PA194DerivationCompiler.Derivation (eval head4 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil)) := by
  rw [eval_head4]
  exact .h4 h d a

noncomputable def head5_derivation (d h : Nat) :
    PA194DerivationCompiler.Derivation (eval head5 (d ::ᵥ h ::ᵥ List.Vector.nil)) := by
  rw [eval_head5]
  exact .h5 d h

noncomputable def head6_derivation (d a h : Nat) :
    PA194DerivationCompiler.Derivation (eval head6 (d ::ᵥ a ::ᵥ h ::ᵥ List.Vector.nil)) := by
  rw [eval_head6]
  exact .h6 d a h

noncomputable def rho8_derivation (a b c u : Nat) (guard : u ≤ a) :
    PA194DerivationCompiler.Derivation (eval rho8 (a ::ᵥ b ::ᵥ c ::ᵥ u ::ᵥ List.Vector.nil)) := by
  rw [eval_rho8]
  exact .r8 a b c u guard

noncomputable def diagonal_derivation (c : Nat) :
    PA194DerivationCompiler.Derivation (eval diagonal (c ::ᵥ List.Vector.nil)) := by
  rw [eval_diagonal]
  exact .diagonal c

#print axioms eval_head2
#print axioms eval_head3
#print axioms eval_head4
#print axioms eval_head5
#print axioms eval_head6
#print axioms eval_rho8
#print axioms eval_diagonal
#print axioms head2_derivation
#print axioms head3_derivation
#print axioms head4_derivation
#print axioms head5_derivation
#print axioms head6_derivation
#print axioms rho8_derivation
#print axioms diagonal_derivation
end PA194TargetLeavesStandard

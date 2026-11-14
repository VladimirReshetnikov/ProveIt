import PA194TargetVectorLength
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetProofLeaf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetLeaves PA194TargetGate
noncomputable def rootCode : Code 1 :=
  bin lookup (.zero 1) (app3 autoHistory (unary lengthCode (.proj 0)) (.proj 0) (.zero 1))

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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rootCode_model (program : M) : F rootCode ![program] =
    F lookup ![0,F autoHistory ![len program,program,0]] := by
  rw [rootCode,modelBin,PRAMultiplication.modelZero,app3_model,modelUnary,modelProjection,PRAMultiplication.modelZero]
  simp only [Matrix.cons_val_zero]
  have hv : (fun _ : Fin 1 => program) = ![program] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv,length_model]
  have hz : F (Code.zero 1) ![program] = (0 : M) := by
    rw [PRAMultiplication.modelZero]
    rfl
  rw [hz]
  rfl

def TargetProof (program result : M) : Prop :=
  0 < len program ∧ F rootCode ![program] = result + 1

def TargetProvable (result : M) : Prop := ∃ program, TargetProof program result

theorem targetProof_def_generic (f g : M → M) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Relation (fun program result => 0 < g program ∧ f program = result + 1) := by
  haveI := hf
  haveI := hg
  definability

theorem targetProof_definable : 𝚺₁-Relation (TargetProof : M → M → Prop) := by
  have hf : 𝚺₁-Function₁ (fun program : M => F rootCode ![program]) := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F rootCode e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) rootCode)
    convert h using 1
    funext e
    change F rootCode ![e 0] = F rootCode e
    apply congrArg (fun x : Fin 1 → M => F rootCode x)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  exact targetProof_def_generic (fun program : M => F rootCode ![program]) len hf inferInstance

theorem targetProvable_definable : 𝚺₁-Predicate (TargetProvable : M → Prop) := by
  haveI := targetProof_definable (M := M)
  unfold TargetProvable
  definability

theorem one_line (line : M) :
    F lookup ![0,F autoHistory ![len (line ∷ 0),line ∷ 0,0]] = F extended ![0,0,line] := by
  have hbase : F autoHistory ![0,line ∷ 0,0] = 0 := PA194ParamHistory.modelBase autoNext (line ∷ 0) 0
  have h := autoHistory_newest (M := M) 0 (line ∷ 0) 0
  simp only [len_adjoin,len_nil,zero_add] at ⊢
  simpa [hbase] using h

theorem one_line_provable (line result : M)
    (h : F extended ![0,0,line] = result + 1) : TargetProvable result := by
  refine ⟨line ∷ (0 : M), ?_⟩
  constructor
  · simp
  · rw [rootCode_model,one_line]
    exact h

theorem head1_provable (a b : M) : TargetProvable (F machineHead1 ![a,b]) := by
  apply one_line_provable (pair 0 (pair a b))
  rw [fallback 0 0 0 (pair a b) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),leaf_step,
    PA194Head1Checker.check_model]
  simp

theorem head2_provable (a b c : M) : TargetProvable (head2Value a b c) := by
  apply one_line_provable (pair 3 (pair a (pair b (pair c 0))))
  exact tag3 0 0 a b c 0

theorem head3_provable (a b c : M) : TargetProvable (head3Value a b c) := by
  apply one_line_provable (pair 4 (pair a (pair b (pair c 0))))
  exact tag4 0 0 a b c 0

theorem head4_provable (a b c : M) : TargetProvable (head4Value a b c) := by
  apply one_line_provable (pair 5 (pair a (pair b (pair c 0))))
  exact tag5 0 0 a b c 0

theorem head5_provable (a b : M) : TargetProvable (head5Value a b) := by
  apply one_line_provable (pair 6 (pair a (pair b (pair 0 0))))
  exact tag6 0 0 a b 0 0

theorem head6_provable (a b c : M) : TargetProvable (head6Value a b c) := by
  apply one_line_provable (pair 7 (pair a (pair b (pair c 0))))
  exact tag7 0 0 a b c 0

theorem rho8_provable (a b c u : M) (h : u ≤ a) : TargetProvable (rho8Value a b c u) := by
  apply one_line_provable (pair 8 (pair a (pair b (pair c u))))
  rw [tag8,if_neg (not_lt_of_ge h)]

theorem gate_provable (a b c : M) (ha : c ≠ a) (hb : c ≠ b) : TargetProvable (oldBundleValue a b c) := by
  apply one_line_provable (pair 9 (pair a (pair b (pair c 0))))
  rw [tag9,if_neg ha,if_neg hb]

theorem diagonal_provable (a : M) : TargetProvable (diagonalValue a) := by
  apply one_line_provable (pair 10 (pair a (pair 0 (pair 0 0))))
  exact tag10 0 0 a 0 0 0

theorem target_leaf_closure : LeafClosure (TargetProvable : M → Prop) where
  head2 := head2_provable
  head3 := head3_provable
  head4 := head4_provable
  head5 := head5_provable
  head6 := head6_provable
  rho8 := rho8_provable
  gate := gate_provable
  diagonal := diagonal_provable

theorem targetProof_sound (G : M → Prop) (hG : 𝚺₁-Predicate G)
    (hLeaf : ∀ a b, G (F machineHead1 ![a,b]))
    (hGen : ∀ label a, G a → G (allValue label a))
    (hMP : ∀ a b, G a → G (impValue a b) → G b)
    (hNew : LeafClosure G) (program result : M) (hp : TargetProof program result) : G result := by
  obtain ⟨hn,hroot⟩ := hp
  rw [rootCode_model] at hroot
  exact autoAccepted_sound G hG hLeaf hGen hMP hNew program 0 (len program) 0 result hn hroot

#print axioms target_leaf_closure
#print axioms targetProof_sound
#print axioms targetProvable_definable
#print axioms rootCode_model
#print axioms one_line
#print axioms head1_provable
#print axioms head2_provable
#print axioms head3_provable
#print axioms head4_provable
#print axioms head5_provable
#print axioms head6_provable
#print axioms rho8_provable
#print axioms gate_provable
#print axioms diagonal_provable
end models
end PA194TargetProofLeaf

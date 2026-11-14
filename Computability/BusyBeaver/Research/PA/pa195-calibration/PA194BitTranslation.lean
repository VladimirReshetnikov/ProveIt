import DiophantineConsistency.PRAHistoryInsertCode

/-! Free-label preservation for the PA194 membership atom translation. -/
set_option autoImplicit false
set_option maxHeartbeats 20000
namespace PA194BitTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency

def substituteTwo (φ : ArithmeticSemisentence 2) (a b : Nat) : ArithmeticFormula Nat :=
  (Rew.embSubsts ![(&a : ArithmeticTerm Nat),&b] : Rew ℒₒᵣ Empty 2 Nat 0) ▹ φ

theorem substituteTwo_free (φ : ArithmeticSemisentence 2) (a b x : Nat)
    (h : (substituteTwo φ a b).FVar? x) : x = a ∨ x = b := by
  unfold substituteTwo at h
  rcases Semiformula.fvar?_rew (φ := φ)
    (ω := (Rew.embSubsts ![(&a : ArithmeticTerm Nat),&b] : Rew ℒₒᵣ Empty 2 Nat 0)) h with
    (⟨i,hi⟩ | ⟨z,_,_⟩)
  · have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl
    · left
      simpa only [Rew.embSubsts_bvar, Matrix.cons_val_zero, Semiterm.fvar?_fvar, eq_comm] using hi
    · right
      simpa only [Rew.embSubsts_bvar, Matrix.cons_val_one, Matrix.cons_val_zero, Semiterm.fvar?_fvar, eq_comm] using hi
  · exact Empty.elim z

@[irreducible] noncomputable def bitMatrix : ArithmeticSemisentence 2 := bitDef.val

/-- Arithmetic bit translation uses source labels only as free arguments;
quantified helper variables remain de Bruijn bound variables. -/
noncomputable def bitTranslation (a b : Nat) : ArithmeticFormula Nat :=
  substituteTwo bitMatrix a b

theorem bitTranslation_free (a b x : Nat) (h : (bitTranslation a b).FVar? x) :
    x = a ∨ x = b := substituteTwo_free bitMatrix a b x h
theorem bitMatrix_eq : bitMatrix = bitDef.val := by
  rw [bitMatrix]

/-- Its semantics is exactly the Foundation bit graph with those two labels. -/
theorem bitTranslation_eval {V : Type*} [ORingStructure V]
    (a b : Nat) (e : Nat → V) :
    (bitTranslation a b).Eval Fin.elim0 e ↔ bitDef.val.Evalb ![e a,e b] := by
  rw [bitTranslation, substituteTwo, Semiformula.eval_rew]
  have hv : (Semiterm.val (L := ℒₒᵣ) Fin.elim0 e ∘
      (Rew.embSubsts ![(&a : ArithmeticTerm Nat),&b] : Rew ℒₒᵣ Empty 2 Nat 0) ∘ Semiterm.bvar) =
      ![e a,e b] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hf : (Semiterm.val (L := ℒₒᵣ) Fin.elim0 e ∘
      (Rew.embSubsts ![(&a : ArithmeticTerm Nat),&b] : Rew ℒₒᵣ Empty 2 Nat 0) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  rw [hv,hf,bitMatrix_eq]

#print axioms bitTranslation_free
#print axioms bitTranslation_eval
end PA194BitTranslation

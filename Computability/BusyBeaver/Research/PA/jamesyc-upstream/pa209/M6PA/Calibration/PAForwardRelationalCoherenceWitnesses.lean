module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceCoverage
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph
attribute [local irreducible] Ordinal.domain Ordinal.successor

def successorValueElim {Γ : List Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (r : Term 0) (q : Form)
    (h : ND.Proof Γ (value (Presentation.succ t) b f r))
    (k : ND.Proof ((value t (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (Rew.shift r)) :: shifted Γ) q.shift) :
    ND.Proof Γ q := by
  apply exsElim (andRight h)
  convert k using 1 <;> valueWitnessSyntax

inductive BinaryOperation | addition | multiplication

def BinaryOperation.term {n : Nat} : BinaryOperation → SourceTerm n → SourceTerm n → SourceTerm n
  | .addition => Presentation.add
  | .multiplication => Presentation.mul

def BinaryOperation.result {m : Nat} : BinaryOperation → Term m → Term m → Term m → Formula m
  | .addition => addResult
  | .multiplication => mulResult

theorem BinaryOperation.result_rew {m k : Nat} (op : BinaryOperation)
    (τ : Rew language Nat m Nat k) (x y z : Term m) :
    Semiformula.rewAux τ (op.result x y z) = op.result (τ x) (τ y) (τ z) := by
  cases op
  · exact addResult_rew τ x y z
  · exact mulResult_rew τ x y z

def binaryWitness {n : Nat} (op : BinaryOperation) (u v : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (r : Term 0) : Form :=
  value u (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1) ⋏
    (value v (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0) ⋏
      op.result (.fvar 1) (.fvar 0) (Rew.shift (Rew.shift r)))

/-- Eliminate both real child witnesses. The unused outer existential hypothesis
is removed by explicit weakening, leaving only the actual witness conjunction. -/
def binaryValueElim {Γ : List Form} {n : Nat} (op : BinaryOperation) (u v : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (r : Term 0) (q : Form)
    (h : ND.Proof Γ (value (op.term u v) b f r))
    (k : ND.Proof (binaryWitness op u v b f r :: shifted (shifted Γ)) q.shift.shift) :
    ND.Proof Γ q := by
  have hh : ND.Proof Γ (∃¹ ∃¹ (value u (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
      (value v (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
        op.result (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift r))))) := by
    cases op <;> exact andRight h
  apply exsElim hh
  apply exsElim (assumption (List.mem_cons_self))
  have kk := weaken k (Δ := binaryWitness op u v b f r ::
    shifted ((∃¹ (value u (shiftEnv (freeShiftEnv b)) (shiftEnv (freeShiftEnv f)) (.fvar 0) ⋏
      (value v (shiftEnv (freeShiftEnv b)) (shiftEnv (freeShiftEnv f)) (.bvar 0) ⋏
        BinaryOperation.result op (.fvar 0) (.bvar 0) (Rew.bShift (Rew.shift r))))) :: shifted Γ)) (by
      intro p hp
      simp only [shifted,List.map_cons,List.mem_cons] at hp ⊢
      exact hp.elim Or.inl (fun h => Or.inr (Or.inr h)))
  convert kk using 1 <;> (simp only [binaryWitness]; simp only [Semiformula.free,Rewriting.free,app_eq_rewAux,Semiformula.rewAux,BinaryOperation.result_rew]; valueWitnessSyntax)
  all_goals first | exact ⟨⟨rfl,rfl⟩,rfl⟩ | rfl

#print axioms successorValueElim
#print axioms binaryValueElim
end M6.PA.ForwardRelational

import ZFCinPA.ValidatorEnvironmentLabels254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_nil
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_cons_zero
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_cons_succ
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.tail_nil
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.tail_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.freeLabel_tail
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.positive_label
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.below_label
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.positive_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.below_cons
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.vec_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.vec_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_bvar
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_fvar
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_func
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.vec_length
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.vec_nth
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.term_shift
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.TermLabels.vec_shift
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.nextState_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.Formulas.atom_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encodeState_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_defined
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_delta
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_of_not_formula
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_verum
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_falsum
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_rel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_nrel
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_and
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_or
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_all
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_exs
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.atom_shift
#print axioms LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254.encode_shift

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (F j : V) : freeLabelDef.val.Evalb ![freeLabel F j,F,j] := by simp
example (F j : V) : ∃! out : V, freeLabelDef.val.Evalb ![out,F,j] := by simp
example (j : V) : freeLabel (0 : V) j=1 := freeLabel_nil j
example (x F : V) : freeLabel (x∷F) 0=x := freeLabel_cons_zero x F
example (x F j : V) : freeLabel (x∷F) (j+1)=freeLabel F j := freeLabel_cons_succ x F j
example (F j : V) : freeLabel F (j+1)=freeLabel (tail F) j := freeLabel_tail F j
example (F j : V) (hF : Positive F) : 0<freeLabel F j := positive_label hF j
example (F n j : V) (hF : Below F n) : freeLabel F j<n := below_label hF j
example (F B j : V) : TermLabels.term F B (^#j)=B.[j] := TermLabels.term_bvar F B j
example (F B j : V) : TermLabels.term F B (^&j)=freeLabel F j := TermLabels.term_fvar F B j
example (F B k terms i : V) (ht : IsUTermVec ℒₛₑₜ k terms) (hi : i<k) :
    (TermLabels.vec F B k terms).[i]=TermLabels.term F B terms.[i] :=
  TermLabels.vec_nth F B ht hi
example (F B t : V) (ht : IsUTerm ℒₛₑₜ t) :
    TermLabels.term F B (termShift ℒₛₑₜ t)=TermLabels.term (tail F) B t :=
  TermLabels.term_shift ht F B
example (F B k terms : V) (ht : IsUTermVec ℒₛₑₜ k terms) :
    TermLabels.vec F B k (termShiftVec ℒₛₑₜ k terms)=TermLabels.vec (tail F) B k terms :=
  TermLabels.vec_shift F B ht
example (state : V) : nextStateDef.val.Evalb ![nextState state,state] := by simp
example (state p : V) : encodeStateDef.val.Evalb ![encodeState state p,state,p] := by simp
example (F B n p : V) : encodeDef.val.Evalb ![encode F B n p,F,B,n,p] := by simp
example (F B n p : V) : ∃! out : V, encodeDef.val.Evalb ![out,F,B,n,p] := by simp
example (F B n p : V) (hp : ¬IsUFormula ℒₛₑₜ p) : encode F B n p=0 :=
  encode_of_not_formula F B n hp
example (F B n : V) : encode F B n (^⊤ : V)=0 := encode_verum F B n
example (F B n : V) : encode F B n (^⊥ : V)=1 := encode_falsum F B n
example (F B n p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode F B n (^∀ p)=wal n (encode F (n∷B) (n+2) p) := encode_all F B n hp
example (F B n p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode F B n (^∃ p)=wim (wal n (wim (encode F (n∷B) (n+2) p) 1)) 1 := encode_exs F B n hp
example (F B n p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode F B n (shift ℒₛₑₜ p)=encode (tail F) B n p := encode_shift hp F B n
example (F B n p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode F B n (shift ℒₛₑₜ (^∀ p))=encode (tail F) B n (^∀ p) :=
  encode_shift (by simp [hp]) F B n
example (F B n p x : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode (x∷F) B n (shift ℒₛₑₜ p)=encode F B n p := by simpa using encode_shift hp (x∷F) B n
example (j : V) : 0<freeLabel (0 : V) j := by simp
example (F j : V) : TermLabels.term F (0 : V) (^#j)=0 := by simp
example : encode (0 : V) 0 0 (^∀ (^⊤ : V))=wal 0 0 := by
  rw [encode_all 0 0 0 (by simp),encode_verum]

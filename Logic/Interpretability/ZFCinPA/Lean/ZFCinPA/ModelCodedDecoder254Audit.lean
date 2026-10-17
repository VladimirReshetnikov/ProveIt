import ZFCinPA.ModelCodedDecoder254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.atomCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.zeroFormula_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.row_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_seq
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_length
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_lookup_le
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_lookup
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_zero
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_succ_row
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.child_bounds
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.row_isFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.history_formulas
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_isFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoder254.decode_succ

example : 𝚺₁-Function₃[V] atomCode via atomCodeDef := inferInstance
example : 𝚺₁-Function₀[V] zeroFormula via zeroFormulaDef := inferInstance
example (out s code : V) : rowDef.val.Evalb ![out,s,code] ↔ out = row s code := by simp
example (out code : V) : historyDef.val.Evalb ![out,code] ↔ out = history code := by simp
example (code : V) : Seq (history code) := history_seq code
example (code : V) : lh (history code) = code+1 := history_length code
example (out code : V) : decodeDef.val.Evalb ![out,code] ↔ out = decode code := by simp
example (code : V) : ∃! out : V, decodeDef.val.Evalb ![out,code] := by
  refine ⟨decode code,by simp,?_⟩
  intro out h
  simpa using h
example (code : V) : IsFormula ℒₛₑₜ (decode code) := decode_isFormula code
example (code i : V) (hi : i ≤ code) : znth (history code) i = decode i := history_lookup_le code i hi
example (code i : V) (hi : code < i) : znth (history code) i = 0 := by
  rw [history_lookup]
  simp [not_le_of_gt hi]
example : decode (0 : V) = zeroFormula := decode_zero
example (raw : V) : decode (raw+1) = row (history raw) (raw+1) := decode_succ_row raw
example (code : V) (h : 0 < code) :
    ArithmeticCantor.first (code/4) < code ∧ ArithmeticCantor.second (code/4) < code := child_bounds h
example (s code : V) (h : ∀ i < code, IsFormula ℒₛₑₜ (znth s i)) :
    IsFormula ℒₛₑₜ (row s code) := row_isFormula s code h
example (code i : V) (hi : i ≤ code) : IsFormula ℒₛₑₜ (znth (history code) i) := history_formulas code i hi
example (raw : V) (h : (raw+1)%4 = 0) : decode (raw+1) =
    imp ℒₛₑₜ (decode (ArithmeticCantor.first ((raw+1)/4)))
      (decode (ArithmeticCantor.second ((raw+1)/4))) := by
  rw [decode_succ]
  simp [h]
example (raw : V) (h : (raw+1)%4 = 1) : decode (raw+1) =
    atomCode 1 (ArithmeticCantor.first ((raw+1)/4)) (ArithmeticCantor.second ((raw+1)/4)) := by
  rw [decode_succ]
  simp [h]
example (raw : V) (h : (raw+1)%4 = 2) : decode (raw+1) =
    namedAll ℒₛₑₜ (ArithmeticCantor.first ((raw+1)/4))
      (decode (ArithmeticCantor.second ((raw+1)/4))) := by
  rw [decode_succ]
  simp [h]
example (raw : V) (h : (raw+1)%4 = 3) : decode (raw+1) =
    atomCode 0 (ArithmeticCantor.first ((raw+1)/4)) (ArithmeticCantor.second ((raw+1)/4)) := by
  rw [decode_succ]
  simp [h]
example (a b : V) : IsFormula ℒₛₑₜ (atomCode 1 a b) := memCode_isFormula a b
example (a b : V) : IsFormula ℒₛₑₜ (atomCode 0 a b) := eqCode_isFormula a b
example : decode (0 : V) = imp ℒₛₑₜ (atomCode 1 0 0) (atomCode 1 0 0) := decode_zero
example (code : V) :
    history (code+1) = seqCons (history code) (row (history code) (code+1)) := history_succ code

import ZFCinPA.ValidatorFormulaEncoder254
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorFormulaEncoder254
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.term_defined
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.vec_defined
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.term_bvar
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.term_fvar
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.vec_length
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.Labels.vec_nth
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.atom_defined
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_defined
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_definable
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_of_not_formula
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_verum
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_falsum
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_rel
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_nrel
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_and
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_or
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_all
#print axioms LeanProofs.ZFCinPA.ValidatorFormulaEncoder254.encode_exs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out depth t : V) : Labels.termDef.val.Evalb ![out,depth,t] ↔ out=Labels.term depth t := by simp
example (out depth k terms : V) : Labels.vecDef.val.Evalb ![out,depth,k,terms] ↔ out=Labels.vec depth k terms := by simp
example (depth i : V) : Labels.term depth (^#i)=2*(depth-i) := Labels.term_bvar depth i
example (depth j : V) : Labels.term depth (^&j)=2*j+1 := Labels.term_fvar depth j
example (depth : V) {k terms : V} (h : IsUTermVec ℒₛₑₜ k terms) :
    len (Labels.vec depth k terms)=k := Labels.vec_length depth h
example (depth : V) {k terms i : V} (h : IsUTermVec ℒₛₑₜ k terms) (hi : i<k) :
    (Labels.vec depth k terms).[i]=Labels.term depth terms.[i] := Labels.vec_nth depth h hi
example (out depth k symbol terms : V) : atomDef.val.Evalb ![out,depth,k,symbol,terms] ↔
    out=atom depth k symbol terms := by simp
example (out depth p : V) : encodeDef.val.Evalb ![out,depth,p] ↔ out=encode depth p := by simp
example : 𝚫₁-Function₂[V] encode := encode_definable
example (depth p : V) : ∃! out : V, encodeDef.val.Evalb ![out,depth,p] := by simp
example (depth : V) : encode depth (0 : V)=0 := encode_of_not_formula depth (by simp)
example (depth : V) : encode depth (^⊤ : V)=0 := encode_verum depth
example (depth : V) : encode depth (^⊥ : V)=1 := encode_falsum depth
example (depth : V) {k symbol terms : V} (hr : (ℒₛₑₜ).IsRel k symbol) (ht : IsUTermVec ℒₛₑₜ k terms) :
    encode depth (^rel k symbol terms)=atom depth k symbol terms := encode_rel depth hr ht
example (depth : V) {k symbol terms : V} (hr : (ℒₛₑₜ).IsRel k symbol) (ht : IsUTermVec ℒₛₑₜ k terms) :
    encode depth (^nrel k symbol terms)=wim (atom depth k symbol terms) 1 := encode_nrel depth hr ht
example (depth p q : V) (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode depth (p ^⋏ q)=wim (wim (encode depth p) (wim (encode depth q) 1)) 1 := encode_and depth hp hq
example (depth p q : V) (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    encode depth (p ^⋎ q)=wim (wim (encode depth p) 1) (encode depth q) := encode_or depth hp hq
example (depth p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode depth (^∀ p)=wal (2*(depth+1)) (encode (depth+1) p) := encode_all depth hp
example (depth p : V) (hp : IsUFormula ℒₛₑₜ p) :
    encode depth (^∃ p)=wim (wal (2*(depth+1)) (wim (encode (depth+1) p) 1)) 1 := encode_exs depth hp
example (depth a b : V) : encode depth (^rel 2 0 ?[^&a,^&b])=weq (2*a+1) (2*b+1) := by
  have hr : (ℒₛₑₜ).IsRel 2 (0 : V) := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 0)).mpr
      ⟨Language.Set.Rel.eq,rfl⟩
  have ht : IsUTermVec ℒₛₑₜ 2 (?[^&a,^&b] : V) := by simp
  rw [encode_rel depth hr ht]
  simp only [atom,if_pos rfl]
  rw [Labels.vec_nth depth ht (by simp : (0 : V)<2),Labels.vec_nth depth ht (by simp : (1 : V)<2)]
  simp
example (depth a b : V) : encode depth (^rel 2 1 ?[^&a,^&b])=wel (2*a+1) (2*b+1) := by
  have hr : (ℒₛₑₜ).IsRel 2 (1 : V) := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
      ⟨Language.Set.Rel.mem,rfl⟩
  have ht : IsUTermVec ℒₛₑₜ 2 (?[^&a,^&b] : V) := by simp
  rw [encode_rel depth hr ht]
  simp only [atom,if_neg (by simp : (1 : V)≠0)]
  rw [Labels.vec_nth depth ht (by simp : (0 : V)<2),Labels.vec_nth depth ht (by simp : (1 : V)<2)]
  simp
example (depth : V) : encode depth (^∀ (^∃ (^⊤ : V)))=
    wal (2*(depth+1)) (wim (wal (2*((depth+1)+1)) (wim 0 1)) 1) := by
  rw [encode_all depth (by simp),encode_exs (depth+1) (by simp),encode_verum]
example (depth : V) : Labels.term (depth+1) (^#0 : V)=2*(depth+1) := by simp
example (depth : V) : Labels.term depth (^#depth : V)=0 := by simp

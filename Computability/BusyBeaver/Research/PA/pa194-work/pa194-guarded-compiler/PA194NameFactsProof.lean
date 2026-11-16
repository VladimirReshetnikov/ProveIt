import PA194NameSemantics
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The naming facts from twelve fixed facts about the ordinal domain

`SourceFacts T`: the source theory `T` proves, in the internal sense, twelve fixed closed
formulas about the domain, source equality, order isomorphism, zero, successor, addition and
multiplication. `nameFacts_of_sourceFacts`: from these and the existence of a name for every
variable, all fields of `NameFacts T`.

Each field is obtained in the same way: a closed sentence over the letters of
`PA194NameSchema` holds in every structure (`PA194NameSemantics`), so its instance at the
value formulas of the given internal terms is provable (`PA194Schematic`), and the instance
is the translation of the name formula (`PA194NameSchema`, `PA194NameForms`).
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-! ### The sentences and their validity -/

def fRefl : SF 0 := sNameAll (sBox 0) (sBox 0)
def fAtom : SF 0 :=
  sNameAll (sBox 0) (sBox 1) 🡒 sNameAll (sBox 2) (sBox 3) 🡒 sEqVal (sBox 0) (sBox 2) 🡒
    sEqVal (sBox 1) (sBox 3)
def fNameOfUniq : SF 0 := sUniq (sBox 0) 🡒 sEqVal (sBox 1) (sBox 0) 🡒 sNameAll (sBox 0) (sBox 1)
def fNameOfEq : SF 0 := sPair 1 🡒 sEqVal (sBox 1) (sBox 0) 🡒 sNameAll (sBox 1) (sBox 0)
def fNSucc : SF 0 := sNameAll (sBox 0) (sBox 1) 🡒 sNameAll (sSuccV (sBox 0)) (sSuccV (sBox 1))
def fNAdd : SF 0 :=
  sNameAll (sBox 0) (sBox 1) 🡒 sNameAll (sBox 2) (sBox 3) 🡒
    sNameAll (sAddV (sBox 0) (sBox 2)) (sAddV (sBox 1) (sBox 3))
def fNMul : SF 0 :=
  sNameAll (sBox 0) (sBox 1) 🡒 sNameAll (sBox 2) (sBox 3) 🡒
    sNameAll (sMulV (sBox 0) (sBox 2)) (sMulV (sBox 1) (sBox 3))
def fUVar : SF 0 := sPair 0 🡒 sUniq (sBox 0)
def fUZero : SF 0 := sUniq sZeroV
def fUSucc : SF 0 := sUniq (sBox 0) 🡒 sUniq (sSuccV (sBox 0))
def fUAdd : SF 0 := sUniq (sBox 0) 🡒 sUniq (sBox 1) 🡒 sUniq (sAddV (sBox 0) (sBox 1))
def fUMul : SF 0 := sUniq (sBox 0) 🡒 sUniq (sBox 1) 🡒 sUniq (sMulV (sBox 0) (sBox 1))
def fEZero : SF 0 := sExName sZeroV
def fESucc : SF 0 := sExName (sBox 0) 🡒 sExName (sSuccV (sBox 0))
def fEAdd : SF 0 := sExName (sBox 0) 🡒 sExName (sBox 1) 🡒 sExName (sAddV (sBox 0) (sBox 1))
def fEMul : SF 0 := sExName (sBox 0) 🡒 sExName (sBox 1) 🡒 sExName (sMulV (sBox 0) (sBox 1))

section validity
variable (M : Type) [Nonempty M] [s : Structure NL M]

theorem pairOf {i : Fin 4} (hp : ∀ a b : M, mD a → mD b → mL i a → mL i b → mI a b) :
    ∀ a b : M, wOf (sBox i) a → wOf (sBox i) b → mI a b := fun a b ha hb =>
  hp a b ((wOf_sBox i a).mp ha).1 ((wOf_sBox i b).mp hb).1 ((wOf_sBox i a).mp ha).2
    ((wOf_sBox i b).mp hb).2

theorem valid_refl : M↓[NL] ⊧ sWith fRefl := by
  show ev (![] : Fin 0 → M) (sWith fRefl)
  refine (ev_sWith _).mpr fun _ => ?_
  simp only [fRefl, ev_sNameAll]
  exact fun x _ h => h
theorem valid_atom : M↓[NL] ⊧ sWith fAtom := by
  show ev (![] : Fin 0 → M) (sWith fAtom)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fAtom, ev_imp, ev_sNameAll, ev_sEqVal]
  exact m_atomTransfer H (wOf_sBox_dom 0) (wOf_sBox_dom 2) (wOf_sBox_dom 1) (wOf_sBox_dom 3)
theorem valid_nameOfUniq : M↓[NL] ⊧ sWith fNameOfUniq := by
  show ev (![] : Fin 0 → M) (sWith fNameOfUniq)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fNameOfUniq, ev_imp, ev_sNameAll, ev_sEqVal, ev_sUniq]
  exact m_nameOfUniq H (wOf_sBox_dom 0) (wOf_sBox_dom 1)
theorem valid_nameOfEq : M↓[NL] ⊧ sWith fNameOfEq := by
  show ev (![] : Fin 0 → M) (sWith fNameOfEq)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fNameOfEq, ev_imp, ev_sNameAll, ev_sEqVal, ev_sPair]
  exact fun hp => m_nameOfEq H (wOf_sBox_dom 0) (wOf_sBox_dom 1) (pairOf M hp)
theorem valid_nSucc : M↓[NL] ⊧ sWith fNSucc := by
  show ev (![] : Fin 0 → M) (sWith fNSucc)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fNSucc, ev_imp, ev_sNameAll, wOf_sSuccV']
  exact m_nSucc H (wOf_sBox_dom 0) (wOf_sBox_dom 1)
theorem valid_nAdd : M↓[NL] ⊧ sWith fNAdd := by
  show ev (![] : Fin 0 → M) (sWith fNAdd)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fNAdd, ev_imp, ev_sNameAll, wOf_sAddV']
  exact m_nAdd H (wOf_sBox_dom 0) (wOf_sBox_dom 2) (wOf_sBox_dom 1) (wOf_sBox_dom 3)
theorem valid_nMul : M↓[NL] ⊧ sWith fNMul := by
  show ev (![] : Fin 0 → M) (sWith fNMul)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fNMul, ev_imp, ev_sNameAll, wOf_sMulV']
  exact m_nMul H (wOf_sBox_dom 0) (wOf_sBox_dom 2) (wOf_sBox_dom 1) (wOf_sBox_dom 3)
theorem valid_uVar : M↓[NL] ⊧ sWith fUVar := by
  show ev (![] : Fin 0 → M) (sWith fUVar)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fUVar, ev_imp, ev_sUniq, ev_sPair]
  exact fun hp => m_uniqOfValIso H (wOf_sBox_dom 0) (pairOf M hp)
theorem valid_uZero : M↓[NL] ⊧ sWith fUZero := by
  show ev (![] : Fin 0 → M) (sWith fUZero)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fUZero, ev_sUniq, wOf_sZeroV']
  exact m_uZero H
theorem valid_uSucc : M↓[NL] ⊧ sWith fUSucc := by
  show ev (![] : Fin 0 → M) (sWith fUSucc)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fUSucc, ev_imp, ev_sUniq, wOf_sSuccV']
  exact m_uSucc H (wOf_sBox_dom 0)
theorem valid_uAdd : M↓[NL] ⊧ sWith fUAdd := by
  show ev (![] : Fin 0 → M) (sWith fUAdd)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fUAdd, ev_imp, ev_sUniq, wOf_sAddV']
  exact m_uAdd H (wOf_sBox_dom 0) (wOf_sBox_dom 1)
theorem valid_uMul : M↓[NL] ⊧ sWith fUMul := by
  show ev (![] : Fin 0 → M) (sWith fUMul)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fUMul, ev_imp, ev_sUniq, wOf_sMulV']
  exact m_uMul H (wOf_sBox_dom 0) (wOf_sBox_dom 1)
theorem valid_eZero : M↓[NL] ⊧ sWith fEZero := by
  show ev (![] : Fin 0 → M) (sWith fEZero)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fEZero, ev_sExName, wOf_sZeroV']
  exact m_eZero H
theorem valid_eSucc : M↓[NL] ⊧ sWith fESucc := by
  show ev (![] : Fin 0 → M) (sWith fESucc)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fESucc, ev_imp, ev_sExName, wOf_sSuccV']
  exact m_eSucc H (wOf_sBox_dom 0)
theorem valid_eAdd : M↓[NL] ⊧ sWith fEAdd := by
  show ev (![] : Fin 0 → M) (sWith fEAdd)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fEAdd, ev_imp, ev_sExName, wOf_sAddV']
  exact m_eAdd H (wOf_sBox_dom 0) (wOf_sBox_dom 1)
theorem valid_eMul : M↓[NL] ⊧ sWith fEMul := by
  show ev (![] : Fin 0 → M) (sWith fEMul)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fEMul, ev_imp, ev_sExName, wOf_sMulV']
  exact m_eMul H (wOf_sBox_dom 0) (wOf_sBox_dom 1)

end validity

#print axioms valid_atom
#print axioms valid_nameOfEq
#print axioms valid_nAdd
#print axioms valid_uAdd
#print axioms valid_eAdd

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Every value formula starts with the domain formula -/

theorem term_cases {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    (∃ i : V, t = ^&i) ∨ t = zeroT ∨
    (∃ a : V, IsSemiterm PA194PAeq.language 0 a ∧ t = succT a) ∨
    (∃ a b : V, IsSemiterm PA194PAeq.language 0 a ∧ IsSemiterm PA194PAeq.language 0 b ∧
      t = addT a b) ∨
    (∃ a b : V, IsSemiterm PA194PAeq.language 0 a ∧ IsSemiterm PA194PAeq.language 0 b ∧
      t = mulT a b) := by
  rcases IsSemiterm.case_iff.mp ht with ⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩
  · simp at hz
  · exact Or.inl ⟨x, rfl⟩
  · rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.isUTerm.lh.symm
      subst v
      exact Or.inr (Or.inl rfl)
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 0 a := by
        simpa using hv.nth (show (0 : V) < 1 by simp)
      exact Or.inr (Or.inr (Or.inl ⟨a, ha, rfl⟩))
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.isUTerm.lh.symm
      have ha : IsSemiterm PA194PAeq.language 0 a := by
        simpa using hv.nth (show (0 : V) < 2 by simp)
      have hb : IsSemiterm PA194PAeq.language 0 b := by
        simpa using hv.nth (show (1 : V) < 2 by simp)
      rcases htwo with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, ha, hb, rfl⟩)))

theorem valBody_split {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    ∃ r : V, IsSemiformula SourceL 1 r ∧ valBody s = domainCode (^#(0 : V)) ^⋏ r := by
  have hv := valBody_valid hs
  rcases term_cases hs with ⟨i, rfl⟩ | rfl | ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, rfl⟩ |
    ⟨a, b, ha, hb, rfl⟩
  · rw [valBody_fvar] at hv ⊢
    unfold variableValue at hv ⊢
    exact ⟨_, (IsSemiformula.and.mp hv).2, rfl⟩
  · rw [valBody_zero] at hv ⊢
    unfold zeroValue at hv ⊢
    exact ⟨_, (IsSemiformula.and.mp hv).2, rfl⟩
  · rw [valBody_succ ha] at hv ⊢
    unfold successorValue at hv ⊢
    exact ⟨_, (IsSemiformula.and.mp hv).2, rfl⟩
  · rw [valBody_add ha hb] at hv ⊢
    unfold binaryValue at hv ⊢
    exact ⟨_, (IsSemiformula.and.mp hv).2, rfl⟩
  · rw [valBody_mul ha hb] at hv ⊢
    unfold binaryValue at hv ⊢
    exact ⟨_, (IsSemiformula.and.mp hv).2, rfl⟩

/-! ### Typed value formulas with their domain conjunct -/

noncomputable def tBox (R : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 := tDom (Bootstrapping.Semiterm.bvar 0) ⋏ R

@[simp] theorem instS_sBox (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) (i : Fin 4) :
    instS (sig A) (sBox i) = tBox (A i) := by
  simp [sBox, tBox]
theorem tBox_val (R : Bootstrapping.Semiformula V SourceL 1) :
    (tBox R).val = domainCode (^#(0 : V)) ^⋏ R.val := by
  simp [tBox]
theorem boxOf {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    ∃ R : Bootstrapping.Semiformula V SourceL 1, (tBox R).val = valBody s := by
  obtain ⟨r, hr, e⟩ := valBody_split hs
  exact ⟨⟨r, by simpa using hr⟩, by rw [tBox_val, e]⟩
/-- The value formula of a variable: the part after the domain conjunct is "equal to `c`". -/
theorem boxVar (c : V) :
    (tBox (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar c) :
      Bootstrapping.Semiformula V SourceL 1)).val = valBody (^&c : V) := by
  rw [valBody_fvar, tBox_val]
  simp [variableValue]
theorem exA4 (a b c d : Bootstrapping.Semiformula V SourceL 1) :
    ∃ A : Fin 4 → Bootstrapping.Semiformula V SourceL 1, A 0 = a ∧ A 1 = b ∧ A 2 = c ∧ A 3 = d :=
  ⟨![a,b,c,d], rfl, rfl, rfl, rfl⟩

/-! ### The fixed facts about the source theory -/

/-- The instance of a sentence in which no value letter occurs. -/
noncomputable abbrev tHyp (φ : SF 0) : Bootstrapping.Semiformula V SourceL 0 :=
  instS (sig (fun _ => (⊤ : Bootstrapping.Semiformula V SourceL 1))) φ

section hyps
variable (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1)
theorem instS_sE1 : instS (sig A) sE1 = tHyp sE1 := by simp [sE1, tHyp]
theorem instS_sEI : instS (sig A) sEI = tHyp sEI := by simp [sEI, tHyp]
theorem instS_sIs : instS (sig A) sIs = tHyp sIs := by simp [sIs, tHyp]
theorem instS_sIt : instS (sig A) sIt = tHyp sIt := by simp [sIt, tHyp]
theorem instS_sZ1 : instS (sig A) sZ1 = tHyp sZ1 := by simp [sZ1, tHyp]
theorem instS_sZ2 : instS (sig A) sZ2 = tHyp sZ2 := by simp [sZ2, tHyp]
theorem instS_sS1 : instS (sig A) sS1 = tHyp sS1 := by simp [sS1, tHyp]
theorem instS_sS2 : instS (sig A) sS2 = tHyp sS2 := by simp [sS2, tHyp]
theorem instS_sA1 : instS (sig A) sA1 = tHyp sA1 := by simp [sA1, tHyp]
theorem instS_sA2 : instS (sig A) sA2 = tHyp sA2 := by simp [sA2, tHyp]
theorem instS_sM1 : instS (sig A) sM1 = tHyp sM1 := by simp [sM1, tHyp]
theorem instS_sM2 : instS (sig A) sM2 = tHyp sM2 := by simp [sM2, tHyp]
end hyps

variable (T : Theory SourceL) [T.Δ₁]

/-- The source theory proves the twelve fixed facts about its ordinal domain. -/
structure SourceFacts : Prop where
  e1 : T.internalize V ⊢ tHyp sE1
  ei : T.internalize V ⊢ tHyp sEI
  is : T.internalize V ⊢ tHyp sIs
  it : T.internalize V ⊢ tHyp sIt
  z1 : T.internalize V ⊢ tHyp sZ1
  z2 : T.internalize V ⊢ tHyp sZ2
  s1 : T.internalize V ⊢ tHyp sS1
  s2 : T.internalize V ⊢ tHyp sS2
  a1 : T.internalize V ⊢ tHyp sA1
  a2 : T.internalize V ⊢ tHyp sA2
  m1 : T.internalize V ⊢ tHyp sM1
  m2 : T.internalize V ⊢ tHyp sM2

variable {T}

theorem tmp {φ ψ : Bootstrapping.Semiformula V SourceL 0} (h : T.internalize V ⊢ φ 🡒 ψ)
    (h' : T.internalize V ⊢ φ) : T.internalize V ⊢ ψ := ⟨TProof.modusPonens h.get h'.get⟩

/-- Every instance of a sentence that holds in all structures under the twelve hypotheses is
provable. -/
theorem with_facts (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1)
    (S : SourceFacts (V := V) T) (F : SF 0)
    (hF : ∀ (M : Type) [Nonempty M] [Structure NL M], M↓[NL] ⊧ sWith F) :
    T.internalize V ⊢ instS (sig A) F := by
  have h := instS_provable_of_valid (sig A) T (sWith F) hF
  unfold sWith at h
  simp only [instS_imp, instS_sE1, instS_sEI, instS_sIs, instS_sIt, instS_sZ1, instS_sZ2,
    instS_sS1, instS_sS2, instS_sA1, instS_sA2, instS_sM1, instS_sM2] at h
  exact tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp (tmp h S.e1) S.ei) S.is) S.it)
    S.z1) S.z2) S.s1) S.s2) S.a1) S.a2) S.m1) S.m2

/-! ### From provable implications to guarded sequents -/

theorem GDerivable.of_derivable {Δ : V} (h : Derivable T Δ) : GDerivable T Δ :=
  ⟨0, Derivable.wk (IsFormulaSet.union.mpr ⟨guards_valid 0, h.isFormulaSet⟩)
    (fun _ hx => mem_cup_iff.mpr (Or.inr hx)) h⟩
theorem gd_of_tder {Γ : Bootstrapping.Sequent V SourceL} (d : T.internalize V ⊢!ᵈᵉʳ Γ) :
    GDerivable T Γ.val := GDerivable.of_derivable d.toDerivable

theorem gd0 {Y : Bootstrapping.Semiformula V SourceL 0} (h : T.internalize V ⊢ Y) :
    GDerivable T (insert Y.val (∅ : V)) := by
  have b : T.internalize V ⊢!ᵈᵉʳ insert Y ∅ := TProof.toTDerivation h.get
  have g := gd_of_tder (Γ := insert Y ∅) b
  simp only [Bootstrapping.Sequent.val_insert, Bootstrapping.Sequent.val_empty,
    Bootstrapping.Semiformula.val_neg] at g
  exact g
theorem gd1 {X Y : Bootstrapping.Semiformula V SourceL 0} (h : T.internalize V ⊢ X 🡒 Y) :
    GDerivable T (insert (neg SourceL X.val) (insert Y.val (∅ : V))) := by
  have b : T.internalize V ⊢!ᵈᵉʳ insert (∼X ⋎ Y) ∅ :=
    TDerivation.cast (by simp [Bootstrapping.Semiformula.imp_def]) (TProof.toTDerivation h.get)
  have b1 : T.internalize V ⊢!ᵈᵉʳ (∼X) ⫽ Y ⫽ ∅ := TDerivation.orInv b
  have g := gd_of_tder (Γ := (∼X) ⫽ Y ⫽ ∅) b1
  simp only [Bootstrapping.Sequent.val_insert, Bootstrapping.Sequent.val_empty,
    Bootstrapping.Semiformula.val_neg] at g
  exact g
theorem gd2 {X₁ X₂ Y : Bootstrapping.Semiformula V SourceL 0}
    (h : T.internalize V ⊢ X₁ 🡒 X₂ 🡒 Y) :
    GDerivable T (insert (neg SourceL X₁.val) (insert (neg SourceL X₂.val)
      (insert Y.val (∅ : V)))) := by
  have b : T.internalize V ⊢!ᵈᵉʳ insert (∼X₁ ⋎ (∼X₂ ⋎ Y)) ∅ :=
    TDerivation.cast (by simp [Bootstrapping.Semiformula.imp_def]) (TProof.toTDerivation h.get)
  have b1 : T.internalize V ⊢!ᵈᵉʳ (∼X₁) ⫽ (∼X₂ ⋎ Y) ⫽ ∅ := TDerivation.orInv b
  have b2 : T.internalize V ⊢!ᵈᵉʳ (∼X₂ ⋎ Y) ⫽ (∼X₁) ⫽ ∅ := TDerivation.rotate₁ b1
  have b3 : T.internalize V ⊢!ᵈᵉʳ (∼X₂) ⫽ Y ⫽ (∼X₁) ⫽ ∅ := TDerivation.orInv b2
  have b4 : T.internalize V ⊢!ᵈᵉʳ (∼X₁) ⫽ (∼X₂) ⫽ Y ⫽ ∅ :=
    b3.wk (seq_subset_of fun φ hφ => by
      simp only [Bootstrapping.Sequent.mem_insert_iff, Bootstrapping.Sequent.not_mem_empty]
        at hφ ⊢
      tauto)
  have g := gd_of_tder (Γ := (∼X₁) ⫽ (∼X₂) ⫽ Y ⫽ ∅) b4
  simp only [Bootstrapping.Sequent.val_insert, Bootstrapping.Sequent.val_empty,
    Bootstrapping.Semiformula.val_neg] at g
  exact g
theorem gd3 {X₁ X₂ X₃ Y : Bootstrapping.Semiformula V SourceL 0}
    (h : T.internalize V ⊢ X₁ 🡒 X₂ 🡒 X₃ 🡒 Y) :
    GDerivable T (insert (neg SourceL X₁.val) (insert (neg SourceL X₂.val)
      (insert (neg SourceL X₃.val) (insert Y.val (∅ : V))))) := by
  have b : T.internalize V ⊢!ᵈᵉʳ insert (∼X₁ ⋎ (∼X₂ ⋎ (∼X₃ ⋎ Y))) ∅ :=
    TDerivation.cast (by simp [Bootstrapping.Semiformula.imp_def]) (TProof.toTDerivation h.get)
  have b1 : T.internalize V ⊢!ᵈᵉʳ (∼X₁) ⫽ (∼X₂ ⋎ (∼X₃ ⋎ Y)) ⫽ ∅ := TDerivation.orInv b
  have b2 : T.internalize V ⊢!ᵈᵉʳ (∼X₂ ⋎ (∼X₃ ⋎ Y)) ⫽ (∼X₁) ⫽ ∅ := TDerivation.rotate₁ b1
  have b3 : T.internalize V ⊢!ᵈᵉʳ (∼X₂) ⫽ (∼X₃ ⋎ Y) ⫽ (∼X₁) ⫽ ∅ := TDerivation.orInv b2
  have b4 : T.internalize V ⊢!ᵈᵉʳ (∼X₃ ⋎ Y) ⫽ (∼X₂) ⫽ (∼X₁) ⫽ ∅ := TDerivation.rotate₁ b3
  have b5 : T.internalize V ⊢!ᵈᵉʳ (∼X₃) ⫽ Y ⫽ (∼X₂) ⫽ (∼X₁) ⫽ ∅ := TDerivation.orInv b4
  have b6 : T.internalize V ⊢!ᵈᵉʳ (∼X₁) ⫽ (∼X₂) ⫽ (∼X₃) ⫽ Y ⫽ ∅ :=
    b5.wk (seq_subset_of fun φ hφ => by
      simp only [Bootstrapping.Sequent.mem_insert_iff, Bootstrapping.Sequent.not_mem_empty]
        at hφ ⊢
      tauto)
  have g := gd_of_tder (Γ := (∼X₁) ⫽ (∼X₂) ⫽ (∼X₃) ⫽ Y ⫽ ∅) b6
  simp only [Bootstrapping.Sequent.val_insert, Bootstrapping.Sequent.val_empty,
    Bootstrapping.Semiformula.val_neg] at g
  exact g

/-! ### Substitution into the typed atoms -/

@[simp] theorem tDom_subst {n m : ℕ} (t : Bootstrapping.Semiterm V SourceL n)
    (w : Bootstrapping.SemitermVec V SourceL n m) : (tDom t).subst w = tDom (t.subst w) := by
  unfold tDom
  rw [Bootstrapping.Semiformula.substs_substs]
  simp
@[simp] theorem tEq_subst {n m : ℕ} (t u : Bootstrapping.Semiterm V SourceL n)
    (w : Bootstrapping.SemitermVec V SourceL n m) :
    (tEq t u).subst w = tEq (t.subst w) (u.subst w) := by
  unfold tEq
  rw [Bootstrapping.Semiformula.substs_substs]
  simp
@[simp] theorem tIso_subst {n m : ℕ} (t u : Bootstrapping.Semiterm V SourceL n)
    (w : Bootstrapping.SemitermVec V SourceL n m) :
    (tIso t u).subst w = tIso (t.subst w) (u.subst w) := by
  unfold tIso
  rw [Bootstrapping.Semiformula.substs_substs]
  simp

/-! ### The fields -/

section fields
variable (S : SourceFacts (V := V) T)
include S

/-- Two members of the domain equal to the variable `c` are isomorphic: the instance of the
second fixed fact at `c`. -/
theorem pair_of_ei (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) (i : Fin 4) (c : V)
    (hA : A i = tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar c)) :
    T.internalize V ⊢ instS (sig A) (sPair i) := by
  have e : (tHyp sEI : Bootstrapping.Semiformula V SourceL 0) =
      ∀⁰ (∀⁰ (∀⁰ (tDom (Bootstrapping.Semiterm.bvar 1) 🡒 tDom (Bootstrapping.Semiterm.bvar 0) 🡒
        tEq (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 2) 🡒
        tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) 🡒
        tIso (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)))) := by
    simp [sEI, tHyp]
  have h0 := S.ei
  rw [e] at h0
  have h1 := TProof.specialize! h0 (Bootstrapping.Semiterm.fvar c)
  have e2 : instS (sig A) (sPair i) =
      (∀⁰ (∀⁰ (tDom (Bootstrapping.Semiterm.bvar 1) 🡒 tDom (Bootstrapping.Semiterm.bvar 0) 🡒
        tEq (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 2) 🡒
        tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) 🡒
        tIso (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)))).subst
          ![Bootstrapping.Semiterm.fvar c] := by
    simp [sPair, hA, Bootstrapping.SemitermVec.q]
  rw [e2]
  exact h1

theorem field_nRefl {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (tr (nameAll s s)) (∅ : V)) := by
  obtain ⟨R, hR⟩ := boxOf hs
  obtain ⟨A, a0, -, -, -⟩ := exA4 R ⊤ ⊤ ⊤
  have h := with_facts A S fRefl valid_refl
  simp only [fRefl, instS_sNameAll, instS_sBox, a0] at h
  have g := gd0 h
  rwa [tNameAll_tr hs hs hR hR] at g

theorem field_atomTransfer {s₁ s₁' s₂ s₂' : V} (h1 : IsSemiterm PA194PAeq.language 0 s₁)
    (h1' : IsSemiterm PA194PAeq.language 0 s₁') (h2 : IsSemiterm PA194PAeq.language 0 s₂)
    (h2' : IsSemiterm PA194PAeq.language 0 s₂') :
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (neg SourceL (tr (peq s₁ s₂))) (insert (tr (peq s₁' s₂')) (∅ : V))))) := by
  obtain ⟨R1, e1⟩ := boxOf h1
  obtain ⟨R1', e1'⟩ := boxOf h1'
  obtain ⟨R2, e2⟩ := boxOf h2
  obtain ⟨R2', e2'⟩ := boxOf h2'
  obtain ⟨A, a0, a1, a2, a3⟩ := exA4 R1 R1' R2 R2'
  have h := with_facts A S fAtom valid_atom
  simp only [fAtom, instS_imp, instS_sNameAll, instS_sEqVal, instS_sBox, a0, a1, a2, a3] at h
  have g := gd3 h
  rwa [tNameAll_tr h1 h1' e1 e1', tNameAll_tr h2 h2' e2 e2', tEqVal_tr h1 h2 e1 e2,
    tEqVal_tr h1' h2' e1' e2'] at g

theorem field_nameOfUniq {t : V} (c : V) (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (insert (neg SourceL (tr (uniq t)))
      (insert (neg SourceL (tr (peq (^&c) t))) (insert (tr (nameAll t (^&c))) (∅ : V)))) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
  obtain ⟨R0, e0⟩ := boxOf ht
  obtain ⟨R1, e1⟩ := boxOf hc
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fNameOfUniq valid_nameOfUniq
  simp only [fNameOfUniq, instS_imp, instS_sNameAll, instS_sEqVal, instS_sUniq, instS_sBox,
    a0, a1] at h
  have g := gd2 h
  rwa [tUniq_tr ht e0, tEqVal_tr hc ht e1 e0, tNameAll_tr ht hc e0 e1] at g

theorem field_nameOfEq {t : V} (c : V) (ht : IsSemiterm PA194PAeq.language 0 t) :
    GDerivable T (insert (neg SourceL (tr (peq (^&c) t)))
      (insert (tr (nameAll (^&c) t)) (∅ : V))) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&c : V) := by simp
  obtain ⟨R0, e0⟩ := boxOf ht
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar c)) ⊤ ⊤
  have e1 := boxVar c
  have h := with_facts A S fNameOfEq valid_nameOfEq
  have hp := pair_of_ei S A 1 c a1
  simp only [fNameOfEq, instS_imp] at h
  have h' := tmp h hp
  simp only [instS_sNameAll, instS_sEqVal, instS_sBox, a0, a1] at h'
  have g := gd1 h'
  rwa [tEqVal_tr hc ht e1 e0, tNameAll_tr hc ht e1 e0] at g

theorem field_nSucc {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    GDerivable T (insert (neg SourceL (tr (nameAll s s')))
      (insert (tr (nameAll (succT s) (succT s'))) (∅ : V))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨R1, e1⟩ := boxOf hs'
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fNSucc valid_nSucc
  simp only [fNSucc, instS_imp, instS_sNameAll, instS_sSuccV, instS_sBox, a0, a1] at h
  have g := gd1 h
  rwa [tNameAll_tr hs hs' e0 e1, tNameAll_tr (succT_valid hs) (succT_valid hs')
    (tSuccV_val hs e0) (tSuccV_val hs' e1)] at g

theorem field_nAdd {s₁ s₁' s₂ s₂' : V} (h1 : IsSemiterm PA194PAeq.language 0 s₁)
    (h1' : IsSemiterm PA194PAeq.language 0 s₁') (h2 : IsSemiterm PA194PAeq.language 0 s₂)
    (h2' : IsSemiterm PA194PAeq.language 0 s₂') :
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (addT s₁ s₂) (addT s₁' s₂'))) (∅ : V)))) := by
  obtain ⟨R1, e1⟩ := boxOf h1
  obtain ⟨R1', e1'⟩ := boxOf h1'
  obtain ⟨R2, e2⟩ := boxOf h2
  obtain ⟨R2', e2'⟩ := boxOf h2'
  obtain ⟨A, a0, a1, a2, a3⟩ := exA4 R1 R1' R2 R2'
  have h := with_facts A S fNAdd valid_nAdd
  simp only [fNAdd, instS_imp, instS_sNameAll, instS_sAddV, instS_sBox, a0, a1, a2, a3] at h
  have g := gd2 h
  rwa [tNameAll_tr h1 h1' e1 e1', tNameAll_tr h2 h2' e2 e2',
    tNameAll_tr (addT_valid h1 h2) (addT_valid h1' h2') (tAddV_val h1 h2 e1 e2)
      (tAddV_val h1' h2' e1' e2')] at g

theorem field_nMul {s₁ s₁' s₂ s₂' : V} (h1 : IsSemiterm PA194PAeq.language 0 s₁)
    (h1' : IsSemiterm PA194PAeq.language 0 s₁') (h2 : IsSemiterm PA194PAeq.language 0 s₂)
    (h2' : IsSemiterm PA194PAeq.language 0 s₂') :
    GDerivable T (insert (neg SourceL (tr (nameAll s₁ s₁')))
      (insert (neg SourceL (tr (nameAll s₂ s₂')))
        (insert (tr (nameAll (mulT s₁ s₂) (mulT s₁' s₂'))) (∅ : V)))) := by
  obtain ⟨R1, e1⟩ := boxOf h1
  obtain ⟨R1', e1'⟩ := boxOf h1'
  obtain ⟨R2, e2⟩ := boxOf h2
  obtain ⟨R2', e2'⟩ := boxOf h2'
  obtain ⟨A, a0, a1, a2, a3⟩ := exA4 R1 R1' R2 R2'
  have h := with_facts A S fNMul valid_nMul
  simp only [fNMul, instS_imp, instS_sNameAll, instS_sMulV, instS_sBox, a0, a1, a2, a3] at h
  have g := gd2 h
  rwa [tNameAll_tr h1 h1' e1 e1', tNameAll_tr h2 h2' e2 e2',
    tNameAll_tr (mulT_valid h1 h2) (mulT_valid h1' h2') (tMulV_val h1 h2 e1 e2)
      (tMulV_val h1' h2' e1' e2')] at g

theorem field_uVar (i : V) : GDerivable T (insert (tr (uniq (^&i))) (∅ : V)) := by
  have hc : IsSemiterm PA194PAeq.language 0 (^&i : V) := by simp
  obtain ⟨A, a0, -, -, -⟩ := exA4
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar i) :
      Bootstrapping.Semiformula V SourceL 1) ⊤ ⊤ ⊤
  have h := with_facts A S fUVar valid_uVar
  have hp := pair_of_ei S A 0 i a0
  simp only [fUVar, instS_imp] at h
  have h' := tmp h hp
  simp only [instS_sUniq, instS_sBox, a0] at h'
  have g := gd0 h'
  rwa [tUniq_tr hc (boxVar i)] at g

theorem field_uZero : GDerivable T (insert (tr (uniq (zeroT : V))) (∅ : V)) := by
  obtain ⟨A, -, -, -, -⟩ := exA4 (⊤ : Bootstrapping.Semiformula V SourceL 1) ⊤ ⊤ ⊤
  have h := with_facts A S fUZero valid_uZero
  simp only [fUZero, instS_sUniq, instS_sZeroV] at h
  have g := gd0 h
  rwa [tUniq_tr (zeroT_valid : IsSemiterm PA194PAeq.language 0 (zeroT : V)) tZeroV_val] at g

theorem field_uSucc {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (tr (uniq (succT s))) (∅ : V))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨A, a0, -, -, -⟩ := exA4 R0 ⊤ ⊤ ⊤
  have h := with_facts A S fUSucc valid_uSucc
  simp only [fUSucc, instS_imp, instS_sUniq, instS_sSuccV, instS_sBox, a0] at h
  have g := gd1 h
  rwa [tUniq_tr hs e0, tUniq_tr (succT_valid hs) (tSuccV_val hs e0)] at g

theorem field_uAdd {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (addT s s'))) (∅ : V)))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨R1, e1⟩ := boxOf hs'
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fUAdd valid_uAdd
  simp only [fUAdd, instS_imp, instS_sUniq, instS_sAddV, instS_sBox, a0, a1] at h
  have g := gd2 h
  rwa [tUniq_tr hs e0, tUniq_tr hs' e1,
    tUniq_tr (addT_valid hs hs') (tAddV_val hs hs' e0 e1)] at g

theorem field_uMul {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    GDerivable T (insert (neg SourceL (tr (uniq s))) (insert (neg SourceL (tr (uniq s')))
      (insert (tr (uniq (mulT s s'))) (∅ : V)))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨R1, e1⟩ := boxOf hs'
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fUMul valid_uMul
  simp only [fUMul, instS_imp, instS_sUniq, instS_sMulV, instS_sBox, a0, a1] at h
  have g := gd2 h
  rwa [tUniq_tr hs e0, tUniq_tr hs' e1,
    tUniq_tr (mulT_valid hs hs') (tMulV_val hs hs' e0 e1)] at g

theorem field_eZero : GDerivable T (insert (tr (exName (zeroT : V))) (∅ : V)) := by
  obtain ⟨A, -, -, -, -⟩ := exA4 (⊤ : Bootstrapping.Semiformula V SourceL 1) ⊤ ⊤ ⊤
  have h := with_facts A S fEZero valid_eZero
  simp only [fEZero, instS_sExName, instS_sZeroV] at h
  have g := gd0 h
  rwa [tExName_tr (zeroT_valid : IsSemiterm PA194PAeq.language 0 (zeroT : V)) tZeroV_val] at g

theorem field_eSucc {s : V} (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (neg SourceL (tr (exName s)))
      (insert (tr (exName (succT s))) (∅ : V))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨A, a0, -, -, -⟩ := exA4 R0 ⊤ ⊤ ⊤
  have h := with_facts A S fESucc valid_eSucc
  simp only [fESucc, instS_imp, instS_sExName, instS_sSuccV, instS_sBox, a0] at h
  have g := gd1 h
  rwa [tExName_tr hs e0, tExName_tr (succT_valid hs) (tSuccV_val hs e0)] at g

theorem field_eAdd {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (addT s s'))) (∅ : V)))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨R1, e1⟩ := boxOf hs'
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fEAdd valid_eAdd
  simp only [fEAdd, instS_imp, instS_sExName, instS_sAddV, instS_sBox, a0, a1] at h
  have g := gd2 h
  rwa [tExName_tr hs e0, tExName_tr hs' e1,
    tExName_tr (addT_valid hs hs') (tAddV_val hs hs' e0 e1)] at g

theorem field_eMul {s s' : V} (hs : IsSemiterm PA194PAeq.language 0 s)
    (hs' : IsSemiterm PA194PAeq.language 0 s') :
    GDerivable T (insert (neg SourceL (tr (exName s))) (insert (neg SourceL (tr (exName s')))
      (insert (tr (exName (mulT s s'))) (∅ : V)))) := by
  obtain ⟨R0, e0⟩ := boxOf hs
  obtain ⟨R1, e1⟩ := boxOf hs'
  obtain ⟨A, a0, a1, -, -⟩ := exA4 R0 R1 ⊤ ⊤
  have h := with_facts A S fEMul valid_eMul
  simp only [fEMul, instS_imp, instS_sExName, instS_sMulV, instS_sBox, a0, a1] at h
  have g := gd2 h
  rwa [tExName_tr hs e0, tExName_tr hs' e1,
    tExName_tr (mulT_valid hs hs') (tMulV_val hs hs' e0 e1)] at g

/-- All naming facts, from the twelve fixed facts about the source theory and the existence
of a name for every variable. -/
theorem nameFacts_of_sourceFacts
    (heVar : ∀ i : V, GDerivable T (insert (tr (exName (^&i))) (∅ : V))) :
    NameFacts (V := V) T where
  nRefl := fun _ hs => field_nRefl S hs
  atomTransfer := fun _ _ _ _ h1 h1' h2 h2' => field_atomTransfer S h1 h1' h2 h2'
  nameOfUniq := fun _ c ht => field_nameOfUniq S c ht
  nameOfEq := fun _ c ht => field_nameOfEq S c ht
  nSucc := fun _ _ hs hs' => field_nSucc S hs hs'
  nAdd := fun _ _ _ _ h1 h1' h2 h2' => field_nAdd S h1 h1' h2 h2'
  nMul := fun _ _ _ _ h1 h1' h2 h2' => field_nMul S h1 h1' h2 h2'
  uVar := fun i => field_uVar S i
  uZero := field_uZero S
  uSucc := fun _ hs => field_uSucc S hs
  uAdd := fun _ _ hs hs' => field_uAdd S hs hs'
  uMul := fun _ _ hs hs' => field_uMul S hs hs'
  eVar := heVar
  eZero := field_eZero S
  eSucc := fun _ hs => field_eSucc S hs
  eAdd := fun _ _ hs hs' => field_eAdd S hs hs'
  eMul := fun _ _ hs hs' => field_eMul S hs hs'

/-- The three term facts of `PA194Leibniz` under the same hypotheses. -/
theorem termFacts_of_sourceFacts
    (heVar : ∀ i : V, GDerivable T (insert (tr (exName (^&i))) (∅ : V))) :
    TermFacts (V := V) T :=
  termFacts_of_nameFacts (nameFacts_of_sourceFacts S heVar)

end fields

#print axioms termFacts_of_sourceFacts
#print axioms valBody_split
#print axioms with_facts
#print axioms gd3
#print axioms pair_of_ei
#print axioms field_atomTransfer
#print axioms field_nameOfEq
#print axioms field_nAdd
#print axioms field_uVar
#print axioms nameFacts_of_sourceFacts
end generic
end PA194GuardedCompiler

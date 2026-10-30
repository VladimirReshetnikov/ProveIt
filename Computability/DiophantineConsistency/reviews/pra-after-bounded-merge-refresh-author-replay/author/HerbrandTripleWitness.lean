import DiophantineConsistency.HerbrandTripleParameterized
import DiophantineConsistency.PRAHerbrandTripleSelection
/-! Compile extracted triple terms and select coordinated PR witnesses. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandTripleWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAUniversalEquivalence
  HerbrandExistentialSequents HerbrandUniversalPreparation HerbrandTripleExtraction
  HerbrandTripleParameterized HerbrandParameterizedWitness PRAFiniteTripleChoice PRAHerbrandTripleSelection

def tripleCode (n : ℕ) (t u v : SyntacticTerm language) : Triple n :=
  ⟨parameterCode n v, parameterCode n u, parameterCode n t⟩

def tripleCodes (n : ℕ) (ts : List (SyntacticTerm language)) : List (Triple n) :=
  (triples ts).map (fun p => tripleCode n p.1 p.2.1 p.2.2)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

theorem modelParameterTripleInstance {n : ℕ} (φ : Semisentence language (n+3))
    (t u v : SyntacticTerm language) (e : Fin n → M)
    (h : (tripleInstance (parameterTripleMatrix φ) t u v).Eval ![] (parameterEnv n e)) :
    (matrixAt φ (tripleCode n t u v)).Eval e Empty.elim := by
  letI : M↓[language] ⊧* PRA := modelCandidatePRA
  unfold tripleInstance afterSecond afterFirst parameterTripleMatrix at h
  simp only [Semiformula.eval_rew] at h
  rw [matrixAt, Semiformula.eval_substs]
  simp only [tripleCode]
  have hv : (Semiterm.val e Empty.elim ∘ Fin.cases (applyCode (parameterCode n v) (vars n))
      (Fin.cases (applyCode (parameterCode n u) (vars n))
        (Fin.cases (applyCode (parameterCode n t) (vars n)) (vars n)))) =
      Fin.cases (Semiterm.val ![] (parameterEnv n e) v)
        (Fin.cases (Semiterm.val ![] (parameterEnv n e) u)
          (Fin.cases (Semiterm.val ![] (parameterEnv n e) t) e)) := by
    have hv : (Semiterm.val e Empty.elim ∘ vars n) = e := by funext i; rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (parameterCode n v) (Semiterm.val e Empty.elim ∘ vars n) = _
      rw [hv, modelParameterCode]; rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Structure.func (L := language) (parameterCode n u) (Semiterm.val e Empty.elim ∘ vars n) = _
        rw [hv, modelParameterCode]; rfl
      · refine Fin.cases ?_ (fun _ => rfl) k
        change Structure.func (L := language) (parameterCode n t) (Semiterm.val e Empty.elim ∘ vars n) = _
        rw [hv, modelParameterCode]; rfl
  rw [hv]
  simp [Function.comp_def, Rew.qpow_succ] at h
  have hb : (fun x =>
        Semiterm.val
          (fun x => Semiterm.val
            (fun x => Semiterm.val
              (fun x => Semiterm.val ![] (parameterEnv n e) v)
              (parameterEnv n e) ((Rew.subst ![u]).q #x))
            (parameterEnv n e) ((Rew.subst ![t]).q.q #x))
          (parameterEnv n e) ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q.q #x)) =
      Fin.cases (Semiterm.val ![] (parameterEnv n e) v)
        (Fin.cases (Semiterm.val ![] (parameterEnv n e) u)
          (Fin.cases (Semiterm.val ![] (parameterEnv n e) t) e)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Semiterm.val _ _ ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q.q #((0 : Fin (n+2)).succ)) = _
        simp only [Rew.q_bvar_succ, Rew.q_bvar_zero, Rew.bShift_bvar, Semiterm.val_bvar, Rew.subst_bvar]
        have heq : (fun _ : Fin 1 => Semiterm.val ![] (parameterEnv n e) v) =
            (Semiterm.val ![] (parameterEnv n e) v :> (Fin.elim0 : Fin 0 → M)) := by
          funext x; exact Fin.cases rfl (fun i => Fin.elim0 i) x
        rw [heq, Semiterm.val_bShift]
        rfl
      · refine Fin.cases ?_ (fun l => ?_) k
        · change Semiterm.val _ _ ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))).q.q.q #((0 : Fin (n+1)).succ.succ)) = _
          simp only [Rew.q_bvar_succ, Rew.q_bvar_zero, Rew.bShift_bvar, Semiterm.val_bvar, Rew.subst_bvar]
          have heq : (fun x : Fin 2 => Semiterm.val
              (fun x => Semiterm.val ![] (parameterEnv n e) v)
              (parameterEnv n e) ((Rew.subst ![u]).q #x)) =
              (Semiterm.val ![] (parameterEnv n e) v :>
                Semiterm.val ![] (parameterEnv n e) u :> Fin.elim0) := by
            funext x
            refine Fin.cases rfl (fun y => ?_) x
            refine Fin.cases ?_ (fun z => Fin.elim0 z) y
            change Semiterm.val _ _ ((Rew.subst ![u]).q #((0 : Fin 1).succ)) = _
            simp only [Rew.q_bvar_succ, Rew.subst_bvar]
            have hv1 : (fun _ : Fin 1 => Semiterm.val ![] (parameterEnv n e) v) =
                (Semiterm.val ![] (parameterEnv n e) v :> (Fin.elim0 : Fin 0 → M)) := by
              funext x; exact Fin.cases rfl (fun i => Fin.elim0 i) x
            rw [hv1, Semiterm.val_bShift]
            rfl
          rw [heq, Semiterm.val_bShift, Semiterm.val_bShift]
          rfl
        · simp [Rew.q_bvar_succ, parameterEnv]
  rw [hb] at h
  have he : (fun x =>
      Semiterm.val
        (fun x => Semiterm.val
          (fun x => Semiterm.val (fun x => Semiterm.val ![] (parameterEnv n e) v) (parameterEnv n e) ((Rew.subst ![u]).q #x))
          (parameterEnv n e) ((Rew.subst ![t]).q.q #x))
        (parameterEnv n e) (Rew.bShift (Rew.bShift (Rew.bShift ((Rew.embSubsts (fun i : Fin n => (&i.val : SyntacticTerm language))) &x))))) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [he] at h
  exact h
omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
theorem modelListMember {n : ℕ} (φ : Semisentence language (n+3)) (fallback : Triple n)
    (ts : List (Triple n)) (t : Triple n) (ht : t ∈ ts) (e : Fin n → M)
    (h : (matrixAt φ t).Eval e Empty.elim) : (matrixList φ fallback ts).Eval e Empty.elim := by
  induction ts with
  | nil => simp at ht
  | cons head tail ih =>
    simp only [List.mem_cons] at ht
    change (matrixAt φ head).Eval e Empty.elim ∨ (matrixList φ fallback tail).Eval e Empty.elim
    rcases ht with rfl | ht
    · exact Or.inl h
    · exact Or.inr (ih ht)

theorem modelExtractedTripleList {n : ℕ} (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (∃⁰ ∃⁰ parameterTripleMatrix φ) axioms) :
    M↓[language] ⊧ (∀⁰* matrixList φ ⟨.zero n,.zero n,.zero n⟩
      (tripleCodes n (existentialTerms p.derivation))) := by
  have hopen : (parameterTripleMatrix φ).Open := by
    change (parameterTripleMatrix φ).qr = 0
    unfold parameterTripleMatrix
    rw [PRAFormulaParameters.qr_rew]
    exact hOpen
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  obtain ⟨t,ht,u,hu,v,hv,hm⟩ := modelTripleWitness (M := M) (parameterTripleMatrix φ) hopen
    axioms hAxioms p (parameterEnv n e)
  apply modelListMember φ ⟨.zero n,.zero n,.zero n⟩ _ (tripleCode n t u v)
  · simp [tripleCodes, triples]
    exact ⟨t, u, v, ⟨ht, hu, hv⟩, rfl⟩
  · exact modelParameterTripleInstance φ t u v e hm
end models

/-- Triple-existential theorems have three coordinated PR witnesses. -/
theorem PRA_exists_tripleWitness {n : ℕ} (φ : Semisentence language (n+3)) (hOpen : φ.Open)
    (h : PRA ⊢ (∀⁰* ∃⁰ ∃⁰ ∃⁰ φ)) :
    ∃ t : Triple n, Primrec (eval t.first) ∧ Primrec (eval t.second) ∧ Primrec (eval t.third) ∧
      PRA ⊢ (∀⁰* matrixAt φ t) := by
  obtain ⟨p⟩ := universal_proves_candidate h
  let prepared := prepareAllTriple φ hOpen p
  have hDisj : UniversalAxiom ⊢ (∀⁰* matrixList φ ⟨.zero n,.zero n,.zero n⟩
      (tripleCodes n (existentialTerms prepared.derivation))) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelExtractedTripleList φ hOpen p.axioms p.axioms_mem prepared
  exact PRA_exists_triple_of_openDisjunction φ hOpen _ _ (candidate_proves_universal hDisj)
end DiophantineConsistency.HerbrandTripleWitness

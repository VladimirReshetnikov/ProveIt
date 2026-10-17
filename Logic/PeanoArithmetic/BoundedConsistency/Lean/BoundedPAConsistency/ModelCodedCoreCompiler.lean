import BoundedPAConsistency.ModelCodedPredicateHygiene

/-!
# Compiling standard finite proof templates at internal matrices

The source is a standard finite first-order proof. Its distinguished predicate
is specialized at an arbitrary typed internal arithmetic matrix S, including
nonstandard codes and free parameters. The shift-free logical core is compiled
by shifting S at universal premises. A finite list of supplied target proofs
discharges the translated source axioms at the root.

The resulting carrier satisfies Foundation's represented proof predicate.
This module does not represent the compiler as an arithmetic function, translate
arbitrary internally coded source proofs, or prove a PA consistency comparison.
-/
namespace LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler

open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateHygiene

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {arity : ℕ}

noncomputable def mapSeq (S : Bootstrapping.Semiformula V ℒₒᵣ arity) :
    List (Proposition (templateLanguage arity)) → Bootstrapping.Sequent V ℒₒᵣ
  | [] => ∅
  | p :: Γ => insert (translateFormula S p) (mapSeq S Γ)

lemma mem_mapSeq (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (Γ : List (Proposition (templateLanguage arity))) (q : Bootstrapping.Formula V ℒₒᵣ) :
    q ∈ mapSeq S Γ ↔ ∃ p ∈ Γ, q = translateFormula S p := by
  induction Γ with
  | nil => simp [mapSeq]
  | cons p Γ ih => simp [mapSeq, ih]

lemma mapSeq_mono (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    {Γ Δ : List (Proposition (templateLanguage arity))} (h : Γ ⊆ Δ) :
    mapSeq S Γ ⊆ mapSeq S Δ := by
  intro q hq
  let q' : Bootstrapping.Formula V ℒₒᵣ := ⟨q, (mapSeq S Γ).val_formulaSet q hq⟩
  have hq' : q' ∈ mapSeq S Γ := hq
  rcases (mem_mapSeq S Γ q').mp hq' with ⟨p, hp, he⟩
  have ht : q' ∈ mapSeq S Δ := (mem_mapSeq S Δ q').mpr ⟨p, h hp, he⟩
  exact ht

lemma mapSeq_append (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (Γ Δ : List (Proposition (templateLanguage arity))) :
    mapSeq S (Γ ++ Δ) = mapSeq S Γ ∪ mapSeq S Δ := by
  ext q
  simp only [mem_mapSeq, List.mem_append, Bootstrapping.Sequent.mem_union_iff]
  aesop

lemma mapSeq_shift (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (Γ : List (Proposition (templateLanguage arity))) :
    mapSeq S.shift (Γ.map Rewriting.shift) = (mapSeq S Γ).shift := by
  induction Γ with
  | nil => simp [mapSeq]
  | cons p Γ ih => simp [mapSeq, ih, translateFormula_shift_heterogeneous]

noncomputable def compileCore (T : InternalTheory V ℒₒᵣ) :
    {Γ : List (Proposition (templateLanguage arity))} →
    (d : LO.FirstOrder.Derivation Γ) →
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) → T ⊢!ᵈᵉʳ mapSeq S Γ
  | _, .identity R v, S => by
      have hn : translateFormula S (.nrel R v) = ∼translateFormula S (.rel R v) := by
        simpa using translateFormula_neg S (.rel R v)
      simp only [mapSeq, hn]
      exact TDerivation.em (translateFormula S (.rel R v)) (by simp) (by simp)
  | _, .cut (Γ := Γ) (Δ := Δ) (φ := p) dp dn, S => by
      have dn' : T ⊢!ᵈᵉʳ insert (∼translateFormula S p) (mapSeq S Δ) := by
        simpa only [mapSeq, translateFormula_neg] using compileCore T dn S
      simpa only [mapSeq, mapSeq_append] using
        TDerivation.cut' (compileCore T dp S) dn'
  | _, .contraction d h, S =>
      TDerivation.wk (compileCore T d S) (mapSeq_mono S h)
  | _, .verum, S => TDerivation.verum (by simp [mapSeq, translateFormula])
  | _, .or d, S => by
      simpa only [mapSeq, translateFormula] using TDerivation.or (compileCore T d S)
  | _, .and dp dq, S => by
      simpa only [mapSeq, translateFormula] using
        TDerivation.and (compileCore T dp S) (compileCore T dq S)
  | _, .all (Γ := Γ) (φ := p) d, S => by
      have dp : T ⊢!ᵈᵉʳ insert (translateFormula S p).free (mapSeq S Γ).shift := by
        simpa only [Rewriting.shifts, mapSeq, translateFormula_free_heterogeneous,
          mapSeq_shift] using compileCore T d S.shift
      simpa only [mapSeq, translateFormula] using TDerivation.all dp
  | _, .exs (φ := p) (t := t) d, S => by
      have hs : translateFormula S (p/[t]) =
          (translateFormula S p).subst ![translateTerm (V := V) t] := by
        simpa [Matrix.constant_eq_singleton] using translateFormula_subst S ![t] p
      have dp := compileCore T d S
      simp only [mapSeq, hs] at dp
      simpa only [mapSeq, translateFormula] using TDerivation.exs (translateTerm t) dp

/-- Discharge a standard finite list of formulas by supplied target proofs. -/
noncomputable def discharge (T : InternalTheory V ℒₒᵣ)
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (Γ : List (Proposition (templateLanguage arity))) :
    (A : List (Proposition (templateLanguage arity))) →
    (∀ p ∈ A, T ⊢! translateFormula S p) →
    T ⊢!ᵈᵉʳ mapSeq S (Γ ++ A.map (∼·)) → T ⊢!ᵈᵉʳ mapSeq S Γ
  | [], _, d => by simpa using d
  | a :: A, hA, d => by
      have dn : T ⊢!ᵈᵉʳ insert (∼translateFormula S a)
          (mapSeq S (Γ ++ A.map (∼·))) := by
        apply d.ofEq
        ext q
        simp only [mapSeq_append, mapSeq, List.map_cons, translateFormula_neg,
          Bootstrapping.Sequent.mem_union_iff, Bootstrapping.Sequent.mem_insert_iff]
        tauto
      have da : T ⊢!ᵈᵉʳ insert (translateFormula S a)
          (mapSeq S (Γ ++ A.map (∼·))) := by
        apply (hA a (by simp)).wk
        intro q hq
        simp only [Bootstrapping.Sequent.val_insert, Bootstrapping.Sequent.val_empty,
          mem_bitInsert_iff, not_mem_empty, or_false] at hq
        simp [hq]
      exact discharge T S Γ A (fun p hp => hA p (by simp [hp])) (TDerivation.cut da dn)

noncomputable def compileTemplate (T : InternalTheory V ℒₒᵣ)
    {T₁ : Theory (templateLanguage arity)} {σ : Sentence (templateLanguage arity)}
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) (d : T₁ ⊢! σ)
    (hA : ∀ ψ ∈ d.axioms, T ⊢! translateFormula S (Rewriting.emb ψ)) :
    T ⊢! translateFormula S (Rewriting.emb σ) := by
  let A := Sequent.embed d.axioms
  have hA' : ∀ p ∈ A, T ⊢! translateFormula S p := by
    intro p hp
    have hex := List.mem_map.mp hp
    let ψ := Classical.choose hex
    have hψ := (Classical.choose_spec hex).1
    have he := (Classical.choose_spec hex).2
    rw [← he]
    exact hA ψ hψ
  have dc := compileCore T d.derivation S
  have d' : T ⊢!ᵈᵉʳ mapSeq S ([Rewriting.emb σ] ++ A.map (∼·)) := by
    simpa [A, Sequent.embed, List.tilde_def, Function.comp_def] using dc
  change T ⊢!ᵈᵉʳ insert (translateFormula S (Rewriting.emb σ)) ∅
  simpa only [mapSeq] using discharge T S [Rewriting.emb σ] A hA' d'

lemma compileTemplate_isProof (T : InternalTheory V ℒₒᵣ)
    {T₁ : Theory (templateLanguage arity)} {σ : Sentence (templateLanguage arity)}
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) (d : T₁ ⊢! σ)
    (hA : ∀ ψ ∈ d.axioms, T ⊢! translateFormula S (Rewriting.emb ψ)) :
    Proof T.theory (compileTemplate T S d hA).val
      (translateFormula S (Rewriting.emb σ)).val := by
  simpa [Proof] using (compileTemplate T S d hA).derivationOf

end LeanProofs.BoundedPAConsistency.ModelCodedCoreCompiler

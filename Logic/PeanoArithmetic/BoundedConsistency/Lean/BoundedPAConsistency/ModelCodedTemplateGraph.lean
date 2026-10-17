import BoundedPAConsistency.ModelCodedPeanoCore

/-!
Represented graphs for fixed standard predicate templates.

The graph family below is chosen by recursion over standard source syntax before
introducing any arithmetic model. Its argument is the raw code of the inserted
matrix. The typed matrix may be nonstandard and may have free parameters.

`templatePeano` is ordinary PA lifted to the placeholder language; it does not
add induction for formulas containing the new predicate.

The final sentence concerns one fixed standard proof template. This is not a
graph or translator for arbitrary internally coded source formulas/proofs.
-/
namespace LeanProofs.BoundedPAConsistency.ModelCodedTemplateGraph

open LO FirstOrder
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedPeanoCore

variable {arity n k : Nat}

/-- Erase the empty extra function alphabet, by ordinary standard recursion. -/
def eraseTerm : SyntacticSemiterm (templateLanguage arity) n →
    SyntacticSemiterm ℒₒᵣ n
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .func (Sum.inl f) v => .func f (fun i => eraseTerm (v i))
  | .func (Sum.inr f) _ => nomatch f

/-- A standard natural, independent of an arithmetic model. -/
noncomputable def argumentVectorCode
    (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) : Nat :=
  Matrix.vecToNat (fun i => Encodable.encode (eraseTerm (v i)))

noncomputable def atomCode (R : (ℒₒᵣ).Rel k)
    (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) : Nat :=
  Encodable.encode (.rel R (fun i => eraseTerm (v i)) : ArithmeticSemiproposition n)

noncomputable def negativeAtomCode (R : (ℒₒᵣ).Rel k)
    (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) : Nat :=
  Encodable.encode (.nrel R (fun i => eraseTerm (v i)) : ArithmeticSemiproposition n)

/-- One fixed parameter-free graph for each standard source formula p. -/
noncomputable def graph : {n : Nat} →
    Semiproposition (templateLanguage arity) n → 𝚺₁.Semisentence 2
  | _, .rel (Sum.inl R) v => .mkSigma “y s. y = ↑(atomCode R v)”
  | _, .rel (Sum.inr .predicate) v =>
      .mkSigma “y s. !(substsGraph ℒₒᵣ) y ↑(argumentVectorCode v) s”
  | _, .nrel (Sum.inl R) v => .mkSigma “y s. y = ↑(negativeAtomCode R v)”
  | _, .nrel (Sum.inr .predicate) v =>
      .mkSigma “y s. ∃ u, !(substsGraph ℒₒᵣ) u ↑(argumentVectorCode v) s ∧
        !(negGraph ℒₒᵣ) y u”
  | _, ⊤ => .mkSigma “y s. !qqVerumDef y”
  | _, ⊥ => .mkSigma “y s. !qqFalsumDef y”
  | _, p ⋏ q => .mkSigma “y s. ∃ u, !(graph p) u s ∧
      ∃ v, !(graph q) v s ∧ !qqAndDef y u v”
  | _, p ⋎ q => .mkSigma “y s. ∃ u, !(graph p) u s ∧
      ∃ v, !(graph q) v s ∧ !qqOrDef y u v”
  | _, ∀⁰ p => .mkSigma “y s. ∃ u, !(graph p) u s ∧ !qqAllDef y u”
  | _, ∃⁰ p => .mkSigma “y s. ∃ u, !(graph p) u s ∧ !qqExsDef y u”

noncomputable def deltaGraph (p : Semiproposition (templateLanguage arity) n) :
    𝚫₁.Semisentence 2 := (graph p).graphDelta

/-- The source formula is fixed; s is an ordinary quantified arithmetic input. -/
noncomputable def provabilitySentence (p : Proposition (templateLanguage arity)) :
    ArithmeticSentence :=
  “∀ s, !(isSemiformula ℒₒᵣ).sigma ↑arity s →
    ∃ y, !(graph p) y s ∧ !(provable Peano) y”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Standard term translation is quotation after erasing the empty alphabet. -/
lemma translateTerm_eq_quote (t : SyntacticSemiterm (templateLanguage arity) n) :
    translateTerm (V := V) t = (⌜eraseTerm t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n) := by
  induction t with
  | bvar i => rfl
  | fvar i => rfl
  | @func k f v ih =>
      rcases f with f | f
      · simp [eraseTerm, translateTerm, ih]
      · exact PEmpty.elim f

/-- Exact vector-code cast, valid in every IΣ1 model, not just Nat. -/
lemma argumentVectorCode_cast
    (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) :
    (argumentVectorCode v : V) = SemitermVec.val (fun i => translateTerm (V := V) (v i)) := by
  simp only [translateTerm_eq_quote, argumentVectorCode]
  exact (LO.FirstOrder.Semiterm.quote_eq_encode' (fun i => eraseTerm (v i))).symm

lemma atomCode_cast (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (R : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) :
    (atomCode R v : V) = (translateFormula S (.rel (Sum.inl R) v)).val := by
  let a : ArithmeticSemiproposition n := .rel R (fun i => eraseTerm (v i))
  calc
    (atomCode R v : V) = (⌜a⌝ : V) := by
      exact (LO.FirstOrder.Semiformula.quote_eq_encode a).symm
    _ = (⌜a⌝ : Bootstrapping.Semiformula V ℒₒᵣ n).val :=
      LO.FirstOrder.Semiformula.quote_def a
    _ = (translateFormula S (.rel (Sum.inl R) v)).val := by
      simp [a, translateFormula, translateTerm_eq_quote]

lemma negativeAtomCode_cast (S : Bootstrapping.Semiformula V ℒₒᵣ arity)
    (R : (ℒₒᵣ).Rel k) (v : Fin k → SyntacticSemiterm (templateLanguage arity) n) :
    (negativeAtomCode R v : V) = (translateFormula S (.nrel (Sum.inl R) v)).val := by
  let a : ArithmeticSemiproposition n := .nrel R (fun i => eraseTerm (v i))
  calc
    (negativeAtomCode R v : V) = (⌜a⌝ : V) := by
      exact (LO.FirstOrder.Semiformula.quote_eq_encode a).symm
    _ = (⌜a⌝ : Bootstrapping.Semiformula V ℒₒᵣ n).val :=
      LO.FirstOrder.Semiformula.quote_def a
    _ = (translateFormula S (.nrel (Sum.inl R) v)).val := by
      simp [a, translateFormula, translateTerm_eq_quote]

/-- Total raw extension; invalid s still receives a value. -/
noncomputable def value : {n : Nat} →
    Semiproposition (templateLanguage arity) n → V → V
  | _, .rel (Sum.inl R) v, _ => atomCode R v
  | _, .rel (Sum.inr .predicate) v, s => subst ℒₒᵣ (argumentVectorCode v : V) s
  | _, .nrel (Sum.inl R) v, _ => negativeAtomCode R v
  | _, .nrel (Sum.inr .predicate) v, s => neg ℒₒᵣ (subst ℒₒᵣ (argumentVectorCode v : V) s)
  | _, ⊤, _ => qqVerum
  | _, ⊥, _ => qqFalsum
  | _, p ⋏ q, s => qqAnd (value p s) (value q s)
  | _, p ⋎ q, s => qqOr (value p s) (value q s)
  | _, ∀⁰ p, s => qqAll (value p s)
  | _, ∃⁰ p, s => qqExs (value p s)

lemma graph_eval (p : Semiproposition (templateLanguage arity) n) (y s : V) :
    (graph p).val.Evalb ![y, s] ↔ y = value p s := by
  induction p using FirstOrder.Semiformula.rec' generalizing y with
  | hrel R v =>
      rcases R with R | R
      · simp [graph, value, numeral_eq_natCast]
      · cases R; simp [graph, value, numeral_eq_natCast]
  | hnrel R v =>
      rcases R with R | R
      · simp [graph, value, numeral_eq_natCast]
      · cases R; simp [graph, value, numeral_eq_natCast]
  | hverum => simp [graph, value]
  | hfalsum => simp [graph, value]
  | hand p q hp hq => simp [graph, value, hp, hq]
  | hor p q hp hq => simp [graph, value, hp, hq]
  | hall p hp => simp [graph, value, hp]
  | hexs p hp => simp [graph, value, hp]

instance value_defined (p : Semiproposition (templateLanguage arity) n) :
    𝚺₁-Function₁[V] value p via graph p := .mk fun e => by
  simpa [← Matrix.fun_eq_vec_two] using graph_eval p (e 0) (e 1)

instance value_defined_delta (p : Semiproposition (templateLanguage arity) n) :
    𝚫₁-Function₁[V] value p via deltaGraph p := value_defined p |>.graph_delta

/-- Unique output at every raw matrix code, including invalid inputs. -/
theorem value_total (p : Semiproposition (templateLanguage arity) n) (s : V) :
    ∃! y, (graph p).val.Evalb ![y, s] := by
  simp

lemma value_eq_typed (p : Semiproposition (templateLanguage arity) n)
    (S : Bootstrapping.Semiformula V ℒₒᵣ arity) :
    value p S.val = (translateFormula S p).val := by
  induction p using FirstOrder.Semiformula.rec' with
  | hrel R v =>
      rcases R with R | R
      · exact atomCode_cast S R v
      · cases R; simp [value, translateFormula, argumentVectorCode_cast]
  | hnrel R v =>
      rcases R with R | R
      · exact negativeAtomCode_cast S R v
      · cases R; simp [value, translateFormula, argumentVectorCode_cast]
  | hverum => rfl
  | hfalsum => rfl
  | hand p q hp hq => simp [value, translateFormula, hp, hq]
  | hor p q hp hq => simp [value, translateFormula, hp, hq]
  | hall p hp => simp [value, translateFormula, hp]
  | hexs p hp => simp [value, translateFormula, hp]

lemma provabilitySentence_eval (p : Proposition (templateLanguage arity)) :
    (provabilitySentence p).Evalb (M := V) ![] ↔
      ∀ s : V, IsSemiformula ℒₒᵣ (arity : V) s → Provable Peano (value p s) := by
  simp [provabilitySentence, numeral_eq_natCast]

lemma fixed_template_sentence_true {σ : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! σ) :
    (provabilitySentence (Rewriting.emb σ)).Evalb (M := V) ![] := by
  apply (provabilitySentence_eval _).mpr
  intro s hs
  let S : Bootstrapping.Semiformula V ℒₒᵣ arity := ⟨s, hs⟩
  rw [value_eq_typed _ S]
  exact ⟨(compilePeanoTemplateOpen S d).val, compilePeanoTemplateOpen_isPAProof S d⟩

/-- One fixed arithmetic sentence per fixed standard source proof template. -/
theorem isigma1_proves_fixed_template {σ : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! σ) :
    𝗜𝚺₁ ⊢ provabilitySentence (Rewriting.emb σ) := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using fixed_template_sentence_true (V := M) d

theorem peano_proves_fixed_template {σ : Sentence (templateLanguage arity)}
    (d : templatePeano arity ⊢! σ) :
    Peano ⊢ provabilitySentence (Rewriting.emb σ) :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) (isigma1_proves_fixed_template d)

end LeanProofs.BoundedPAConsistency.ModelCodedTemplateGraph

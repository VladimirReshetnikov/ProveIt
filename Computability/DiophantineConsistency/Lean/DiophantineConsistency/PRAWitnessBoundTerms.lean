import DiophantineConsistency.PRAWitnessCodeGrowth
/-! # Nested exponential bound terms

Some witnesses are bounded only by towers of `tau X D = 2^((X + 4) · 2^D)`
(`PRAWitnessCodeGrowth`), for instance the negation of a substitution. A
`BoundTerm n` is built from `ℒₒᵣ` polynomials in `n` variables by addition,
multiplication and `exp2 A B = 2^(A · 2^B)`. Each has

* `term`, a candidate-PRA term (through `PRAHistoryExpCode.expCode`);
* `graph`, an `ℒₒᵣ` graph, `Σ₁` with exponentials;
* `vval`, its value in models of `𝗜𝚺₁`, which `graph` defines there
  (`eval_graph`);
* in candidate-PRA models `graph` defines `term` (`eval_graph_model`), which
  gives domination and monotonicity, so `wb_exs_bt` is a witness-bound rule
  whose side condition is an `𝗜𝚺₁` inequality. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessBoundTerms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessTransfer
  PRAWitnessExpBounds

/-- Bound terms: polynomials closed under `+`, `*` and `2^(A · 2^B)`. -/
inductive BoundTerm (n : ℕ) where
  | poly (P : ArithmeticSemiterm Empty n)
  | add (A B : BoundTerm n)
  | mul (A B : BoundTerm n)
  | exp2 (A B : BoundTerm n)

namespace BoundTerm
variable {n : ℕ}

/-- The candidate-PRA term. -/
noncomputable def term : BoundTerm n → TermN n
  | poly P => Semiterm.lMap embedding P
  | add A B => .func addCode ![A.term, B.term]
  | mul A B => .func mulCode ![A.term, B.term]
  | exp2 A B => .func PRAHistoryExpCode.expCode
      ![.func mulCode ![A.term, .func PRAHistoryExpCode.expCode ![B.term]]]

/-- The `ℒₒᵣ` graph, context `t :> e`. -/
noncomputable def graph : BoundTerm n → ArithmeticSemisentence (n + 1)
  | poly P => “t. t = !!(Rew.bShift P)”
  | add A B => “t. ∃ a b, !(graph A) a ⋯ ∧ !(graph B) b ⋯ ∧ t = a + b”
  | mul A B => “t. ∃ a b, !(graph A) a ⋯ ∧ !(graph B) b ⋯ ∧ t = a * b”
  | exp2 A B => “t. ∃ a b c, !(graph A) a ⋯ ∧ !(graph B) b ⋯ ∧
      !exponentialDef.val b c ∧ !exponentialDef.val (a * c) t”

section sigma0
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] in
theorem eval_graph_poly (P : ArithmeticSemiterm Empty n) (t : V) (e : Fin n → V) :
    (graph (poly P)).Eval (t :> e) Empty.elim ↔ t = P.val e Empty.elim := by
  simp [graph, Semiterm.val_bShift', Function.comp_def]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] in
theorem eval_graph_add (A B : BoundTerm n) (t : V) (e : Fin n → V) :
    (graph (add A B)).Eval (t :> e) Empty.elim ↔
      ∃ a b, (graph A).Eval (a :> e) Empty.elim ∧ (graph B).Eval (b :> e) Empty.elim ∧ t = a + b := by
  simp [graph, Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] in
theorem eval_graph_mul (A B : BoundTerm n) (t : V) (e : Fin n → V) :
    (graph (mul A B)).Eval (t :> e) Empty.elim ↔
      ∃ a b, (graph A).Eval (a :> e) Empty.elim ∧ (graph B).Eval (b :> e) Empty.elim ∧ t = a * b := by
  simp [graph, Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar]

theorem eval_graph_exp2 (A B : BoundTerm n) (t : V) (e : Fin n → V) :
    (graph (exp2 A B)).Eval (t :> e) Empty.elim ↔
      ∃ a b, (graph A).Eval (a :> e) Empty.elim ∧ (graph B).Eval (b :> e) Empty.elim ∧
        ∃ c, Exponential b c ∧ Exponential (a * c) t := by
  simp [graph, Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar]

end sigma0

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The value in models of `𝗜𝚺₁`. -/
noncomputable def vval : BoundTerm n → (Fin n → V) → V
  | poly P, e => P.val e Empty.elim
  | add A B, e => A.vval e + B.vval e
  | mul A B, e => A.vval e * B.vval e
  | exp2 A B, e => Exp.exp (A.vval e * Exp.exp (B.vval e))

theorem eval_graph (A : BoundTerm n) (t : V) (e : Fin n → V) :
    (graph A).Eval (t :> e) Empty.elim ↔ t = A.vval e := by
  induction A generalizing t with
  | poly P => rw [eval_graph_poly]; rfl
  | add A B ihA ihB =>
    rw [eval_graph_add]; simp [ihA, ihB, vval]
  | mul A B ihA ihB =>
    rw [eval_graph_mul]; simp [ihA, ihB, vval]
  | exp2 A B ihA ihB =>
    rw [eval_graph_exp2]
    simp only [ihA, ihB, vval]
    constructor
    · rintro ⟨_, _, rfl, rfl, x, hx, ht⟩
      rw [hx.uniq (exponential_exp _)] at ht
      exact ht.uniq (exponential_exp _)
    · rintro rfl
      exact ⟨_, _, rfl, rfl, _, exponential_exp _, exponential_exp _⟩

theorem tau_eq (X D : V) :
    PRAWitnessCodeGrowth.tau X D = Exp.exp ((X + 4) * Exp.exp D) := rfl

end sigma1

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem val_term_add (A B : BoundTerm n) (e : Fin n → M) :
    (add A B).term.val e Empty.elim = A.term.val e Empty.elim + B.term.val e Empty.elim := by
  simp only [term, Semiterm.val_func]
  congr 1; funext i; revert i; simp [Fin.forall_fin_succ]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem val_term_mul (A B : BoundTerm n) (e : Fin n → M) :
    (mul A B).term.val e Empty.elim = A.term.val e Empty.elim * B.term.val e Empty.elim := by
  simp only [term, Semiterm.val_func]
  congr 1; funext i; revert i; simp [Fin.forall_fin_succ]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem val_term_exp2 (A B : BoundTerm n) (e : Fin n → M) :
    (exp2 A B).term.val e Empty.elim =
      PRAHistoryTruncation.expF (A.term.val e Empty.elim *
        PRAHistoryTruncation.expF (B.term.val e Empty.elim)) := by
  simp [term, Semiterm.val_func, expF_eq]
  rfl

theorem eval_graph_model (A : BoundTerm n) (t : M) (e : Fin n → M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    (graph A).Eval (t :> e) Empty.elim ↔ t = A.term.val e Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  induction A generalizing t with
  | poly P => rw [eval_graph_poly]; simp [term, val_lMap_std]
  | add A B ihA ihB =>
    rw [eval_graph_add, val_term_add]; simp [ihA, ihB]
  | mul A B ihA ihB =>
    rw [eval_graph_mul, val_term_mul]; simp [ihA, ihB]
  | exp2 A B ihA ihB =>
    rw [eval_graph_exp2, val_term_exp2]
    simp only [ihA, ihB]
    constructor
    · rintro ⟨_, _, rfl, rfl, c, hc, ht⟩
      rw [hc.uniq (PRAHistoryTruncation.exponential_expF _)] at ht
      exact ht.uniq (PRAHistoryTruncation.exponential_expF _)
    · rintro rfl
      exact ⟨_, _, rfl, rfl, _, PRAHistoryTruncation.exponential_expF _,
        PRAHistoryTruncation.exponential_expF _⟩

theorem mono_term (A : BoundTerm n) : Mono M (fun e => A.term.val e Empty.elim) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  induction A with
  | poly P => intro e e' h; simpa [term, val_lMap_std] using term_mono P e e' h
  | add A B ihA ihB =>
    intro e e' h; dsimp only; rw [val_term_add, val_term_add]
    exact add_le_add (ihA e e' h) (ihB e e' h)
  | mul A B ihA ihB =>
    intro e e' h; dsimp only; rw [val_term_mul, val_term_mul]
    exact mul_le_mul' (ihA e e' h) (ihB e e' h)
  | exp2 A B ihA ihB =>
    intro e e' h; dsimp only; rw [val_term_exp2, val_term_exp2]
    exact PRAHistoryTruncation.expF_mono
      (mul_le_mul' (ihA e e' h) (PRAHistoryTruncation.expF_mono (ihB e e' h)))

end models

theorem dominates_term (A : BoundTerm n) : PRA ⊢ dominates A.graph A.term := by
  refine PRAWitnessExpBounds.dominates_of_val _ _ fun M _ _ _ hM t e ht => ?_
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [eval_lMap_std, eval_graph_model] at ht
  rw [eval_le_lMap, ht]

/-- `tau X D` as a bound term. -/
noncomputable def tauT (X D : BoundTerm n) : BoundTerm n := exp2 (add X (poly ‘4’)) D

theorem vval_tauT {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (X D : BoundTerm n) (e : Fin n → V) :
    (tauT X D).vval e = PRAWitnessCodeGrowth.tau (X.vval e) (D.vval e) := by
  simp [tauT, vval, tau_eq]

end BoundTerm

section models
open BoundTerm
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- **Witness bounds from a bound term**: the witness of `∃⁰ ψ` is below the
`𝗜𝚺₁` value of `A`. -/
theorem wb_exs_bt {n : ℕ} (ψ : ArithmeticSemisentence (n + 1)) (hψ : Hierarchy 𝚺 1 ψ)
    (A : BoundTerm n)
    (hI : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V) (x : V),
      ψ.Eval (x :> e) Empty.elim → x ≤ A.vval e)
    (hWB : WB M ψ) : WB M (∃⁰ ψ) :=
  wb_exs_bound ψ hψ A.graph A.term (dominates_term A) (mono_term A)
    (fun V _ _ e x h => ⟨A.vval e, (eval_graph A _ e).mpr rfl, x, hI V e x h, h⟩) hWB

end models

end DiophantineConsistency.PRAWitnessBoundTerms

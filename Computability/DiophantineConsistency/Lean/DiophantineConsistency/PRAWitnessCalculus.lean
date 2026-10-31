import DiophantineConsistency.PRABndRewriting
import Foundation.FirstOrder.Arithmetic.Exponential.Bit
/-! # A compositional witness-bound calculus

`bnd φ` (`StrictSigmaOneInduction`) bounds every unbounded existential of `φ`
by one new last variable `w`. `WB M φ` says: in `M`, whenever `φ` holds,
`bnd φ` holds at a bound that is a *monotone* function of the free variables.

Monotonicity is what makes the predicate compositional. Below a bounded
universal `∀ x < t`, the witnesses of the body depend on `x`, and one `w` must
serve every `x < t`; a monotone bound evaluated at `t` does. So `WB` is closed
under the constructors that Foundation's `Σ₁` definitions are built from:

* open formulas (`wb_open`), `⋏` (`wb_and`), `⋎` (`wb_or`);
* universals `∀⁰ (χ ⋎ ψ)` with an open guard `χ` whose failure bounds the
  variable (`wb_all_guard`), which covers `∀ x < t`, `∀ x ≤ t` and `∀ x ∈' t`;
* existentials with a monotone witness bound (`wb_exs`), which covers the
  bounded forms `∃ x < t` and `∃ x ≤ t` with the bound read off the guard;
* substitution of `ℒₒᵣ` terms (`wb_rew`), which covers Foundation's `!φ`
  embeddings, using that term values are monotone in `𝗣𝗔⁻` (`term_mono`).

A bound for a large definition then needs arithmetic only at its genuinely
unbounded existentials. Only `𝗣𝗔⁻` is assumed, so the calculus applies to the
arithmetic reduct of every candidate-PRA model. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessCalculus
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction

variable (M : Type) [ORingStructure M]

/-- A bound that grows with every argument. -/
def Mono {n : ℕ} (B : (Fin n → M) → M) : Prop :=
  ∀ e e' : Fin n → M, (∀ i, e i ≤ e' i) → B e ≤ B e'

/-- **`φ` has witnesses below a monotone bound** in `M`. -/
def WB {n : ℕ} (φ : ArithmeticSemisentence n) : Prop :=
  ∃ B : (Fin n → M) → M, Mono M B ∧
    ∀ e, φ.Eval e Empty.elim → (bnd φ).Eval (Fin.snoc e (B e)) Empty.elim

variable {M} [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-! ## Monotone bounds -/

theorem mono_const {n : ℕ} (c : M) : Mono M (fun _ : Fin n → M => c) :=
  fun _ _ _ => le_rfl

theorem mono_add {n : ℕ} {B C : (Fin n → M) → M} (hB : Mono M B) (hC : Mono M C) :
    Mono M (fun e => B e + C e) :=
  fun e e' h => add_le_add (hB e e' h) (hC e e' h)

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] in
theorem mono_cons {n : ℕ} {B : (Fin (n + 1) → M) → M} {T : (Fin n → M) → M}
    (hB : Mono M B) (hT : Mono M T) : Mono M (fun e => B (T e :> e)) := by
  intro e e' h
  apply hB
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hT e e' h
  · simpa using h j

/-- **Values of `ℒₒᵣ` terms are monotone** in every model of `𝗣𝗔⁻`. -/
theorem term_mono {n : ℕ} :
    ∀ t : Semiterm ℒₒᵣ Empty n, Mono M (fun e => t.val e Empty.elim)
  | #x => fun _ _ h => h x
  | &x => Empty.elim x
  | .func f v => by
      intro e e' h
      have ih : ∀ i, (v i).val e Empty.elim ≤ (v i).val e' Empty.elim :=
        fun i => term_mono (v i) e e' h
      cases f with
      | zero => exact le_of_eq (congrArg _ (funext fun i => i.elim0))
      | one => exact le_of_eq (congrArg _ (funext fun i => i.elim0))
      | add =>
          simp only [Semiterm.val_func]
          exact add_le_add (ih 0) (ih 1)
      | mul =>
          simp only [Semiterm.val_func]
          exact mul_le_mul' (ih 0) (ih 1)

/-! ## Closure rules -/

theorem wb_open {n : ℕ} {φ : ArithmeticSemisentence n} (h : φ.Open) : WB M φ := by
  refine ⟨fun _ => 0, mono_const 0, fun e he => ?_⟩
  rw [bnd_open φ h]
  exact (eval_bnd_atom φ e 0 Empty.elim).mpr he

theorem wb_and {n : ℕ} {φ ψ : ArithmeticSemisentence n} (hφ : WB M φ) (hψ : WB M ψ) :
    WB M (φ ⋏ ψ) := by
  obtain ⟨B, hB, hb⟩ := hφ
  obtain ⟨C, hC, hc⟩ := hψ
  refine ⟨fun e => B e + C e, mono_add hB hC, fun e he => ?_⟩
  simp only [bnd, LogicalConnective.HomClass.map_and] at he ⊢
  exact ⟨eval_bnd_mono φ e Empty.elim le_self_add (hb e he.1),
    eval_bnd_mono ψ e Empty.elim le_add_self (hc e he.2)⟩

theorem wb_or {n : ℕ} {φ ψ : ArithmeticSemisentence n} (hφ : WB M φ) (hψ : WB M ψ) :
    WB M (φ ⋎ ψ) := by
  obtain ⟨B, hB, hb⟩ := hφ
  obtain ⟨C, hC, hc⟩ := hψ
  refine ⟨fun e => B e + C e, mono_add hB hC, fun e he => ?_⟩
  simp only [bnd, LogicalConnective.HomClass.map_or] at he ⊢
  exact he.imp (fun h => eval_bnd_mono φ e Empty.elim le_self_add (hb e h))
    (fun h => eval_bnd_mono ψ e Empty.elim le_add_self (hc e h))

/-- **Guarded universal.** Where the open guard `χ` fails, the variable is at
most the monotone `T`; the body's bound is taken there. -/
theorem wb_all_guard {n : ℕ} {χ ψ : ArithmeticSemisentence (n + 1)} (hχ : χ.Open)
    (T : (Fin n → M) → M) (hT : Mono M T)
    (hguard : ∀ x e, ¬ χ.Eval (x :> e) Empty.elim → x ≤ T e)
    (hψ : WB M ψ) : WB M (∀⁰ (χ ⋎ ψ)) := by
  obtain ⟨B, hB, hb⟩ := hψ
  refine ⟨fun e => B (T e :> e), mono_cons hB hT, fun e he => ?_⟩
  simp only [bnd, Semiformula.eval_all, LogicalConnective.HomClass.map_or] at he ⊢
  intro x
  rw [cons_snoc, bnd_open χ hχ, eval_bnd_atom]
  by_cases hx : χ.Eval (x :> e) Empty.elim
  · exact Or.inl hx
  · right
    have hψx := (he x).resolve_left hx
    refine eval_bnd_mono ψ (x :> e) Empty.elim (hB _ _ ?_) (hb _ hψx)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hguard x e hx
    · simp

/-- **Existential with a monotone witness bound.** -/
theorem wb_exs {n : ℕ} {ψ : ArithmeticSemisentence (n + 1)}
    (F : (Fin n → M) → M) (hF : Mono M F)
    (hwit : ∀ e, (∃ x, ψ.Eval (x :> e) Empty.elim) →
      ∃ x, x ≤ F e ∧ ψ.Eval (x :> e) Empty.elim)
    (hψ : WB M ψ) : WB M (∃⁰ ψ) := by
  obtain ⟨B, hB, hb⟩ := hψ
  refine ⟨fun e => F e + 1 + B (F e :> e),
    mono_add (mono_add hF (mono_const 1)) (mono_cons hB hF), fun e he => ?_⟩
  simp only [Semiformula.eval_ex] at he
  obtain ⟨x, hxF, hx⟩ := hwit e he
  simp only [bnd, Semiformula.eval_bexs]
  refine ⟨x, ?_, ?_⟩
  · have hlt : x < F e + 1 + B (F e :> e) :=
      lt_of_lt_of_le (lt_succ_iff_le.mpr hxF) le_self_add
    simpa [val_lastVar] using hlt
  · rw [cons_snoc]
    refine eval_bnd_mono ψ (x :> e) Empty.elim ?_ (hb _ hx)
    refine le_trans (hB _ _ ?_) le_add_self
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hxF
    · simp

/-- **Substitution of terms.** -/
theorem wb_rew {k n : ℕ} {ψ : ArithmeticSemisentence k} (ω : Rew ℒₒᵣ Empty k Empty n)
    (hψ : WB M ψ) : WB M (ω ▹ ψ) := by
  obtain ⟨B, hB, hb⟩ := hψ
  let V : (Fin n → M) → Fin k → M := fun e i => (ω #i).val e Empty.elim
  refine ⟨fun e => B (V e), fun e e' h => hB _ _ (fun i => term_mono (ω #i) e e' h),
    fun e he => ?_⟩
  have hf : (Semiterm.val e Empty.elim ∘ ⇑ω ∘ Semiterm.fvar) = (Empty.elim : Empty → M) :=
    funext fun x => Empty.elim x
  rw [Semiformula.eval_rew, hf] at he
  have hn := PRABndRewriting.natural ψ ω e (B (V e))
  exact hn.mpr (hb (V e) (by simpa [V, Function.comp_def] using he))

/-- A conjunction with `⊥` never holds. -/
theorem wb_bot_and {n : ℕ} (ψ : ArithmeticSemisentence n) : WB M (⊥ ⋏ ψ) :=
  ⟨fun _ => 0, mono_const 0, fun _ h => by simp at h⟩

theorem wb_and_bot {n : ℕ} (ψ : ArithmeticSemisentence n) : WB M (ψ ⋏ ⊥) :=
  ⟨fun _ => 0, mono_const 0, fun _ h => by simp at h⟩

/-- A disjunction with `⊤` keeps `⊤` under `bnd`. -/
theorem wb_top_or {n : ℕ} (ψ : ArithmeticSemisentence n) : WB M (⊤ ⋎ ψ) :=
  ⟨fun _ => 0, mono_const 0, fun _ _ => by simp [bnd]⟩

theorem wb_or_top {n : ℕ} (ψ : ArithmeticSemisentence n) : WB M (ψ ⋎ ⊤) :=
  ⟨fun _ => 0, mono_const 0, fun _ _ => by simp [bnd]⟩

/-- Foundation's `!ψ t₁ … tₖ` embedding. -/
theorem wb_subst {k n : ℕ} {ψ : ArithmeticSemisentence k} (v : Fin k → ArithmeticSemiterm Empty n)
    (hψ : WB M ψ) : WB M (Rewriting.subst ψ v) :=
  wb_rew (Rew.subst v) hψ

/-- A negated embedding `∼(!ψ t₁ … tₖ)` reduces to the negated definition. -/
theorem wb_neg_subst {k n : ℕ} {ψ : ArithmeticSemisentence k}
    (v : Fin k → ArithmeticSemiterm Empty n) (hψ : WB M (∼ψ)) :
    WB M (∼(Rewriting.subst ψ v)) := by
  have h : (∼(Rewriting.subst ψ v) : ArithmeticSemisentence n) = Rewriting.subst (∼ψ) v :=
    (LogicalConnective.HomClass.map_neg (Semiformula.rew (Rew.subst v)) ψ).symm
  rw [h]
  exact wb_subst v hψ

/-- An explicit bound given by an `ℒₒᵣ` term, as in the earlier per-graph
bound modules, is a monotone bound. -/
theorem wb_of_term_bound {n : ℕ} {φ : ArithmeticSemisentence n} (P : ArithmeticSemiterm Empty n)
    (h : ∀ e : Fin n → M, φ.Eval e Empty.elim →
      (bnd φ).Eval (Fin.snoc e (P.val e Empty.elim)) Empty.elim) : WB M φ :=
  ⟨fun e => P.val e Empty.elim, term_mono P, h⟩

/-! ## Derived rules for Foundation's bounded quantifiers -/

theorem wb_bexsLT {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.bexsLT t) := by
  unfold Semiformula.bexsLT FirstOrder.bexs
  refine wb_exs (fun e => t.val e Empty.elim) (term_mono t) (fun e ⟨x, hx⟩ => ⟨x, ?_, hx⟩)
    (wb_and (wb_open (by simp)) hψ)
  simp [Function.comp_def] at hx
  exact le_of_lt hx.1

theorem wb_bexsLE {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.bexsLE t) := by
  unfold Semiformula.bexsLE FirstOrder.bexs
  refine wb_exs (fun e => t.val e Empty.elim) (term_mono t) (fun e ⟨x, hx⟩ => ⟨x, ?_, hx⟩)
    (wb_and (wb_open (by simp)) hψ)
  simp [Semiformula.Operator.le_def, Function.comp_def] at hx
  exact le_iff_eq_or_lt.mpr hx.1

theorem wb_ballLT {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.ballLT t) := by
  unfold Semiformula.ballLT FirstOrder.ball
  rw [Semiformula.imp_eq]
  refine wb_all_guard (by simp) (fun e => t.val e Empty.elim) (term_mono t)
    (fun x e hx => ?_) hψ
  simp [Function.comp_def] at hx
  exact le_of_lt hx

theorem wb_ballLE {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.ballLE t) := by
  unfold Semiformula.ballLE FirstOrder.ball
  rw [Semiformula.imp_eq]
  refine wb_all_guard (by simp) (fun e => t.val e Empty.elim) (term_mono t)
    (fun x e hx => ?_) hψ
  simp [Semiformula.Operator.le_def, Function.comp_def] at hx
  exact le_iff_eq_or_lt.mpr (or_iff_not_imp_left.mpr hx)

theorem wb_bexsLTSucc {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.bexsLTSucc t) :=
  wb_bexsLT _ hψ

theorem wb_ballLTSucc {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M ψ) : WB M (ψ.ballLTSucc t) :=
  wb_ballLT _ hψ

/-! ## Negated bounded quantifiers -/

theorem wb_neg_bexsLT {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M (∼ψ)) : WB M (∼(ψ.bexsLT t)) := by
  have h : (∼(ψ.bexsLT t) : ArithmeticSemisentence n) = (∼ψ).ballLT t := by
    simp [Semiformula.bexsLT, Semiformula.ballLT, FirstOrder.bexs, FirstOrder.ball,
      Semiformula.imp_eq]
  rw [h]; exact wb_ballLT t hψ

theorem wb_neg_ballLT {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M (∼ψ)) : WB M (∼(ψ.ballLT t)) := by
  have h : (∼(ψ.ballLT t) : ArithmeticSemisentence n) = (∼ψ).bexsLT t := by
    simp [Semiformula.bexsLT, Semiformula.ballLT, FirstOrder.bexs, FirstOrder.ball,
      Semiformula.imp_eq]
  rw [h]; exact wb_bexsLT t hψ

theorem wb_neg_bexsLE {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M (∼ψ)) : WB M (∼(ψ.bexsLE t)) := by
  have h : (∼(ψ.bexsLE t) : ArithmeticSemisentence n) = (∼ψ).ballLE t := by
    simp [Semiformula.bexsLE, Semiformula.ballLE, FirstOrder.bexs, FirstOrder.ball,
      Semiformula.imp_eq]
  rw [h]; exact wb_ballLE t hψ

theorem wb_neg_ballLE {n : ℕ} (t : ArithmeticSemiterm Empty n) {ψ : ArithmeticSemisentence (n + 1)}
    (hψ : WB M (∼ψ)) : WB M (∼(ψ.ballLE t)) := by
  have h : (∼(ψ.ballLE t) : ArithmeticSemisentence n) = (∼ψ).bexsLE t := by
    simp [Semiformula.bexsLE, Semiformula.ballLE, FirstOrder.bexs, FirstOrder.ball,
      Semiformula.imp_eq]
  rw [h]; exact wb_bexsLE t hψ

theorem wb_neg_bexsLTSucc {n : ℕ} (t : ArithmeticSemiterm Empty n)
    {ψ : ArithmeticSemisentence (n + 1)} (hψ : WB M (∼ψ)) : WB M (∼(ψ.bexsLTSucc t)) :=
  wb_neg_bexsLT _ hψ

theorem wb_neg_ballLTSucc {n : ℕ} (t : ArithmeticSemiterm Empty n)
    {ψ : ArithmeticSemisentence (n + 1)} (hψ : WB M (∼ψ)) : WB M (∼(ψ.ballLTSucc t)) :=
  wb_neg_ballLT _ hψ

/-! ## Membership and the `∈'` quantifiers

For `ℒₒᵣ` the membership operator is Foundation's `bitDef`, so its atoms are
not open; they reduce to the bit graph in either polarity. -/

theorem wb_emb {n : ℕ} {ψ : ArithmeticSemisentence n} (hψ : WB M ψ) :
    WB M (Rewriting.emb ψ : ArithmeticSemisentence n) :=
  wb_rew Rew.emb hψ

theorem wb_mem {n : ℕ} (t u : ArithmeticSemiterm Empty n) (hbit : WB M bitDef.val) :
    WB M (Semiformula.Operator.Mem.mem.operator ![t, u]) := by
  unfold Semiformula.Operator.operator
  rw [operator_mem_def]
  exact wb_subst _ (wb_emb hbit)

theorem wb_not_mem {n : ℕ} (t u : ArithmeticSemiterm Empty n) (hbit : WB M (∼bitDef.val)) :
    WB M (∼Semiformula.Operator.Mem.mem.operator ![t, u]) := by
  unfold Semiformula.Operator.operator
  rw [operator_mem_def]
  refine wb_neg_subst _ ?_
  have h : (∼(Rewriting.emb bitDef.val : ArithmeticSemisentence 2)) = Rewriting.emb (∼bitDef.val) :=
    (LogicalConnective.HomClass.map_neg (Semiformula.rew Rew.emb) bitDef.val).symm
  rw [h]
  exact wb_emb hbit

/-- A Foundation operator (such as `memRelOpr`) is its sentence, embedded. -/
theorem wb_operator {k n : ℕ} (o : Semiformula.Operator ℒₒᵣ k)
    (v : Fin k → ArithmeticSemiterm Empty n) (ho : WB M o.sentence) : WB M (o.operator v) := by
  unfold Semiformula.Operator.operator
  exact wb_subst _ (wb_emb ho)

theorem wb_neg_operator {k n : ℕ} (o : Semiformula.Operator ℒₒᵣ k)
    (v : Fin k → ArithmeticSemiterm Empty n) (ho : WB M (∼o.sentence)) :
    WB M (∼o.operator v) := by
  unfold Semiformula.Operator.operator
  refine wb_neg_subst _ ?_
  have h : (∼(Rewriting.emb o.sentence : ArithmeticSemisentence k)) = Rewriting.emb (∼o.sentence) :=
    (LogicalConnective.HomClass.map_neg (Semiformula.rew Rew.emb) o.sentence).symm
  rw [h]
  exact wb_emb ho

/-- One step of the calculus: the rule that matches the head constructor.
`wb_auto` repeats it; leaves it cannot match (named definitions, genuinely
unbounded existentials) remain as goals or are closed by hypotheses. -/
macro "wb_step" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | (apply wb_open; simp; done)
    | with_reducible apply wb_bot_and | with_reducible apply wb_and_bot
    | with_reducible apply wb_top_or | with_reducible apply wb_or_top
    | with_reducible apply wb_subst
    | with_reducible apply wb_neg_subst
    | with_reducible apply wb_and | with_reducible apply wb_or
    | with_reducible apply wb_bexsLT | with_reducible apply wb_bexsLE
    | with_reducible apply wb_ballLT | with_reducible apply wb_ballLE
    | with_reducible apply wb_bexsLTSucc | with_reducible apply wb_ballLTSucc
    | with_reducible apply wb_neg_bexsLT | with_reducible apply wb_neg_ballLT
    | with_reducible apply wb_neg_bexsLE | with_reducible apply wb_neg_ballLE
    | with_reducible apply wb_neg_bexsLTSucc | with_reducible apply wb_neg_ballLTSucc
    | (with_reducible apply wb_mem; with_reducible assumption)
    | (with_reducible apply wb_not_mem; with_reducible assumption)
    | (with_reducible apply wb_operator; assumption)
    | (with_reducible apply wb_neg_operator; assumption)
    | (simp only [Semiformula.imp_eq, Semiformula.iff_eq, DeMorgan.and, DeMorgan.or,
        DeMorgan.neg, Semiformula.neg_all, Semiformula.neg_ex, ballIn, bexsIn]))

macro "wb_auto" : tactic => `(tactic| repeat' wb_step)

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] in
/-- Transport along a syntactic equality, for rewriting a definition into
constructor form before applying the rules. -/
theorem wb_of_eq {n : ℕ} {φ ψ : ArithmeticSemisentence n} (h : φ = ψ) (hψ : WB M ψ) :
    WB M φ := h ▸ hψ

/-! ## Using a bound -/

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] in
/-- A `WB` formula holds only together with its bounded form at some bound. -/
theorem exists_bound {n : ℕ} {φ : ArithmeticSemisentence n} (h : WB M φ)
    (e : Fin n → M) (he : φ.Eval e Empty.elim) :
    ∃ w, (bnd φ).Eval (Fin.snoc e w) Empty.elim := by
  obtain ⟨B, -, hb⟩ := h
  exact ⟨B e, hb e he⟩

end DiophantineConsistency.PRAWitnessCalculus

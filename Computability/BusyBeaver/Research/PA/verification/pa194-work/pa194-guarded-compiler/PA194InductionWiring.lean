import PA194InductionSchema
import PA194GuardedClosed
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The closure of parameters, and the induction statement in quoted form

Two statements that connect `induction_body` with the induction supplier of
`pa194-model-logic` without importing its modules.

* `tr_close_iter`: for any `Σ₁` iteration `cl` of a binder `B` that inverts opening
  (`free (B φ) = φ`), a guarded derivation of `tr φ` gives one of `tr (cl n φ)` for every
  internal `n`. The closure `close` of the arithmetic development has this shape, with
  `B = bindFormula 0`.
* `indCode_quotes`: `indCode q` written with the quotes of the standard formulas
  `domain`, `zero`, `successor` at bound variables, the form in which the ordinal induction
  statement of the source theory is defined in `pa194-model-axioms`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

theorem indBody_valid {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    IsSemiformula PA194PAeq.language 0 (indBody p) := by
  have hpS := substs1_succVar_valid hp
  have hp0 : IsSemiformula PA194PAeq.language 0 (substs1 PA194PAeq.language zeroT p) :=
    IsSemiformula.substs1 zeroT_valid hp
  have himp : IsSemiformula PA194PAeq.language 1
      (neg PA194PAeq.language p ^⋎ substs1 PA194PAeq.language succVar p) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hp,hpS⟩
  have hall1 : IsSemiformula PA194PAeq.language 0
      (^∀ (neg PA194PAeq.language p ^⋎ substs1 PA194PAeq.language succVar p)) :=
    IsSemiformula.all.mpr (by simpa using himp)
  have hall2 : IsSemiformula PA194PAeq.language 0 (^∀ p) :=
    IsSemiformula.all.mpr (by simpa using hp)
  show IsSemiformula PA194PAeq.language 0
    (neg PA194PAeq.language (substs1 PA194PAeq.language zeroT p) ^⋎
      (neg PA194PAeq.language (^∀ (neg PA194PAeq.language p ^⋎
        substs1 PA194PAeq.language succVar p)) ^⋎ ^∀ p))
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hp0,
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hall1,hall2⟩⟩

/-- Iterated closure of parameters. `cl` is any `Σ₁` iteration of `φ ↦ ∀ (B φ)` where `B`
produces a formula of arity one that opens to its argument. -/
theorem tr_close_iter {cl : V → V → V} {B : V → V} (hdef : 𝚺₁-Function₂ cl)
    (h0 : ∀ φ : V, cl 0 φ = φ) (hsucc : ∀ n φ : V, cl (n+1) φ = ^∀ (B (cl n φ)))
    (hB : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ →
      IsSemiformula PA194PAeq.language 1 (B φ) ∧ free PA194PAeq.language (B φ) = φ)
    {φ : V} (hφ : IsSemiformula PA194PAeq.language 0 φ)
    (h : GDerivable T (insert (tr φ) (∅ : V))) (n : V) :
    IsSemiformula PA194PAeq.language 0 (cl n φ) ∧
      GDerivable T (insert (tr (cl n φ)) (∅ : V)) := by
  haveI : 𝚺₁-Function₂ cl := hdef
  induction n using ISigma1.sigma1_succ_induction
  · unfold GDerivable
    definability
  case zero =>
    rw [h0]
    exact ⟨hφ,h⟩
  case succ n ih =>
    obtain ⟨hv,hd⟩ := ih
    obtain ⟨hb,hfree⟩ := hB (cl n φ) hv
    rw [hsucc]
    refine ⟨IsSemiformula.all.mpr (by simpa using hb),?_⟩
    exact tr_close_step hb (by rw [hfree]; exact hd)

/-- The translated induction axiom with any number of its parameters closed. -/
theorem induction_closed {cl : V → V → V} {B : V → V} (hdef : 𝚺₁-Function₂ cl)
    (h0 : ∀ φ : V, cl 0 φ = φ) (hsucc : ∀ n φ : V, cl (n+1) φ = ^∀ (B (cl n φ)))
    (hB : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ →
      IsSemiformula PA194PAeq.language 1 (B φ) ∧ free PA194PAeq.language (B φ) = φ)
    (F : TermFacts (V := V) T) (S : SourceFacts (V := V) T)
    (hInd : ∀ q : V, IsSemiformula SourceL 1 q → Provable T (indCode q)) {p : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) (n : V) :
    GDerivable T (insert (tr (cl n (indBody p))) (∅ : V)) :=
  (tr_close_iter hdef h0 hsucc hB (indBody_valid hp) (induction_body F S hInd hp) n).2

/-- When the closed axiom has no free variable left, it is proved outright. -/
theorem induction_closed_provable {cl : V → V → V} {B : V → V} (hdef : 𝚺₁-Function₂ cl)
    (h0 : ∀ φ : V, cl 0 φ = φ) (hsucc : ∀ n φ : V, cl (n+1) φ = ^∀ (B (cl n φ)))
    (hB : ∀ φ : V, IsSemiformula PA194PAeq.language 0 φ →
      IsSemiformula PA194PAeq.language 1 (B φ) ∧ free PA194PAeq.language (B φ) = φ)
    (F : TermFacts (V := V) T) (S : SourceFacts (V := V) T)
    (hInd : ∀ q : V, IsSemiformula SourceL 1 q → Provable T (indCode q))
    (hdom : Provable T (^∃ (domainCode (^#(0 : V))))) {p : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) (n : V)
    (hs : shift PA194PAeq.language (cl n (indBody p)) = cl n (indBody p)) :
    Provable T (tr (cl n (indBody p))) := by
  have h := tr_close_iter hdef h0 hsucc hB (indBody_valid hp) (induction_body F S hInd hp) n
  exact tr_provable_of_closed hdom h.1 hs h.2

/-- `indCode q` with the quotes of the standard domain, zero and successor formulas. -/
theorem indCode_quotes (q : V) :
    indCode q =
      neg SourceL (^∀ (neg SourceL ((⌜Ordinal.domain (#(0 : Fin 1) : Ordinal.Term 1)⌝ : V) ^⋏
          ⌜Ordinal.zero (#(0 : Fin 1) : Ordinal.Term 1)⌝) ^⋎ q)) ^⋎
        (neg SourceL (^∀ (^∀ (neg SourceL ((⌜Ordinal.domain (#(1 : Fin 2) : Ordinal.Term 2)⌝ : V) ^⋏
            ((⌜Ordinal.domain (#(0 : Fin 2) : Ordinal.Term 2)⌝ : V) ^⋏
              ((⌜Ordinal.successor (#(1 : Fin 2) : Ordinal.Term 2) (#(0 : Fin 2) : Ordinal.Term 2)⌝ : V) ^⋏
                substs1 SourceL (^#(1 : V)) q))) ^⋎ q))) ^⋎
          ^∀ (neg SourceL (⌜Ordinal.domain (#(0 : Fin 1) : Ordinal.Term 1)⌝ : V) ^⋎ q)) := by
  unfold indCode
  rw [← domainCode_quote (V := V) (.bvar (0 : Fin 1)), ← zeroCode_quote (V := V) (.bvar (0 : Fin 1)),
    ← domainCode_quote (V := V) (.bvar (1 : Fin 2)), ← domainCode_quote (V := V) (.bvar (0 : Fin 2)),
    ← successorCode_quote (V := V) (.bvar (1 : Fin 2)) (.bvar (0 : Fin 2))]
  simp [Semiterm.quote_def]

#print axioms indBody_valid
#print axioms tr_close_iter
#print axioms induction_closed
#print axioms induction_closed_provable
#print axioms indCode_quotes
end generic
end PA194GuardedCompiler

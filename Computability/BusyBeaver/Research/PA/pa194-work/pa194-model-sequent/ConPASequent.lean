import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Foundation.FirstOrder.Arithmetic.HFS.Vec
import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Sequents of nonstandard length inside a model of `𝗜𝚺₁`

A Hilbert calculus is given inside a model `V` of `𝗜𝚺₁` by a `𝚺₁` implication constructor
`imp` on codes and a `𝚺₁` provability predicate `Pr`, closed under modus ponens and containing
the combinators `K`, `S`, `B` (composition) and `C` (exchange). Codes and hypothesis lists are
elements of `V`, so a list may have nonstandard length.

For a Foundation vector `Γ = γ₀ ∷ γ₁ ∷ …` and a code `a`,

  `seq Γ a = imp γ₀ (imp γ₁ (… a))`,

and `Pr (seq Γ a)` is read as the sequent `Γ ⊢ a`. Since `seq (γ ∷ Γ) a = imp γ (seq Γ a)`
holds by definition, the deduction theorem at the head of the list is an equation.

Every rule below is a statement about `Pr`, so each is proved by `𝚺₁` induction inside `V`,
on the list or on the length of a suffix of it:

* `seq_weaken`: a theorem is derivable from every list;
* `seq_proj`: `Γ ⊢ Γ.[i]` for `i < len Γ`;
* `seq_mp_formula`, `seq_mp`: modus ponens under a list;
* `seq_adjoin_iff`: the deduction theorem, `γ ∷ Γ ⊢ a` exactly when `Γ ⊢ imp γ a`;
* `seq_cut`: if `Δ ⊢ γ` for every entry `γ` of `Γ`, then `Pr (imp (seq Γ a) (seq Δ a))`;
* `seq_mono`: the same when every entry of `Γ` occurs in `Δ` (weakening, exchange and
  contraction for lists of nonstandard length);
* `seq_all_formula`, `seq_gen`: generalization under a list whose entries are closed under the
  quantifier, for a calculus with a universal quantifier constructor.

Nothing here refers to a particular calculus or machine.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace ConPA.Sequent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (V) in
/-- An implicational Hilbert calculus on the codes of `V`. -/
structure Calc where
  imp : V → V → V
  impDef : 𝚺₁.Semisentence 3
  imp_defined : 𝚺₁-Function₂ imp via impDef
  Pr : V → Prop
  pr_definable : 𝚺₁-Predicate Pr
  mp : ∀ {a b : V}, Pr a → Pr (imp a b) → Pr b
  k : ∀ a b : V, Pr (imp a (imp b a))
  s : ∀ a b c : V, Pr (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  comp : ∀ a b c : V, Pr (imp (imp a b) (imp (imp b c) (imp a c)))
  exchange : ∀ a b c : V, Pr (imp (imp a (imp b c)) (imp b (imp a c)))

attribute [instance] Calc.imp_defined Calc.pr_definable

variable (C : Calc V)

instance imp_definable : 𝚺₁-Function₂ C.imp := C.imp_defined.to_definable

instance imp_definable' (Γ m) : Γ-[m + 1]-Function₂ C.imp := (imp_definable C).of_sigmaOne

/-! ## Derived rules of the implication basis -/

lemma Calc.imp_refl (a : V) : C.Pr (C.imp a a) :=
  C.mp (C.k a a) (C.mp (C.k a (C.imp a a)) (C.s a (C.imp a a) a))

lemma Calc.imp_const {a : V} (ha : C.Pr a) (x : V) : C.Pr (C.imp x a) := C.mp ha (C.k a x)

/-- From `a → b` to `(x → a) → (x → b)`. -/
lemma Calc.imp_lift {a b : V} (hab : C.Pr (C.imp a b)) (x : V) :
    C.Pr (C.imp (C.imp x a) (C.imp x b)) := C.mp (C.imp_const hab x) (C.s x a b)

lemma Calc.imp_trans {a b c : V} (hab : C.Pr (C.imp a b)) (hbc : C.Pr (C.imp b c)) :
    C.Pr (C.imp a c) := C.mp hab (C.imp_lift hbc a)

/-- `γ → ((G → a) → ((γ → G) → a))`: the step of the cut rule. -/
lemma Calc.cut_step (γ G a : V) :
    C.Pr (C.imp γ (C.imp (C.imp G a) (C.imp (C.imp γ G) a))) :=
  C.imp_trans (C.mp (C.imp_refl (C.imp γ G)) (C.exchange (C.imp γ G) γ G))
    (C.comp (C.imp γ G) G a)

/-! ## The implication chain of a list -/

namespace Seq

def blueprint (impDef : 𝚺₁.Semisentence 3) : VecRec.Blueprint 1 where
  nil := .mkSigma “y a. y = a”
  adjoin := .mkSigma “y x xs ih a. !impDef y x ih”

def construction : VecRec.Construction V (blueprint C.impDef) where
  nil := fun v ↦ v 0
  adjoin := fun _ x _ ih ↦ C.imp x ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end Seq

/-- `seq Γ a`: the formula `γ₀ → (γ₁ → (… → a))` for the list `Γ = γ₀ ∷ γ₁ ∷ …`. -/
def seq (Γ a : V) : V := (Seq.construction C).result ![a] Γ

@[simp] lemma seq_nil (a : V) : seq C 0 a = a := by simp [seq, Seq.construction]

@[simp] lemma seq_adjoin (γ Γ a : V) : seq C (γ ∷ Γ) a = C.imp γ (seq C Γ a) := by
  simp [seq, Seq.construction]

def seqDef (impDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 := (Seq.blueprint impDef).resultDef

instance seq_defined : 𝚺₁-Function₂ (seq C) via seqDef C.impDef :=
  (Seq.construction C).result_defined

instance seq_definable : 𝚺₁-Function₂ (seq C) := (seq_defined C).to_definable

instance seq_definable' (Γ m) : Γ-[m + 1]-Function₂ (seq C) := (seq_definable C).of_sigmaOne

/-! ## Structural rules -/

/-- `a → (Γ ⊢ a)`. -/
lemma seq_k (Γ a : V) : C.Pr (C.imp a (seq C Γ a)) := by
  induction Γ using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa using C.imp_refl a
  case adjoin γ Γ ih =>
    rw [seq_adjoin]
    exact C.imp_trans ih (C.k (seq C Γ a) γ)

/-- A theorem is derivable from every list. -/
lemma seq_weaken {a : V} (ha : C.Pr a) (Γ : V) : C.Pr (seq C Γ a) := C.mp ha (seq_k C Γ a)

/-- Modus ponens under a list, as one theorem of the calculus. -/
lemma seq_mp_formula (Γ a b : V) :
    C.Pr (C.imp (seq C Γ (C.imp a b)) (C.imp (seq C Γ a) (seq C Γ b))) := by
  induction Γ using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa using C.imp_refl (C.imp a b)
  case adjoin γ Γ ih =>
    simp only [seq_adjoin]
    exact C.imp_trans (C.imp_lift ih γ) (C.s γ (seq C Γ a) (seq C Γ b))

lemma seq_mp {Γ a b : V} (ha : C.Pr (seq C Γ a)) (hab : C.Pr (seq C Γ (C.imp a b))) :
    C.Pr (seq C Γ b) := C.mp ha (C.mp hab (seq_mp_formula C Γ a b))

/-- A provable implication acts on the conclusion of a sequent. -/
lemma seq_lift {a b : V} (hab : C.Pr (C.imp a b)) (Γ : V) :
    C.Pr (C.imp (seq C Γ a) (seq C Γ b)) :=
  C.mp (seq_weaken C hab Γ) (seq_mp_formula C Γ a b)

/-- The deduction theorem at the inner end of the list: `(γ → (Γ ⊢ a)) → (Γ ⊢ γ → a)`. -/
lemma seq_deduction_formula (Γ γ a : V) :
    C.Pr (C.imp (C.imp γ (seq C Γ a)) (seq C Γ (C.imp γ a))) := by
  induction Γ using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa using C.imp_refl (C.imp γ a)
  case adjoin δ Γ ih =>
    simp only [seq_adjoin]
    exact C.imp_trans (C.exchange γ δ (seq C Γ a)) (C.imp_lift ih δ)

/-- The converse: `(Γ ⊢ γ → a) → (γ → (Γ ⊢ a))`. -/
lemma seq_undeduction_formula (Γ γ a : V) :
    C.Pr (C.imp (seq C Γ (C.imp γ a)) (C.imp γ (seq C Γ a))) := by
  induction Γ using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa using C.imp_refl (C.imp γ a)
  case adjoin δ Γ ih =>
    simp only [seq_adjoin]
    exact C.imp_trans (C.imp_lift ih δ) (C.exchange δ γ (seq C Γ a))

/-- The deduction theorem: `γ ∷ Γ ⊢ a` exactly when `Γ ⊢ γ → a`. -/
theorem seq_adjoin_iff (γ Γ a : V) :
    C.Pr (seq C (γ ∷ Γ) a) ↔ C.Pr (seq C Γ (C.imp γ a)) := by
  rw [seq_adjoin]
  exact ⟨fun h => C.mp h (seq_deduction_formula C Γ γ a),
    fun h => C.mp h (seq_undeduction_formula C Γ γ a)⟩

/-- Every entry of a list is derivable from it. -/
lemma seq_proj (Γ : V) : ∀ i < len Γ, C.Pr (seq C Γ Γ.[i]) := by
  induction Γ using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro i hi; simp at hi
  case adjoin γ Γ ih =>
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simpa using seq_k C Γ γ
    · have hj : j < len Γ := by simpa using hi
      simpa using C.imp_const (ih j hj) γ

lemma index_lt {n k : V} (hk : k < n) : n - (k + 1) < n := by
  have h1 : n - (k + 1) + (k + 1) = n := sub_add_self_of_le (succ_le_iff_lt.mpr hk)
  have h2 : n - (k + 1) < n - (k + 1) + (k + 1) :=
    lt_add_of_pos_right _ (lt_of_le_of_lt (by simp : (0 : V) ≤ k) (lt_add_one k))
  exact lt_of_lt_of_eq h2 h1

/-- If `Δ` derives every entry of `Γ`, then `Δ` derives `(Γ ⊢ a) → a`, for every suffix of
`Γ`. The hypothesis stays outside the induction, which runs on the length of the suffix. -/
lemma seq_cut_suffix (Γ Δ a : V) (h : ∀ i < len Γ, C.Pr (seq C Δ Γ.[i])) :
    ∀ k, k ≤ len Γ → C.Pr (seq C Δ (C.imp (seq C (takeLast Γ k) a) a)) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simpa using seq_weaken C (C.imp_refl a) Δ
  case succ k ih =>
    intro hk
    have hlt : k < len Γ := succ_le_iff_lt.mp hk
    rw [takeLast_succ_of_lt hlt, seq_adjoin]
    have hγ := h _ (index_lt hlt)
    have hG := ih (le_of_lt hlt)
    exact seq_mp C hG (seq_mp C hγ (seq_weaken C (C.cut_step _ _ _) Δ))

/-- Cut: if `Δ ⊢ γ` for every entry `γ` of `Γ`, then `(Γ ⊢ a) → (Δ ⊢ a)` is a theorem. -/
theorem seq_cut (Γ Δ a : V) (h : ∀ i < len Γ, C.Pr (seq C Δ Γ.[i])) :
    C.Pr (C.imp (seq C Γ a) (seq C Δ a)) := by
  have h1 := seq_cut_suffix C Γ Δ a h (len Γ) (le_refl _)
  rw [takeLast_len_self] at h1
  exact C.imp_trans (seq_k C Δ (seq C Γ a)) (C.mp h1 (seq_mp_formula C Δ (seq C Γ a) a))

/-- Weakening, exchange and contraction: `Γ ⊢ a` gives `Δ ⊢ a` when every entry of `Γ` occurs
in `Δ`. -/
theorem seq_mono (Γ Δ a : V) (h : ∀ i < len Γ, ∃ j < len Δ, Γ.[i] = Δ.[j]) :
    C.Pr (C.imp (seq C Γ a) (seq C Δ a)) :=
  seq_cut C Γ Δ a (fun i hi => by
    obtain ⟨j, hj, e⟩ := h i hi
    rw [e]
    exact seq_proj C Δ j hj)

theorem seq_cut_rule {Γ Δ a : V} (ha : C.Pr (seq C Γ a))
    (h : ∀ i < len Γ, C.Pr (seq C Δ Γ.[i])) : C.Pr (seq C Δ a) :=
  C.mp ha (seq_cut C Γ Δ a h)

theorem seq_mono_rule {Γ Δ a : V} (ha : C.Pr (seq C Γ a))
    (h : ∀ i < len Γ, ∃ j < len Δ, Γ.[i] = Δ.[j]) : C.Pr (seq C Δ a) :=
  C.mp ha (seq_mono C Γ Δ a h)

/-- Adding a hypothesis at the head. -/
theorem seq_up {Γ a : V} (ha : C.Pr (seq C Γ a)) (γ : V) : C.Pr (seq C (γ ∷ Γ) a) := by
  rw [seq_adjoin]
  exact C.imp_const ha γ

/-! ## Generalization -/

variable (V) in
/-- A calculus with a universal quantifier constructor `all x a`. -/
structure Quant extends Calc V where
  all : V → V → V
  allDef : 𝚺₁.Semisentence 3
  all_defined : 𝚺₁-Function₂ all via allDef
  gen : ∀ (x : V) {a : V}, Pr a → Pr (all x a)
  dist : ∀ x a b : V, Pr (imp (all x (imp a b)) (imp (all x a) (all x b)))

attribute [instance] Quant.all_defined

variable (Q : Quant V)

instance all_definable : 𝚺₁-Function₂ Q.all := Q.all_defined.to_definable

instance all_definable' (Γ m) : Γ-[m + 1]-Function₂ Q.all := (all_definable Q).of_sigmaOne

/-- `∀x (Γ ⊢ a) → (Γ ⊢ ∀x a)` for suffixes of a list whose entries `γ` satisfy `γ → ∀x γ`. -/
lemma seq_all_suffix (x Γ a : V)
    (hv : ∀ i < len Γ, Q.Pr (Q.imp Γ.[i] (Q.all x Γ.[i]))) :
    ∀ k, k ≤ len Γ → Q.Pr (Q.imp (Q.all x (seq Q.toCalc (takeLast Γ k) a))
      (seq Q.toCalc (takeLast Γ k) (Q.all x a))) := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simpa using Q.toCalc.imp_refl (Q.all x a)
  case succ k ih =>
    intro hk
    have hlt : k < len Γ := succ_le_iff_lt.mp hk
    simp only [takeLast_succ_of_lt hlt, seq_adjoin]
    have hγ := hv _ (index_lt hlt)
    have hG := ih (le_of_lt hlt)
    exact Q.toCalc.imp_trans (Q.dist x _ _)
      (Q.toCalc.imp_trans (Q.mp hγ (Q.comp _ _ _)) (Q.toCalc.imp_lift hG _))

theorem seq_all_formula (x Γ a : V)
    (hv : ∀ i < len Γ, Q.Pr (Q.imp Γ.[i] (Q.all x Γ.[i]))) :
    Q.Pr (Q.imp (Q.all x (seq Q.toCalc Γ a)) (seq Q.toCalc Γ (Q.all x a))) := by
  have h1 := seq_all_suffix Q x Γ a hv (len Γ) (le_refl _)
  simpa using h1

/-- Generalization under a list whose entries do not depend on the variable. -/
theorem seq_gen {Γ a : V} (x : V) (ha : Q.Pr (seq Q.toCalc Γ a))
    (hv : ∀ i < len Γ, Q.Pr (Q.imp Γ.[i] (Q.all x Γ.[i]))) :
    Q.Pr (seq Q.toCalc Γ (Q.all x a)) :=
  Q.mp (Q.gen x ha) (seq_all_formula Q x Γ a hv)

#print axioms seq_proj
#print axioms seq_mp
#print axioms seq_cut
#print axioms seq_mono
#print axioms seq_gen
end model
end ConPA.Sequent

import ZFCinPA.ModelCodedShiftCancellation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding

set_option autoImplicit false

/-!
Compile a fixed ordinary proof with a finite buffer of free-variable shifts.
The translation at buffer b+1 commutes with a source shift applied at buffer b.
ALL increases the buffer; an explicit SHIFT consumes one. A bound computed from
this external proof tree prevents underflow. Source axioms need target proofs,
so open schema instances can be used. Internal formulas need not be shift-fixed.
This module supplies the logical compiler interface, not its predicate instance.
The finite-sequent coding follows TypedTemplateProofCompiler in this repository.
-/
namespace LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]

section sequents
variable (f : Proposition L₁ → Formula V L₂)
/-- Translate a finite standard sequent into an HFS-coded typed sequent.

We fold over a list instead of choosing a code for a mapped finite set.  The
membership theorem below makes the construction's order irrelevant and also
handles translations which identify two source formulas. -/
noncomputable def translateList :
    List (Proposition L₁) → Bootstrapping.Sequent V L₂
  | [] => ∅
  | p :: Γ => insert (f p) (translateList Γ)

noncomputable def translateSequent
    (Γ : Finset (Proposition L₁)) : Bootstrapping.Sequent V L₂ :=
  translateList f Γ.toList

omit [L₁.DecidableEq] in
lemma mem_translateList_iff {q : V}
    {Γ : List (Proposition L₁)} :
    q ∈ (translateList f Γ).val ↔
      ∃ p ∈ Γ, (f p).val = q := by
  induction Γ with
  | nil => simp [translateList]
  | cons p Γ ih =>
      simp only [translateList, Bootstrapping.Sequent.val_insert,
        mem_bitInsert_iff, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨r, hr, htr⟩)
        · exact ⟨p, Or.inl rfl, rfl⟩
        · exact ⟨r, Or.inr hr, htr⟩
      · rintro ⟨r, rfl | hr, htr⟩
        · exact Or.inl htr.symm
        · exact Or.inr ⟨r, hr, htr⟩

lemma mem_translateSequent_iff {q : V}
    {Γ : Finset (Proposition L₁)} :
    q ∈ (translateSequent f Γ).val ↔
      ∃ p ∈ Γ, (f p).val = q := by
  simp only [translateSequent, mem_translateList_iff,
    Finset.mem_toList]

lemma formula_mem_translateSequent {p : Proposition L₁}
    {Γ : Finset (Proposition L₁)} (hp : p ∈ Γ) :
    f p ∈ translateSequent f Γ := by
  exact (mem_translateSequent_iff (f := f)).mpr ⟨p, hp, rfl⟩

lemma translateSequent_insert (p : Proposition L₁)
    (Γ : Finset (Proposition L₁)) :
    translateSequent f (insert p Γ) =
      insert (f p) (translateSequent f Γ) := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  simp only [mem_translateSequent_iff,
    Bootstrapping.Sequent.val_insert, mem_bitInsert_iff,
    Finset.mem_insert]
  constructor
  · rintro ⟨r, rfl | hr, htr⟩
    · exact Or.inl htr.symm
    · exact Or.inr ⟨r, hr, htr⟩
  · rintro (rfl | ⟨r, hr, htr⟩)
    · exact ⟨p, Or.inl rfl, rfl⟩
    · exact ⟨r, Or.inr hr, htr⟩

lemma translateSequent_singleton (p : Proposition L₁) :
    translateSequent f {p} =
      ({f p} : Bootstrapping.Sequent V L₂) := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  simp only [mem_translateSequent_iff,
    Bootstrapping.Sequent.val_singleton, mem_singleton_iff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨r, rfl, htr⟩
    exact htr.symm
  · rintro rfl
    exact ⟨p, rfl, rfl⟩

lemma translateSequent_mono {Γ Δ : Finset (Proposition L₁)}
    (h : Γ ⊆ Δ) :
    translateSequent f Γ ⊆ translateSequent f Δ := by
  intro q hq
  rcases (mem_translateSequent_iff (f := f)).mp hq with ⟨p, hp, rfl⟩
  exact formula_mem_translateSequent f (h hp)

end sequents

structure BufferedTranslation (V : Type*) (L₁ L₂ : Language)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    [L₂.Encodable] [L₂.LORDefinable] where
  term : {n : Nat} → SyntacticSemiterm L₁ n → Bootstrapping.Semiterm V L₂ n
  formula : Nat → {n : Nat} → Semiproposition L₁ n → Bootstrapping.Semiformula V L₂ n
  neg : ∀ b {n} (p : Semiproposition L₁ n), formula b (∼p) = ∼formula b p
  and : ∀ b {n} (p q : Semiproposition L₁ n), formula b (p ⋏ q) = formula b p ⋏ formula b q
  or : ∀ b {n} (p q : Semiproposition L₁ n), formula b (p ⋎ q) = formula b p ⋎ formula b q
  verum : ∀ b {n}, formula b (⊤ : Semiproposition L₁ n) = ⊤
  all : ∀ b {n} (p : Semiproposition L₁ (n+1)), formula b (∀⁰ p) = ∀⁰ formula b p
  exs : ∀ b {n} (p : Semiproposition L₁ (n+1)), formula b (∃⁰ p) = ∃⁰ formula b p
  shift : ∀ b {n} (p : Semiproposition L₁ n),
    formula (b+1) (Rewriting.shift p) = (formula b p).shift
  free : ∀ b (p : Semiproposition L₁ 1),
    formula (b+1) (Rewriting.free p) = (formula b p).free
  subst₁ : ∀ b (p : Semiproposition L₁ 1) (t : SyntacticTerm L₁),
    formula b (p/[t]) = (formula b p).subst ![term t]

namespace BufferedTranslation
variable (tr : BufferedTranslation V L₁ L₂)

lemma sequent_shift (b : Nat) (Γ : Finset (Proposition L₁)) :
    translateSequent (tr.formula (b+1)) (Γ.image Rewriting.shift) =
      (translateSequent (tr.formula b) Γ).shift := by
  apply Bootstrapping.Sequent.ext'
  apply mem_ext
  intro q
  rw [mem_translateSequent_iff]
  constructor
  · rintro ⟨p,hp,rfl⟩
    rcases Finset.mem_image.mp hp with ⟨r,hr,rfl⟩
    rw [tr.shift]
    exact Bootstrapping.mem_setShift_iff.mpr
      ⟨(tr.formula b r).val,formula_mem_translateSequent _ hr,rfl⟩
  · intro hq
    rcases Bootstrapping.mem_setShift_iff.mp hq with ⟨r,hr,hqr⟩
    rcases (mem_translateSequent_iff (f := tr.formula b)).mp hr with ⟨p,hp,rfl⟩
    refine ⟨Rewriting.shift p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
    rw [tr.shift]
    exact hqr.symm

omit [L₁.DecidableEq] in
lemma closed_buffer (p : Proposition L₁) (hp : Rewriting.shift p = p) (b : Nat) :
    tr.formula b p = shiftN b (tr.formula 0 p) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show tr.formula (b+1) p = (tr.formula b p).shift from by
        simpa only [hp] using tr.shift b p,ih]
      rfl
end BufferedTranslation

/-- External recursion over the fixed ordinary proof tree. -/
def bufferBound {T : Theory L₁} {Γ : Finset (Proposition L₁)} : T ⟹₂ Γ → Nat
  | .closed _ _ _ _ => 0
  | .axm _ _ _ => 0
  | .verum _ => 0
  | .and _ d e => max (bufferBound d) (bufferBound e)
  | .or _ d => bufferBound d
  | .all _ d => bufferBound d
  | .exs _ _ d => bufferBound d
  | .wk d _ => bufferBound d
  | .shift d => bufferBound d + 1
  | .cut d e => max (bufferBound d) (bufferBound e)

variable {T₁ : Theory L₁} {T₂ : InternalTheory V L₂}
variable (tr : BufferedTranslation V L₁ L₂)
variable (axiomProof : ∀ b (σ : Sentence L₁), σ ∈ T₁ →
  T₂ ⊢! tr.formula b (Rewriting.emb σ))

/-- The premise is computed from the fixed source proof, never from an internal
formula or an internal proof code. Every branch returns an actual proof code. -/
noncomputable def compileDerivation {Γ : Finset (Proposition L₁)}
    (d : T₁ ⟹₂ Γ) (b : Nat) (hb : bufferBound d ≤ b) :
    T₂ ⊢!ᵈᵉʳ translateSequent (tr.formula b) Γ := by
  induction d generalizing b with
  | closed Δ p hp hn =>
      exact TDerivation.em (tr.formula b p)
        (formula_mem_translateSequent _ hp)
        (by rw [←tr.neg]; exact formula_mem_translateSequent _ hn)
  | axm σ hT hΓ =>
      apply TDerivation.wk (axiomProof b σ hT).toTDerivation
      intro q hq
      have hq' : q = (tr.formula b (Rewriting.emb σ)).val := by
        simpa [Bootstrapping.Sequent.val_insert,Bootstrapping.Sequent.val_empty] using hq
      subst q
      exact formula_mem_translateSequent _ hΓ
  | verum h =>
      exact TDerivation.verum (by rw [←tr.verum b]; exact formula_mem_translateSequent _ h)
  | and h dp dq ihp ihq =>
      exact TDerivation.and'
        (by rw [←tr.and]; exact formula_mem_translateSequent _ h)
        ((ihp b (Nat.le_trans (Nat.le_max_left _ _) hb)).cast
          (by rw [translateSequent_insert]))
        ((ihq b (Nat.le_trans (Nat.le_max_right _ _) hb)).cast
          (by rw [translateSequent_insert]))
  | or h d ih =>
      exact TDerivation.or'
        (by rw [←tr.or]; exact formula_mem_translateSequent _ h)
        ((ih b hb).cast
          (by rw [translateSequent_insert,translateSequent_insert]))
  | all h d ih =>
      exact TDerivation.all'
        (by rw [←tr.all]; exact formula_mem_translateSequent _ h)
        ((ih (b+1) (Nat.le_trans hb (Nat.le_succ b))).cast
          (by rw [translateSequent_insert,tr.free,tr.sequent_shift]))
  | exs h t d ih =>
      exact TDerivation.exs'
        (by rw [←tr.exs]; exact formula_mem_translateSequent _ h) (tr.term t)
        ((ih b hb).cast
          (by rw [translateSequent_insert,tr.subst₁]))
  | wk d h ih =>
      exact TDerivation.wk (ih b hb)
        (translateSequent_mono _ h)
  | shift d ih =>
      cases b with
      | zero => simp only [bufferBound,Nat.add_one_le_iff,Nat.not_lt_zero] at hb
      | succ b =>
          exact (TDerivation.shift (ih b
            (Nat.le_of_succ_le_succ hb))).cast (tr.sequent_shift b _).symm
  | cut dp dq ihp ihq =>
      exact TDerivation.cut
        ((ihp b (Nat.le_trans (Nat.le_max_left _ _) hb)).cast
          (by rw [translateSequent_insert]))
        ((ihq b (Nat.le_trans (Nat.le_max_right _ _) hb)).cast
          (by rw [translateSequent_insert,tr.neg]))

/-- Cancel the external buffer at a closed source conclusion. The target
conclusion can still contain arbitrary internal free parameters. -/
noncomputable def compileProof {σ : Sentence L₁} (d : T₁ ⊢! σ) :
    T₂ ⊢! tr.formula 0 (Rewriting.emb σ) := by
  let d₂ : T₁ ⊢!₂! (Rewriting.emb σ : Proposition L₁) := d.toProof2
  let b := bufferBound d₂
  have h : T₂ ⊢! tr.formula b (Rewriting.emb σ) := by
    apply (compileDerivation tr axiomProof d₂ b (Nat.le_refl b)).cast
    simpa only [Bootstrapping.Sequent.insert_empty_eq_singleton] using
      translateSequent_singleton (tr.formula b) (Rewriting.emb σ)
  rw [tr.closed_buffer (Rewriting.emb σ) (by simp)] at h
  exact cancelShiftN T₂ _ b h

lemma compileProof_isProof {σ : Sentence L₁} (d : T₁ ⊢! σ) :
    Proof T₂.theory (compileProof tr axiomProof d).val
      (tr.formula 0 (Rewriting.emb σ)).val := by
  simpa [Proof] using (compileProof tr axiomProof d).derivationOf

end LeanProofs.ZFCinPA.BufferedTemplateProofCompiler

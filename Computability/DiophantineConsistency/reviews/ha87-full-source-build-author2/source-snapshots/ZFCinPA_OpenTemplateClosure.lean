import ZFCinPA.OpenSetTemplateCompiler

set_option autoImplicit false

/-!
Close the ordinary source parameters of a proof template while retaining every
free parameter of its arbitrary internal predicate interpretations. The number
of source parameters is externally finite; internal formula codes need not be.
-/
namespace LeanProofs.ZFCinPA.OpenTemplateClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def shifts {n : Nat} : Nat → Semiformula V L n → Semiformula V L n
  | 0,p => p
  | b+1,p => (shifts b p).shift

lemma shifts_all {n : Nat} (p : Semiformula V L (n+1)) (b : Nat) :
    shifts b (∀⁰ p) = ∀⁰ shifts b p := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [shifts,ih,Semiformula.shift_all]

noncomputable def freshTuple (n : Nat) : SemitermVec V L n 0 :=
  fun i => Semiterm.fvar (i.val : V)

/-- Generalize finitely many coordinates after shifting all pre-existing free
parameters above them. This does not require a closed internal formula. -/
noncomputable def generalizeAll (T : InternalTheory V L)
    {n : Nat} (p : Semiformula V L n)
    (h : T ⊢! (shifts n p).subst (freshTuple n)) : T ⊢! ∀⁰* p := by
  induction n with
  | zero => simpa only [shifts,Semiformula.subst_nil_eq_self,allClosure_zero] using h
  | succ n ih =>
      rw [allClosure_succ]
      apply ih (∀⁰ p)
      rw [shifts_all,Semiformula.substs_all]
      apply TProof.all
      have hv :
          (fun i => (((freshTuple (V := V) (L := L) n).q i).shift).subst
            ![Semiterm.fvar (0 : V)]) = freshTuple (n+1) := by
        funext i
        cases i using Fin.cases with
        | zero => simp [freshTuple,SemitermVec.q]
        | succ j => simp [freshTuple,SemitermVec.q,Nat.cast_add,Nat.cast_one]
      rw [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs]
      change T ⊢! (shifts n p).shift.subst
        (fun i => (((freshTuple n).q i).shift).subst ![Semiterm.fvar (0 : V)])
      rw [hv]
      exact h

variable {k : Nat} {arities : Fin k → Nat}

lemma translate_closed_shifts
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (arities i))
    {n : Nat} (p : Semiproposition (setTemplateLanguage k arities) n)
    (hp : p.freeVariables = ∅) (b : Nat) :
    shifts b (translateFormula Ks p) =
      translateFormula (shiftedPredicates Ks b) p := by
  have hs : Rewriting.shift p = p := by
    apply FirstOrder.Semiformula.rew_eq_self_of
    · simp
    · intro x hx
      simp [FirstOrder.Semiformula.FVar?,hp] at hx
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [shifts,ih,←translate_shift_family,hs]
      rfl

def sourceClosure (p : Proposition (setTemplateLanguage k arities)) :
    Semiproposition (setTemplateLanguage k arities) (0+p.fvSup) :=
  Rew.fixitr 0 p.fvSup ▹ p

lemma sourceClosure_closed (p : Proposition (setTemplateLanguage k arities)) :
    (sourceClosure p).freeVariables = ∅ := by
  simpa only [FirstOrder.Semiformula.univCl',sourceClosure,
    FirstOrder.Semiformula.freeVariables_allClosure] using
    FirstOrder.Semiformula.fvarList_univCl' p

lemma translate_allClosure
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (arities i))
    {n : Nat} (p : Semiproposition (setTemplateLanguage k arities) n) :
    translateFormula Ks (∀⁰* p) = ∀⁰* translateFormula Ks p := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (∀⁰ p)

lemma translate_univCl
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (arities i))
    (p : Proposition (setTemplateLanguage k arities)) :
    translateFormula Ks (Rewriting.emb p.univCl) =
      ∀⁰* translateFormula Ks (sourceClosure p) := by
  rw [FirstOrder.Semiformula.coe_univCl_eq_univCl',
    FirstOrder.Semiformula.univCl',translate_allClosure]
  rfl

lemma closure_opening
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (arities i))
    (p : Proposition (setTemplateLanguage k arities)) :
    (shifts (0+p.fvSup) (translateFormula Ks (sourceClosure p))).subst
        (freshTuple (0+p.fvSup)) = translateFormula (shiftedPredicates Ks (0+p.fvSup)) p := by
  rw [translate_closed_shifts Ks (sourceClosure p) (sourceClosure_closed p)]
  have ht : freshTuple (V := V) (L := ℒₛₑₜ) (0+p.fvSup) =
      fun i => translateTerm (&i.val : SyntacticTerm (setTemplateLanguage k arities)) := rfl
  rw [ht,←translateFormula_subst]
  simp only [sourceClosure,FirstOrder.Semiformula.subst_comp_fixitr]

/-- An open source proof available at every shifted predicate family gives the
translation of its ordinary universal closure. Extra internal parameters stay
free; only the source formula's finite free-variable range is generalized. -/
noncomputable def closeTemplate
    (Ks : (i : Fin k) → Semiformula V ℒₛₑₜ (arities i))
    (T : InternalTheory V ℒₛₑₜ)
    (p : Proposition (setTemplateLanguage k arities))
    (h : ∀ b, T ⊢! translateFormula (shiftedPredicates Ks b) p) :
    T ⊢! translateFormula Ks (Rewriting.emb p.univCl) := by
  have hp : T ⊢! (shifts (0+p.fvSup) (translateFormula Ks (sourceClosure p))).subst
      (freshTuple (0+p.fvSup)) := by
    rw [closure_opening]
    exact h (0+p.fvSup)
  have hc := generalizeAll T (translateFormula Ks (sourceClosure p)) hp
  simpa only [translate_univCl] using hc

end LeanProofs.ZFCinPA.OpenTemplateClosure

import IPRABridge.Syntax

/-! The Foundation syntax obtained by a round trip through ConciseIPRA. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency.IPRAEqualityOnlyReference

variable {ξ ζ : Type} {n m : ℕ}

/-- Change only the primitive-recursive function symbols. -/
private def normalization : language →ᵥ language where
  func := normalizeCode
  rel := id

def normalizeTerm (t : Semiterm language ξ n) : Semiterm language ξ n :=
  Semiterm.lMap normalization t

def normalizeFormula : {n : ℕ} → Semiformulaᵢ language ξ n → Semiformulaᵢ language ξ n
  | _, .falsum => .falsum
  | _, .rel r ts => .rel r (fun i => normalizeTerm (ts i))
  | _, .and φ ψ => .and (normalizeFormula φ) (normalizeFormula ψ)
  | _, .or φ ψ => .or (normalizeFormula φ) (normalizeFormula ψ)
  | _, .imp φ ψ => .imp (normalizeFormula φ) (normalizeFormula ψ)
  | _, .all φ => .all (normalizeFormula φ)
  | _, .exs φ => .exs (normalizeFormula φ)

def normalizeRew (r : Rew language ξ n ζ m) : Rew language ξ n ζ m :=
  Rew.bind (fun i => normalizeTerm (r (.bvar i))) (fun x => normalizeTerm (r (.fvar x)))

theorem normalizeTerm_rew (r : Rew language ξ n ζ m) (t : Semiterm language ξ n) :
    normalizeTerm (r t) = normalizeRew r (normalizeTerm t) := by
  induction t with
  | bvar | fvar => rfl
  | func c ts ih =>
    simp only [normalizeTerm, Rew.func', Semiterm.lMap_func]
    congr 1
    exact funext ih

private theorem normalizeRew_q (r : Rew language ξ n ζ m) :
    normalizeRew r.q = (normalizeRew r).q := by
  ext x
  · refine Fin.cases rfl (fun i => ?_) x
    simp [normalizeRew, normalizeTerm, Rew.q, Semiterm.lMap_bShift, Function.comp_def]
  · simp [normalizeRew, normalizeTerm, Rew.q, Semiterm.lMap_bShift, Function.comp_def]

theorem normalizeFormula_rew (r : Rew language ξ n ζ m) (φ : Semiformulaᵢ language ξ n) :
    normalizeFormula (r ▹ φ) = normalizeRew r ▹ normalizeFormula φ := by
  change normalizeFormula (Semiformulaᵢ.rewAux r φ) =
    Semiformulaᵢ.rewAux (normalizeRew r) (normalizeFormula φ)
  induction φ using Semiformulaᵢ.rec' generalizing m <;>
    simp [normalizeFormula, Semiformulaᵢ.rewAux, ← normalizeRew_q, normalizeTerm_rew, *]
  all_goals rfl

@[simp] theorem normalizeFormula_free (φ : Semipropositionᵢ language (n + 1)) :
    normalizeFormula (Rewriting.free φ) = Rewriting.free (normalizeFormula φ) := by
  have hr : normalizeRew (Rew.free : Rew language ℕ (n + 1) ℕ n) = Rew.free := by
    ext x
    · refine Fin.lastCases ?_ (fun i => ?_) x <;> simp [normalizeRew, normalizeTerm]
    · simp [normalizeRew, normalizeTerm]
  simpa only [Rewriting.free, hr] using
    normalizeFormula_rew (Rew.free : Rew language ℕ (n + 1) ℕ n) φ

@[simp] theorem normalizeFormula_emb (φ : Semisentenceᵢ language n) :
    normalizeFormula (Rewriting.emb (ξ := ξ) φ) =
      Rewriting.emb (ξ := ξ) (normalizeFormula φ) := by
  have hr : normalizeRew (Rew.emb : Rew language Empty n ξ n) = Rew.emb := by
    ext x
    · simp [normalizeRew, normalizeTerm]
    · exact Empty.elim x
  simpa only [Rewriting.emb, hr] using normalizeFormula_rew (Rew.emb : Rew language Empty n ξ n) φ

/-- The syntactic round trip at an arbitrary finite bound-variable scope. -/
theorem referenceTerm_roundtrip (t : TermN n) :
    toFoundationTerm (toConciseTerm PTm.var Empty.elim t) = normalizeTerm t := by
  induction t with
  | bvar => rfl
  | fvar x => exact Empty.elim x
  | func c ts ih =>
    simp only [toConciseTerm, toFoundationTerm, normalizeTerm, Semiterm.lMap_func,
      normalization, normalizeCode, Function.comp_def, ih]

theorem referenceFormula_roundtrip (φ : Semisentenceᵢ language n) :
    toFoundation (toConciseFormula PTm.var Empty.elim φ) = normalizeFormula φ := by
  have hfree : ∀ k : ℕ, (fun x : Empty => Syn.shift (Empty.elim x : PTm k)) =
      (Empty.elim : Empty → PTm (k + 1)) := fun _ => funext (fun x => Empty.elim x)
  have hbound : ∀ k : ℕ, Syn.up (PTm.var : Fin k → PTm k) = PTm.var :=
    fun _ => Syn.up_var
  induction φ using Semiformulaᵢ.rec'
  case hRel r ts =>
    cases r
    simp only [toConciseFormula, toFoundation, normalizeFormula, referenceTerm_roundtrip]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  all_goals simp only [toConciseFormula, toFoundation, normalizeFormula, *]

end IPRABridge

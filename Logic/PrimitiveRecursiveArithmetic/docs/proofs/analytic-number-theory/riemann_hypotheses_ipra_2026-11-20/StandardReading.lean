import ArithmeticReading
import Hypotheses
import ConciseIPRA.Semantics

/-! Interpret the exact submitted sentences in ProveIt's term-model semantics.
    There is no interpretation of complex analysis or choice of zeros here. -/
namespace RiemannIPRA
open LeanProofs.ConciseIPRA

def termValue {n : Nat} : PTm n → (Fin n → Nat) → Nat
  | .var i, e => e i
  | .app r terms, e => PacketLanguage.value r (fun i => termValue (terms i) e)

theorem term_subst {n m : Nat} (s : PTm n) (σ : Fin n → PTm m) (e : Fin m → Nat) :
    termValue (Syn.subst σ s) e = termValue s (fun i => termValue (σ i) e) := by
  induction s with
  | var i => rfl
  | app r ts ih =>
    simp only [PTm.subst_app, termValue, ih]

/-- The actual ProveIt model structure for the ordinary natural numbers. -/
def naturalTerms : TermModel PTm Nat where
  eval := termValue
  eval_var _ _ := rfl
  eval_subst σ s e := term_subst s σ e

/-- Assignment to the five parameters in their documented order. -/
def packetArgs (d H u v t : Nat) : Fin 5 → Nat :=
  Fin.cases d (Fin.cases H (Fin.cases u (Fin.cases v (fun _ => t))))

private theorem term_zero {n} (e : Fin n → Nat) : termValue PTm.zero e = 0 := rfl
private theorem term_one {n} (e : Fin n → Nat) : termValue (PTm.succ PTm.zero) e = 1 := rfl

private theorem holds_atom {n} (f : PR 5) (d H u v t : PTm n) (e : Fin n → Nat) :
    naturalTerms.Holds (RHHierarchy.atom f d H u v t) e ↔
      PacketLanguage.value f (packetArgs (termValue d e) (termValue H e)
        (termValue u e) (termValue v e) (termValue t e)) = 0 := by
  change (PacketLanguage.value f (fun i => termValue
    (Fin.cases d (Fin.cases H (Fin.cases u (Fin.cases v (fun _ => t)))) i) e) = 0) ↔ _
  have h : (fun i => termValue (Fin.cases d (Fin.cases H (Fin.cases u
      (Fin.cases v (fun _ => t)))) i) e) =
      packetArgs (termValue d e) (termValue H e) (termValue u e)
        (termValue v e) (termValue t e) := by
    funext i
    refine Fin.cases rfl (fun a => Fin.cases rfl (fun b => Fin.cases rfl
      (fun c => Fin.cases rfl (fun _ => rfl) c) b) a) i
  rw [h]

private theorem holds_all {n} (A : Fm PTm (n+1)) (e : Fin n → Nat) :
    naturalTerms.Holds (.all A) e ↔ ∀ x, naturalTerms.Holds A (Fin.cases x e) := Iff.rfl

theorem rh_reading : naturalTerms.Holds RH Fin.elim0 ↔
    ∀ t, PacketLanguage.value excess (packetArgs 0 0 0 1 t) = 0 := by
  simp only [RH, RHHierarchy.RHOf, holds_all, holds_atom, term_zero, term_one]
  rfl

theorem grh_reading : naturalTerms.Holds GRH Fin.elim0 ↔
    ∀ d t, PacketLanguage.value excess (packetArgs d 0 0 1 t) = 0 := by
  simp only [GRH, RHHierarchy.GRHOf, holds_all, holds_atom, term_zero, term_one]
  rfl

theorem erh_reading : naturalTerms.Holds ERH Fin.elim0 ↔
    ∀ d H u v t, PacketLanguage.value excess (packetArgs d H u v t) = 0 := by
  simp only [ERH, RHHierarchy.ERHOf, holds_all, holds_atom]
  rfl

private theorem term_cons {k n} (t : PTm n) (ts : Fin k → PTm n) (e : Fin n → Nat) :
    (fun i => termValue (Fin.cases t ts i) e) = Fin.cases (termValue t e) (fun i => termValue (ts i) e) := by
  funext i; exact Fin.cases rfl (fun _ => rfl) i

private theorem eval_inst {k} (val : PTm k) (e : Fin k → Nat) :
    (fun i => naturalTerms.eval (Syn.inst val i) e) = Fin.cases (termValue val e) e :=
  term_cons val _ e

private theorem eval_repl {k} (val : PTm (k+1)) (e : Fin (k+1) → Nat) :
    (fun i => naturalTerms.eval (Syn.repl val i) e) = Fin.cases (termValue val e) (fun i => e i.succ) :=
  term_cons val _ e

/-- The interpretation above validates every axiom, including quantifier-free induction. -/
theorem naturalTerms_valid {n : Nat} {A : Fm PTm n} (h : PRAAx n A) (e : Fin n → Nat) :
    naturalTerms.Holds A e := by
  cases h with
  | proj => rfl
  | comp => rfl
  | precZero f g =>
    simp only [TermModel.Holds, naturalTerms, termValue]
    rw [PacketLanguage.value]
    rfl
  | precSucc f g =>
    simp only [TermModel.Holds, naturalTerms, termValue]
    simp only [Syn.repl, term_cons]
    rw [PacketLanguage.value]
    simp only [Fin.cases_zero, Fin.cases_succ]
    congr 1
  | succNeZero => exact Nat.noConfusion
  | succInj => exact Nat.succ.inj
  | ind A _ =>
    intro base step y
    induction y with
    | zero =>
      rw [naturalTerms.holds_subst, eval_inst] at base
      exact base
    | succ y ih =>
      have next := (naturalTerms.holds_subst _ _ _).mp (step y ih)
      rw [eval_repl] at next
      exact next

/-- Soundness at the standard natural numbers for arbitrary finite contexts. -/
theorem naturalTerms_sound {n : Nat} {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (h : Prf PRAAx Γ A) (e : Fin n → Nat) (hΓ : ∀ B ∈ Γ, naturalTerms.Holds B e) :
    naturalTerms.Holds A e :=
  naturalTerms.sound naturalTerms_valid h e hΓ

end RiemannIPRA

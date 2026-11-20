import ConciseIPRA.PR

/-! Compilation of a fixed finite decision tree to an actual object-iPRA term.
    Each traced test supplies a derivation of its selected bit. -/
namespace Sparse.ObjectReplay
open LeanProofs.ConciseIPRA
open scoped Fm
open PTm (app zero succ)

private def branches (l r : PTm n) : Fin 2 → PTm n :=
  Fin.cases l (fun _ => r)

def switchFn : PR 3 := .prec (.proj 0 : PR 2) (.proj 3 : PR 4)

def switch (b l r : PTm n) : PTm n :=
  app switchFn (Fin.cases b (branches l r))

variable {n : Nat} {Γ : List (Fm PTm n)}

theorem switchZero (l r : PTm n) : Γ ⊢[PRAAx] switch zero l r ≐ l :=
  (PRA.precZero (.proj 0 : PR 2) (.proj 3 : PR 4) (branches l r)).eqTrans
    (PRA.proj 0 _)

theorem switchSucc (t l r : PTm n) : Γ ⊢[PRAAx] switch (succ t) l r ≐ r :=
  (PRA.precSucc (.proj 0 : PR 2) (.proj 3 : PR 4) t (branches l r)).eqTrans
    (PRA.proj 3 _)

theorem switchCongr {b c : PTm n} (l r : PTm n) (e : Γ ⊢[PRAAx] b ≐ c) :
    Γ ⊢[PRAAx] switch b l r ≐ switch c l r := by
  let s : Fin 3 → PTm n := Fin.cases b (branches l r)
  let t : Fin 3 → PTm n := Fin.cases c (branches l r)
  have eqs : ∀ i, Γ ⊢[PRAAx] s i ≐ t i := Fin.cases e (fun _ => .eqRefl _)
  exact Prf.eqCongr (app switchFn Syn.var) eqs

inductive Tree (n : Nat) where
  | leaf (value : PTm n)
  | ask (address : Nat) (left right : Tree n)

def compile (read : Nat → PTm n) : Tree n → PTm n
  | .leaf v => v
  | .ask q l r => switch (read q) (compile read l) (compile read r)

def selected (bits : Nat → Bool) : Tree n → PTm n
  | .leaf v => v
  | .ask q l r => if bits q then selected bits r else selected bits l

def path (bits : Nat → Bool) : Tree n → List Nat
  | .leaf _ => []
  | .ask q l r => q :: (if bits q then path bits r else path bits l)

def bitTerm : Bool → PTm n
  | false => zero
  | true => succ zero

theorem replay (read : Nat → PTm n) (bits : Nat → Bool) (t : Tree n)
    (h : ∀ q ∈ path bits t, Γ ⊢[PRAAx] read q ≐ bitTerm (bits q)) :
    Γ ⊢[PRAAx] compile read t ≐ selected bits t := by
  induction t with
  | leaf v => exact .eqRefl _
  | ask q l r il ir =>
    have head := h q (by simp [path])
    cases b : bits q with
    | false =>
      have e : Γ ⊢[PRAAx] read q ≐ zero := by simpa [b, bitTerm] using head
      simp only [selected, b, Bool.false_eq_true, ↓reduceIte, compile]
      exact (switchCongr _ _ e).eqTrans ((switchZero _ _).eqTrans
        (il (fun i hi => h i (by simp [path, b, hi]))))
    | true =>
      have e : Γ ⊢[PRAAx] read q ≐ succ zero := by simpa [b, bitTerm] using head
      simp only [selected, b, ↓reduceIte, compile]
      exact (switchCongr _ _ e).eqTrans ((switchSucc _ _ _).eqTrans
        (ir (fun i hi => h i (by simp [path, b, hi]))))

theorem replayTwo (read₁ read₂ : Nat → PTm n) (bits : Nat → Bool) (t : Tree n)
    (h₁ : ∀ q ∈ path bits t, Γ ⊢[PRAAx] read₁ q ≐ bitTerm (bits q))
    (h₂ : ∀ q ∈ path bits t, Γ ⊢[PRAAx] read₂ q ≐ bitTerm (bits q)) :
    Γ ⊢[PRAAx] compile read₁ t ≐ compile read₂ t :=
  (replay read₁ bits t h₁).eqTrans (replay read₂ bits t h₂).eqSymm

/-- One unconditional closed sentence, with a deliberately irrelevant branch. -/
theorem exampleClosed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      compile (fun _ => succ zero) (.ask 17 (.leaf zero) (.leaf (succ zero))) ≐ succ zero :=
  replay _ (fun _ => true) _ (fun _ _ => .eqRefl _)

#print axioms replayTwo
#print axioms exampleClosed
end Sparse.ObjectReplay

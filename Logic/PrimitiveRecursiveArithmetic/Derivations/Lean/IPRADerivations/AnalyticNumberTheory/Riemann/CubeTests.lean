import IPRADerivations.AnalyticNumberTheory.Riemann.ObjectForms

/-! Imported from the packet `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`,
`CubeTests.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Synchronized finite boxes for an arbitrary universal closure of a zero test.
All conclusions use the repository's first-order derivability predicate. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.CubeTests
open LeanProofs.ConciseIPRA Syn
open scoped Fm
open PTm (app zero succ)
variable {k n m : Nat} {Γ : List (Fm PTm n)}

private theorem congrApp (f : PR k) {s t : Fin k → PTm n}
    (p : ∀ i, Prf PRAAx Γ (s i ≐ t i)) : Prf PRAAx Γ (app f s ≐ app f t) := by
  simpa using Prf.eqCongr (app f (var : Fin k → PTm k)) p

private def cons {α} {q : Nat} (a : α) (s : Fin q → α) : Fin (q+1) → α := Fin.cases a s

private def reindex (f : PR k) (p : Fin k → Fin m) : PR m := .comp f (fun i => .proj (p i))

private theorem reindexAt (f : PR k) (p : Fin k → Fin m) (s : Fin m → PTm n) :
    Prf PRAAx Γ (app (reindex f p) s ≐ app f (fun i => s (p i))) :=
  Prf.eqTrans (PRA.comp _ _ _) (congrApp _ fun i => PRA.proj (p i) s)

private def plus (s t : PTm n) := app PacketLanguage.addR (cons s fun _ => t)

@[simp] private theorem subPlus (σ : Fin n → PTm m) (s t : PTm n) :
    subst σ (plus s t) = plus (subst σ s) (subst σ t) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl fun _ => rfl)

private theorem add0 (a : PTm n) : Prf PRAAx Γ (plus zero a ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ _) (PRA.proj 0 _)

private theorem addS (a b : PTm n) : Prf PRAAx Γ (plus (succ a) b ≐ succ (plus a b)) :=
  Prf.eqTrans (PRA.precSucc _ _ _ _) (reindexAt .succ (fun _ : Fin 1 => (1 : Fin 3)) _)

private theorem liftSucc {s t : PTm n} (h : Prf PRAAx Γ (s ≐ t)) :
    Prf PRAAx Γ (succ s ≐ succ t) := congrApp .succ fun _ => h

private theorem leftAdd (s : PTm n) {a b : PTm n} (h : Prf PRAAx Γ (a ≐ b)) :
    Prf PRAAx Γ (plus s a ≐ plus s b) := congrApp _ (Fin.cases (Prf.eqRefl s) fun _ => h)

private theorem rightAdd (s : PTm n) {a b : PTm n} (h : Prf PRAAx Γ (a ≐ b)) :
    Prf PRAAx Γ (plus a s ≐ plus b s) := congrApp _ (Fin.cases h fun _ => Prf.eqRefl s)

@[simp] private theorem replShift (s : PTm (n+1)) (t : PTm n) :
    subst (repl s) (Syn.shift t) = Syn.shift t := by rw [Syn.subst_shift]; rfl

private theorem addAssoc (a b c : PTm n) :
    Prf PRAAx Γ (plus a (plus b c) ≐ plus (plus a b) c) := by
  let B := Syn.shift b
  let C := Syn.shift c
  let P := plus (var 0) (plus B C) ≐ plus (plus (var 0) B) C
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simp only [P,B,C,Fm.subst_eq,subPlus,subst_var,inst_zero,subst_inst_shift]
      exact Prf.eqTrans (add0 _) (Prf.eqSymm (rightAdd _ (add0 _)))
    · simp only [P,B,C,Fm.subst_eq,subPlus,subst_var,repl_zero,replShift]
      exact Prf.eqTrans (addS _ _) (Prf.eqTrans (liftSucc (Prf.hyp0 (φ := P)))
        (Prf.eqSymm (Prf.eqTrans (rightAdd _ (addS _ _)) (addS _ _))))
  simpa [P,B,C] using Prf.allE a h

private theorem addRight0 (a : PTm n) : Prf PRAAx Γ (plus a zero ≐ a) := by
  let P : Fm PTm (n+1) := plus (var 0) zero ≐ var 0
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simpa [P] using add0 (Γ := Γ) (zero : PTm n)
    · simp only [P,Fm.subst_eq,subPlus,subst_var,repl_zero,PTm.subst_zero]
      exact Prf.eqTrans (addS _ _) (liftSucc (Prf.hyp0 (φ := P)))
  simpa [P] using Prf.allE a h

private theorem addRightS (a b : PTm n) : Prf PRAAx Γ (plus a (succ b) ≐ succ (plus a b)) := by
  let B := Syn.shift b
  let P := plus (var 0) (succ B) ≐ succ (plus (var 0) B)
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simp only [P,B,Fm.subst_eq,subPlus,subst_var,PTm.subst_succ,inst_zero,subst_inst_shift]
      exact Prf.eqTrans (add0 _) (Prf.eqSymm (liftSucc (add0 _)))
    · simp only [P,B,Fm.subst_eq,subPlus,subst_var,PTm.subst_succ,repl_zero,replShift]
      exact Prf.eqTrans (addS _ _) (Prf.eqTrans (liftSucc (Prf.hyp0 (φ := P)))
        (Prf.eqSymm (liftSucc (addS _ _))))
  simpa [P,B] using Prf.allE a h

private theorem addComm (a b : PTm n) : Prf PRAAx Γ (plus a b ≐ plus b a) := by
  let B := Syn.shift b
  let P := plus (var 0) B ≐ plus B (var 0)
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simp only [P,B,Fm.subst_eq,subPlus,subst_var,inst_zero,subst_inst_shift]
      exact Prf.eqTrans (add0 _) (Prf.eqSymm (addRight0 _))
    · simp only [P,B,Fm.subst_eq,subPlus,subst_var,repl_zero,replShift]
      exact Prf.eqTrans (addS _ _) (Prf.eqTrans (liftSucc (Prf.hyp0 (φ := P)))
        (Prf.eqSymm (addRightS _ _)))
  simpa [P,B] using Prf.allE a h

/-- Return the old accumulator if the current sample is zero, and one otherwise. -/
private def latch : PR 2 := .prec (.proj 0) (PacketLanguage.numeral 1)
private def join (x a : PTm n) := app latch (cons x fun _ => a)

@[simp] private theorem subJoin (σ : Fin n → PTm m) (s t : PTm n) :
    subst σ (join s t) = join (subst σ s) (subst σ t) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl fun _ => rfl)

private theorem zeroCode (s : Fin k → PTm n) : Prf PRAAx Γ (app PacketLanguage.zeroR s ≐ zero) :=
  Prf.eqTrans (PRA.comp _ _ _) (congrApp _ fun i => i.elim0)

private theorem join0 (a : PTm n) : Prf PRAAx Γ (join zero a ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ _) (PRA.proj 0 _)

private theorem joinS (x a : PTm n) : Prf PRAAx Γ (join (succ x) a ≐ succ zero) :=
  Prf.eqTrans (PRA.precSucc _ _ _ _) (Prf.eqTrans (PRA.comp _ _ _) (liftSucc (zeroCode _)))

private theorem joinSpec (x a : PTm n) :
    Prf PRAAx Γ (Fm.iff (join x a ≐ zero) ((x ≐ zero) ⋏ (a ≐ zero))) := by
  let A := Syn.shift a
  let P := Fm.iff (join (var 0) A ≐ zero) (((var 0) ≐ zero) ⋏ (A ≐ zero))
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨⟨trivial,trivial,trivial⟩,⟨⟨trivial,trivial⟩,trivial⟩⟩
    · simp only [P,A,Fm.iff,Fm.subst_imp,Fm.subst_and,Fm.subst_eq,subJoin,
        subst_var,PTm.subst_zero,inst_zero,subst_inst_shift]
      exact Prf.iffI (Prf.impI (Prf.andI (Prf.eqRefl _)
        (Prf.eqTrans (Prf.eqSymm (join0 _)) Prf.hyp0)))
        (Prf.impI (Prf.eqTrans (join0 _) (Prf.andE₂ Prf.hyp0)))
    · simp only [P,A,Fm.iff,Fm.subst_imp,Fm.subst_and,Fm.subst_eq,subJoin,
        subst_var,PTm.subst_zero,repl_zero,replShift]
      exact Prf.iffI (Prf.impI (Prf.botE _ (Prf.impE (PRA.succNeZero _)
        (Prf.eqTrans (Prf.eqSymm (joinS _ _)) Prf.hyp0))))
        (Prf.impI (Prf.botE _ (Prf.impE (PRA.succNeZero _) (Prf.andE₁ Prf.hyp0))))
  simpa [P,A,Fm.iff] using Prf.allE x h

private def applyAt (f : PR (k+1)) (x : PTm n) (s : Fin k → PTm n) := app f (cons x s)

@[simp] private theorem subAt (σ : Fin n → PTm m) (f : PR (k+1)) (x : PTm n)
    (s : Fin k → PTm n) :
    subst σ (applyAt f x s) = applyAt f (subst σ x) (fun i => subst σ (s i)) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl fun _ => rfl)

private def scan (f : PR (k+1)) : PR (k+1) := .prec PacketLanguage.zeroR
  (.comp latch (cons (reindex f (cons 0 fun i => i.succ.succ)) fun _ => .proj 1))

private theorem scan0 (f : PR (k+1)) (s : Fin k → PTm n) :
    Prf PRAAx Γ (applyAt (scan f) zero s ≐ zero) :=
  Prf.eqTrans (PRA.precZero _ _ s) (zeroCode s)

private theorem scanS (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n) :
    Prf PRAAx Γ (applyAt (scan f) (succ x) s ≐ join (applyAt f x s) (applyAt (scan f) x s)) := by
  let args := cons x (cons (applyAt (scan f) x s) s)
  apply Prf.eqTrans (PRA.precSucc _ _ _ s)
  apply Prf.eqTrans (PRA.comp _ _ args)
  apply congrApp latch
  refine Fin.cases ?_ (fun _ => ?_)
  · apply Prf.eqTrans (reindexAt f _ args)
    exact congrApp _ (Fin.cases (Prf.eqRefl _) fun _ => Prf.eqRefl _)
  · exact PRA.proj 1 args

private theorem scanStep (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n) :
    Prf PRAAx Γ (Fm.iff (applyAt (scan f) (succ x) s ≐ zero)
        ((applyAt f x s ≐ zero) ⋏ (applyAt (scan f) x s ≐ zero))) := by
  exact Prf.iffI (Prf.impI (Prf.iffMp (joinSpec _ _)
    (Prf.eqTrans (Prf.eqSymm (scanS f s x)) Prf.hyp0)))
    (Prf.impI (Prf.eqTrans (scanS f s x) (Prf.iffMpr (joinSpec _ _) Prf.hyp0)))

private theorem scanClean (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n)
    (good : Prf PRAAx (Γ.map Fm.shift) (applyAt f (var 0) (fun i => Syn.shift (s i)) ≐ zero)) :
    Prf PRAAx Γ (applyAt (scan f) x s ≐ zero) := by
  let P := applyAt (scan f) (var 0) (fun i => Syn.shift (s i)) ≐ zero
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simpa [P] using scan0 (Γ := Γ) f s
    · simp only [P,Fm.subst_eq,subAt,subst_var,PTm.subst_zero,repl_zero,replShift]
      exact Prf.iffMpr (scanStep _ _ _) (Prf.andI good.wk Prf.hyp0)
  simpa [P] using Prf.allE x h

private theorem headEq (f : PR (k+1)) (s : Fin k → PTm n) {x y : PTm n}
    (h : Prf PRAAx Γ (x ≐ y)) : Prf PRAAx Γ (applyAt f x s ≐ applyAt f y s) :=
  congrApp _ (Fin.cases h fun _ => Prf.eqRefl _)

private theorem scanRead (f : PR (k+1)) (s : Fin k → PTm n) (x d : PTm n) :
    Prf PRAAx Γ ((applyAt (scan f) (plus d (succ x)) s ≐ zero) ⟶ (applyAt f x s ≐ zero)) := by
  let X := Syn.shift x
  let S := fun i => Syn.shift (s i)
  let P := (applyAt (scan f) (plus (var 0) (succ X)) S ≐ zero) ⟶ (applyAt f X S ≐ zero)
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P ⟨trivial,trivial⟩
    · simp only [P,X,S,Fm.subst_imp,Fm.subst_eq,subAt,subPlus,subst_var,inst_zero,
        PTm.subst_succ,PTm.subst_zero,subst_inst_shift]
      apply Prf.impI
      exact Prf.andE₁ (Prf.iffMp (scanStep f s x)
        (Prf.eqTrans (Prf.eqSymm (headEq (scan f) s (add0 _))) Prf.hyp0))
    · simp only [P,X,S,Fm.subst_imp,Fm.subst_eq,subAt,subPlus,subst_var,repl_zero,
        PTm.subst_succ,PTm.subst_zero,replShift]
      apply Prf.impI
      apply Prf.impE Prf.hyp1
      exact Prf.andE₂ (Prf.iffMp (scanStep _ _ _)
        (Prf.eqTrans (Prf.eqSymm (headEq (scan f) S (addS _ _))) Prf.hyp0))
  simpa [P,X,S] using Prf.allE d h

/-- A universally quantified block of arbitrary length ending in a zero-test.
Free arithmetic parameters are allowed. -/
inductive Block : Nat → Type
  | test {n : Nat} (t : PTm n) : Block n
  | bind {n : Nat} (b : Block (n+1)) : Block n

def Block.form : {q : Nat} → Block q → Fm PTm q
  | _, .test t => t ≐ zero
  | _, .bind b => .all b.form

private def compileTerm : PTm k → PR k
  | .var i => .proj i
  | .app f ts => .comp f (fun i => compileTerm (ts i))

private theorem termAt (t : PTm k) (s : Fin k → PTm n) :
    Prf PRAAx Γ (app (compileTerm t) s ≐ subst s t) := by
  induction t with
  | var i => exact PRA.proj i s
  | app f ts ih => exact Prf.eqTrans (PRA.comp _ _ _) (congrApp _ ih)

private def swapHead {q : Nat} : Fin (q+2) → Fin (q+2) :=
  cons 1 (cons 0 fun i => i.succ.succ)

private def duplHead {q : Nat} : Fin (q+2) → Fin (q+1) := cons 0 id

/-- The head argument is the common, exclusive cutoff in every dimension.
Remaining arguments supply any free parameters of the block. -/
def Block.cube : {q : Nat} → Block q → PR (q+1)
  | _, .test t => reindex (compileTerm t) Fin.succ
  | _, .bind b => reindex (scan (reindex b.cube swapHead)) duplHead

private def valueAt (b : Block k) (N : PTm n) (s : Fin k → PTm n) :=
  applyAt b.cube N s

private theorem leafEq (t : PTm k) (N : PTm n) (s : Fin k → PTm n) :
    Prf PRAAx Γ (valueAt (.test t) N s ≐ subst s t) := by
  apply Prf.eqTrans (reindexAt _ _ _)
  apply Prf.eqTrans _ (termAt t s)
  exact congrApp _ (fun _ => Prf.eqRefl _)

private theorem bindEq (b : Block (k+1)) (N : PTm n) (s : Fin k → PTm n) :
    Prf PRAAx Γ (valueAt (.bind b) N s ≐ applyAt (scan (reindex b.cube swapHead)) N (cons N s)) := by
  apply Prf.eqTrans (reindexAt _ _ _)
  exact congrApp _ (Fin.cases (Prf.eqRefl _) fun _ => Prf.eqRefl _)

private theorem swapEq (b : Block (k+1)) (x N : PTm n) (s : Fin k → PTm n) :
    Prf PRAAx Γ (applyAt (reindex b.cube swapHead) x (cons N s) ≐ valueAt b N (cons x s)) := by
  apply Prf.eqTrans (reindexAt _ _ _)
  exact congrApp _ (Fin.cases (Prf.eqRefl _) fun i => Fin.cases (Prf.eqRefl _)
    (fun _ => Prf.eqRefl _) i)

private theorem under (σ : Fin k → PTm n) : up σ = cons (var 0) (fun i => Syn.shift (σ i)) := rfl

/-- An arbitrary satisfactory tuple implies the vanishing of every finite box
when generalized over all the coordinates. -/
private theorem testBox (b : Block k) (N : PTm n) (s : Fin k → PTm n)
    (h : Prf PRAAx Γ (b.form.subst s)) : Prf PRAAx Γ (valueAt b N s ≐ zero) := by
  induction b generalizing n with
  | test t =>
    exact Prf.eqTrans (leafEq t N s) (by simpa [Block.form] using h)
  | bind b ih =>
    apply Prf.eqTrans (bindEq b N s)
    apply scanClean
    have good := Prf.allOpen h
    have smaller := ih (Syn.shift N) (up s) good
    have toChild := swapEq (Γ := Γ.map Fm.shift) b (var 0) (Syn.shift N) (fun i => Syn.shift (s i))
    rw [under] at smaller
    have e : (fun i => Syn.shift (cons N s i)) = cons (Syn.shift N) (fun i => Syn.shift (s i)) := by
      exact funext (Fin.cases rfl fun _ => rfl)
    rw [e]
    exact Prf.eqTrans toChild smaller

private def Row : {q : Nat} → Block q → Nat → Type
  | _, .test _, _ => PUnit
  | _, .bind b, m => PTm m × Row b m

private def cell : {q : Nat} → (b : Block q) → (Fin q → PTm n) → Row b n → PTm n
  | _, .test t, s, _ => subst s t
  | _, .bind b, s, row => cell b (cons row.1 s) row.2

private def horizon : {q : Nat} → (b : Block q) → Row b n → PTm n
  | _, .test _, _ => zero
  | _, .bind b, row => plus (succ row.1) (horizon b row.2)

private def Fits (Γ : List (Fm PTm n)) : {q : Nat} → (b : Block q) → Row b n → PTm n → Prop
  | _, .test _, _, _ => True
  | _, .bind b, row, N =>
    (∃ d : PTm n, Prf PRAAx Γ (N ≐ plus d (succ row.1))) ∧ Fits Γ b row.2 N

private theorem extend (b : Block k) (row : Row b n) (l N : PTm n) (h : Fits Γ b row N) :
    Fits Γ b row (plus l N) := by
  induction b with
  | test => trivial
  | bind b ih =>
    obtain ⟨x,xs⟩ := row
    obtain ⟨⟨d,hd⟩,tail⟩ := h
    exact ⟨⟨plus l d,Prf.eqTrans (leftAdd l hd) (addAssoc _ _ _)⟩,ih xs tail⟩

private theorem fitsHorizon (b : Block k) (row : Row b n) : Fits Γ b row (horizon b row) := by
  induction b with
  | test => trivial
  | bind b ih =>
    obtain ⟨x,xs⟩ := row
    exact ⟨⟨horizon b xs,addComm _ _⟩,extend b xs _ _ (ih xs)⟩

private theorem readBox (b : Block k) (N : PTm n) (s : Fin k → PTm n) (row : Row b n)
    (covers : Fits Γ b row N) (ok : Prf PRAAx Γ (valueAt b N s ≐ zero)) :
    Prf PRAAx Γ (cell b s row ≐ zero) := by
  induction b with
  | test t => exact Prf.eqTrans (Prf.eqSymm (leafEq _ _ _)) ok
  | bind b ih =>
    obtain ⟨x,xs⟩ := row
    obtain ⟨⟨d,hd⟩,tail⟩ := covers
    have clean := Prf.eqTrans (Prf.eqSymm (bindEq b N s)) ok
    have adjusted := Prf.eqTrans (Prf.eqSymm (headEq _ _ hd)) clean
    have there := Prf.impE (scanRead _ _ x d) adjusted
    exact ih (cons x s) xs tail (Prf.eqTrans (Prf.eqSymm (swapEq b x N s)) there)

/-- The meta-level argument describes how to fill every leaf of a finite
sequence of applications of the object-level universal introduction rule. -/
private theorem allCells (b : Block k) (s : Fin k → PTm n)
    (h : ∀ {m} (η : Fin n → PTm m) (row : Row b m),
      Prf PRAAx (Γ.map (fun A => A.subst η)) (cell b (fun i => subst η (s i)) row ≐ zero)) :
    Prf PRAAx Γ (b.form.subst s) := by
  induction b generalizing n with
  | test t =>
    simpa [cell,Block.form] using h var PUnit.unit
  | bind b ih =>
    apply Prf.allI
    apply ih
    intro m η row
    let tail := fun i => η (Fin.succ i)
    have v := h tail (η 0,row)
    have e : (fun i => subst η (up s i)) = cons (η 0) (fun i => subst tail (s i)) := by
      apply funext
      exact Fin.cases (by simp [cons]) (fun i => by simp [tail,cons,Syn.subst_shift])
    have ec : (Γ.map Fm.shift).map (fun A => A.subst η) = Γ.map (fun A => A.subst tail) := by
      simp [List.map_map, Function.comp_def, Fm.subst_shift, tail]
    rw [e,ec]
    exact v

/-- A single universal quantifier, even if the original test has many inputs. -/
def Block.diagonal (b : Block n) : Fm PTm n :=
  .all (valueAt b (var 0) (fun i => var i.succ) ≐ zero)

theorem diagonal_iff (b : Block n) : Prf PRAAx [] (Fm.iff b.form b.diagonal) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.allI
    exact testBox b (var 0) _ (Prf.hyp0 (φ := b.form.shift))
  · apply Prf.impI
    have h : Prf PRAAx [b.diagonal] (b.form.subst var) := by
      apply allCells
      intro m η row
      let N := horizon b row
      have d := (Prf.hyp0 (Ax := PRAAx) (φ := b.diagonal) (Γ := [])).subst η
      have clean := Prf.allE N d
      simp only [Block.diagonal,Fm.subst_eq,valueAt,subAt,PTm.subst_zero,subst_var,
        up_zero,inst_zero,up_succ,subst_inst_shift] at clean
      simpa only [Block.diagonal,valueAt,subst_var] using readBox b N η row (fitsHorizon b row) clean
    simpa using h

private def packet {q} (d H u v t : PTm q) : PTm q :=
  app RiemannIPRA.excess (cons d (cons H (cons u (cons v (fun _ => t)))))

def rhBlock : Block 0 := .bind (.test (packet zero zero zero (succ zero) (var 0)))
def grhBlock : Block 0 := .bind (.bind (.test (packet (var 1) zero zero (succ zero) (var 0))))
def erhBlock : Block 0 := .bind (.bind (.bind (.bind (.bind
  (.test (packet (var 4) (var 3) (var 2) (var 1) (var 0)))))))

theorem rh_cube : Prf PRAAx [] (Fm.iff RiemannIPRA.RH rhBlock.diagonal) := diagonal_iff rhBlock
theorem grh_cube : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH grhBlock.diagonal) := diagonal_iff grhBlock
theorem erh_cube : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH erhBlock.diagonal) := diagonal_iff erhBlock

/-- Any explicitly scheduled increase of a common horizon gives another unary test. -/
def Block.schedule (b : Block n) (lag : PR 1) : Fm PTm n :=
  .all (valueAt b (plus (app lag (fun _ => var 0)) (var 0)) (fun i => var i.succ) ≐ zero)

theorem schedule_iff (b : Block n) (lag : PR 1) : Prf PRAAx [] (Fm.iff b.form (b.schedule lag)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.allI
    exact testBox b _ _ (Prf.hyp0 (φ := b.form.shift))
  · apply Prf.impI
    have h : Prf PRAAx [b.schedule lag] (b.form.subst var) := by
      apply allCells
      intro m η row
      let N := horizon b row
      have d := (Prf.hyp0 (Ax := PRAAx) (φ := b.schedule lag) (Γ := [])).subst η
      have clean := Prf.allE N d
      simp only [Block.schedule,Fm.subst_eq,valueAt,subAt,subPlus, PTm.subst_app,
        PTm.subst_zero,subst_var,up_zero,inst_zero,up_succ,subst_inst_shift] at clean
      have cov := extend (Γ := [(b.schedule lag).subst η]) b row (app lag (fun _ => N)) N (fitsHorizon b row)
      simpa only [List.map_cons,List.map_nil,Block.schedule,valueAt,subst_var] using
        readBox b _ η row cov clean
    simpa using h

private abbrev neg (A : Fm PTm n) := RHCounterexamples.neg A

private def pickCode : PR 3 := .prec (.proj 0) (.proj 3)
private def pick (z a b : PTm n) := app pickCode (cons z (cons a fun _ => b))

@[simp] private theorem subPick (σ : Fin n → PTm m) (z a b : PTm n) :
    subst σ (pick z a b) = pick (subst σ z) (subst σ a) (subst σ b) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl fun i => Fin.cases rfl (fun _ => rfl) i)

private theorem pick0 (a b : PTm n) : Prf PRAAx Γ (pick zero a b ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ _) (PRA.proj 0 _)
private theorem pickS (z a b : PTm n) : Prf PRAAx Γ (pick (succ z) a b ≐ b) :=
  Prf.eqTrans (PRA.precSucc _ _ _ _) (PRA.proj 3 _)

private theorem pickPos (z a b : PTm n) :
    Prf PRAAx Γ (neg (z ≐ zero) ⟶ (pick z a b ≐ b)) := by
  let A := Syn.shift a
  let B := Syn.shift b
  let P := neg (var 0 ≐ zero) ⟶ (pick (var 0) A B ≐ B)
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P ⟨⟨trivial,trivial⟩,trivial⟩
    · simp [P,A,B,neg,RHCounterexamples.neg]
      exact Prf.impI (Prf.botE _ (Prf.impE Prf.hyp0 (Prf.eqRefl _)))
    · simp [P,A,B,neg,RHCounterexamples.neg]
      exact Prf.impI (pickS _ _ _)
  simpa [P,A,B,neg,RHCounterexamples.neg] using Prf.allE z h

/-- Rightmost bad sample, with default zero for a clean prefix. -/
private def hit (f : PR (k+1)) : PR (k+1) := .prec PacketLanguage.zeroR
  (.comp pickCode (cons (reindex f (cons 0 fun i => i.succ.succ)) (cons (.proj 1) fun _ => .proj 0)))

private theorem hitS (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n) :
    Prf PRAAx Γ (applyAt (hit f) (succ x) s ≐ pick (applyAt f x s) (applyAt (hit f) x s) x) := by
  let args := cons x (cons (applyAt (hit f) x s) s)
  apply Prf.eqTrans (PRA.precSucc _ _ _ s)
  apply Prf.eqTrans (PRA.comp _ _ args)
  apply congrApp pickCode
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i)
  · apply Prf.eqTrans (reindexAt f _ args)
    exact congrApp _ (Fin.cases (Prf.eqRefl _) fun _ => Prf.eqRefl _)
  · exact PRA.proj 1 args
  · exact PRA.proj 0 args

private theorem hitStep (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n)
    (ih : Prf PRAAx Γ (neg (applyAt (scan f) x s ≐ zero) ⟶ neg (applyAt f (applyAt (hit f) x s) s ≐ zero))) :
    Prf PRAAx Γ (neg (applyAt (scan f) (succ x) s ≐ zero) ⟶ neg (applyAt f (applyAt (hit f) (succ x) s) s ≐ zero)) := by
  apply Prf.impI
  apply Prf.orE (RHCounterexamples.zero_decidable (applyAt f x s))
  · let ctx := (applyAt f x s ≐ zero) :: neg (applyAt (scan f) (succ x) s ≐ zero) :: Γ
    have eqn := Prf.eqTrans (hitS (Γ := ctx) f s x) (Prf.eqTrans
      (congrApp pickCode (Fin.cases Prf.hyp0 fun _ => Prf.eqRefl _))
      (pick0 (applyAt (hit f) x s) x))
    have old : Prf PRAAx ctx (neg (applyAt (scan f) x s ≐ zero)) := Prf.impI (Prf.impE (Prf.hyp (by simp [ctx]) : Prf PRAAx _
        (neg (applyAt (scan f) (succ x) s ≐ zero)))
      (Prf.iffMpr (scanStep f s x) (Prf.andI Prf.hyp1 Prf.hyp0)))
    apply Prf.impI
    exact Prf.impE (Prf.impE ih.wk.wk old).wk (Prf.eqTrans (Prf.eqSymm (headEq f s eqn.wk)) Prf.hyp0)
  · let ctx := neg (applyAt f x s ≐ zero) :: neg (applyAt (scan f) (succ x) s ≐ zero) :: Γ
    have eqn := Prf.eqTrans (hitS (Γ := ctx) f s x) (Prf.impE (pickPos _ _ _) Prf.hyp0)
    apply Prf.impI
    exact Prf.impE Prf.hyp1 (Prf.eqTrans (Prf.eqSymm (headEq f s eqn.wk)) Prf.hyp0)

private theorem hitWorks (f : PR (k+1)) (s : Fin k → PTm n) (x : PTm n) :
    Prf PRAAx Γ (neg (applyAt (scan f) x s ≐ zero) ⟶ neg (applyAt f (applyAt (hit f) x s) s ≐ zero)) := by
  let S := fun i => Syn.shift (s i)
  let P := neg (applyAt (scan f) (var 0) S ≐ zero) ⟶ neg (applyAt f (applyAt (hit f) (var 0) S) S ≐ zero)
  have h : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P ⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩
    · simp [P,S,neg,RHCounterexamples.neg]
      exact Prf.impI (Prf.botE _ (Prf.impE Prf.hyp0 (scan0 f s)))
    · simp [P,S,neg,RHCounterexamples.neg]
      exact hitStep f S (var 0) Prf.hyp0
  simpa [P,S,neg,RHCounterexamples.neg] using Prf.allE x h

private def Block.bad : {q : Nat} → Block q → Fm PTm q
  | _, .test t => neg (t ≐ zero)
  | _, .bind b => .ex b.bad

private theorem badEq (b : Block k) : b.bad = RHCounterexamples.counter b.form := by
  induction b with
  | test t => rfl
  | bind b ih => exact congrArg Fm.ex ih

private theorem badTuple (b : Block k) (N : PTm n) (s : Fin k → PTm n)
    (dirty : Prf PRAAx Γ (neg (valueAt b N s ≐ zero))) : Prf PRAAx Γ (b.bad.subst s) := by
  induction b with
  | test t =>
    simp only [Block.bad,neg,RHCounterexamples.neg,Fm.subst_imp,Fm.subst_eq,Fm.subst_bot,PTm.subst_zero]
    exact Prf.impI (Prf.impE dirty.wk (Prf.eqTrans (leafEq t N s) Prf.hyp0))
  | bind b ih =>
    let f := reindex b.cube swapHead
    let args := cons N s
    let x := applyAt (hit f) N args
    have dirtyScan : Prf PRAAx Γ (neg (applyAt (scan f) N args ≐ zero)) :=
      Prf.impI (Prf.impE dirty.wk (Prf.eqTrans (bindEq b _ s) Prf.hyp0))
    have dirtySample := Prf.impE (hitWorks f args N) dirtyScan
    have dirtyChild : Prf PRAAx Γ (neg (valueAt b N (cons x s) ≐ zero)) :=
      Prf.impI (Prf.impE dirtySample.wk (Prf.eqTrans (swapEq b x N s) Prf.hyp0))
    apply Prf.exI x
    rw [Fm.subst_subst]
    have eqargs : (fun i => subst (inst x) (up s i)) = cons x s := by
      exact funext (Fin.cases (by simp [cons]) fun i => by simp [cons])
    rw [eqargs]
    exact ih _ dirtyChild

private theorem fromRows (b : Block k) (s : Fin k → PTm n) (target : Fm PTm n)
    (h : ∀ {m} (η : Fin n → PTm m) (row : Row b m),
      Prf PRAAx (Γ.map (fun A => A.subst η)) (neg (cell b (fun i => subst η (s i)) row ≐ zero) ⟶
        target.subst η)) : Prf PRAAx Γ ((b.bad.subst s) ⟶ target) := by
  induction b generalizing n with
  | test t =>
    simpa [cell,Block.bad,neg,RHCounterexamples.neg] using h var PUnit.unit
  | bind b ih =>
    have tailLemma : Prf PRAAx (Γ.map Fm.shift) ((b.bad.subst (up s)) ⟶ target.shift) := by
      apply ih
      intro m η row
      let tail := fun i => η (Fin.succ i)
      have v := h tail (η 0,row)
      have e : (fun i => subst η (up s i)) = cons (η 0) (fun i => subst tail (s i)) := by
        apply funext
        exact Fin.cases (by simp [cons]) (fun i => by simp [tail,cons,Syn.subst_shift])
      simp only [List.map_map, Function.comp_def, Fm.subst_shift, e]
      exact v
    apply Prf.impI
    apply Prf.exE Prf.hyp0
    exact Prf.impE tailLemma.wk.wk Prf.hyp0

/-- Positive finite witnesses on both sides. The reverse direction applies
the PR rightmost-hit selector once per universally quantified coordinate. -/
theorem failure_iff (b : Block n) : Prf PRAAx []
    (Fm.iff (RHCounterexamples.counter b.form) (RHCounterexamples.counter b.diagonal)) := by
  rw [← badEq]
  apply Prf.iffI
  · have pos : Prf PRAAx [] ((b.bad.subst var) ⟶ RHCounterexamples.counter b.diagonal) := by
      apply fromRows
      intro m η row
      let N := horizon b row
      apply Prf.impI
      apply Prf.exI N
      change Prf PRAAx _ (neg ((((valueAt b (var 0) (fun i => var i.succ) ≐ zero).subst (up η)).subst (inst N))))
      simp only [Fm.subst_eq,valueAt,subAt,PTm.subst_zero,subst_var,up_zero,up_succ,inst_zero,subst_inst_shift]
      apply Prf.impI
      apply Prf.impE Prf.hyp1
      simpa only [valueAt,subst_var] using readBox b N η row (fitsHorizon b row) (Prf.hyp0 (Γ := _))
    simpa using pos
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    exact badTuple b (var 0) (fun i => var i.succ) Prf.hyp0

/-- Reuse the one-dimensional count on the sequence of *entire* cubes. -/
private def cubeSequence (b : Block 0) : PR 5 := reindex b.cube (fun _ => 4)

private def emptyFields : Fin 4 → PTm n := fun _ => zero

def Block.census (b : Block 0) (form : PacketAudit.Form) : Fm PTm 0 :=
  PacketAudit.tests (cubeSequence b) form emptyFields

private theorem cubeSample (b : Block 0) (p : Fin 4 → PTm n) (j : PTm n) (s : Fin 0 → PTm n) :
    Prf PRAAx Γ (PacketAudit.sample (cubeSequence b) p j ≐ valueAt b j s) := by
  apply Prf.eqTrans (reindexAt _ _ _)
  exact congrApp _ (Fin.cases (Prf.eqRefl _) fun i => i.elim0)

private theorem auditPoint (b : Block 0) :
    Prf PRAAx [] (Fm.iff b.diagonal (b.census .pointwise)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.allI
    exact Prf.eqTrans (cubeSample _ _ _ _)
      (Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := b.diagonal)))
  · apply Prf.impI
    apply Prf.allI
    exact Prf.eqTrans (Prf.eqSymm (cubeSample b _ _ _))
      (Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := b.census .pointwise)))

theorem census_iff (b : Block 0) (form : PacketAudit.Form) :
    Prf PRAAx [] (Fm.iff b.form (b.census form)) :=
  Prf.iffTrans (diagonal_iff b) (Prf.iffTrans (auditPoint b)
    (PacketAudit.equivalence _ form _))

/-- A dirty cube whose every predecessor is clean. The order is now on the
one global radius, including every parameter of the family. -/
def Block.firstRadius (b : Block 0) : Fm PTm 0 :=
  PacketAudit.earliestFailure (cubeSequence b) emptyFields

private theorem auditDirty (b : Block 0) : Prf PRAAx []
    (Fm.iff (RHCounterexamples.counter b.diagonal) (PacketAudit.anyFailure (cubeSequence b) emptyFields)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    apply Prf.impI
    exact Prf.impE Prf.hyp1 (Prf.eqTrans (Prf.eqSymm (cubeSample b _ _ _)) Prf.hyp0)
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    apply Prf.impI
    exact Prf.impE Prf.hyp1 (Prf.eqTrans (cubeSample b _ _ _) Prf.hyp0)

theorem failure_iff_first_radius (b : Block 0) : Prf PRAAx []
    (Fm.iff (RHCounterexamples.counter b.form) b.firstRadius) :=
  Prf.iffTrans (failure_iff b) (Prf.iffTrans (auditDirty b)
    (PacketAudit.failure_iff_first _ _))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.CubeTests

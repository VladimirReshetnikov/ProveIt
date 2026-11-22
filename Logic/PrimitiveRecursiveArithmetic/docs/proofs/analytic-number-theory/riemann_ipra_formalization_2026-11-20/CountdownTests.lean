import Hypotheses
import RHCounterexamples

/-! One-bit observations of the magnitude of a failed packet. Object iPRA,
with explicit derivations using only quantifier-free induction. -/
namespace CountdownTests
open LeanProofs.ConciseIPRA Syn
open scoped Fm
open PTm (app zero succ)
variable {n m k : Nat} {Γ : List (Fm PTm n)}

private theorem congrArgPR (f : PR k) {xs ys : Fin k → PTm n}
    (h : ∀ i, Prf PRAAx Γ (xs i ≐ ys i)) :
    Prf PRAAx Γ (app f xs ≐ app f ys) := by
  simpa using Prf.eqCongr (app f (var : Fin k → PTm k)) h

def predT (x : PTm n) : PTm n := app PacketLanguage.predR (fun _ => x)
def drop (j x : PTm n) : PTm n := app PacketLanguage.reversedSub (Fin.cases j (fun _ => x))
private abbrev one : PTm n := succ zero

@[simp] private theorem substPred (σ : Fin n → PTm m) (x : PTm n) :
    subst σ (predT x) = predT (subst σ x) := rfl
@[simp] private theorem substDrop (σ : Fin n → PTm m) (j x : PTm n) :
    subst σ (drop j x) = drop (subst σ j) (subst σ x) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))
@[simp] private theorem repl_shift (s : PTm (n+1)) (u : PTm n) :
    subst (repl s) (Syn.shift u) = Syn.shift u := by rw [Syn.subst_shift]; rfl

private theorem congrPred {x y : PTm n} (h : Prf PRAAx Γ (x ≐ y)) :
    Prf PRAAx Γ (predT x ≐ predT y) := congrArgPR _ (fun _ => h)
private theorem congrDrop {j k x y : PTm n} (h : Prf PRAAx Γ (j ≐ k)) (p : Prf PRAAx Γ (x ≐ y)) :
    Prf PRAAx Γ (drop j x ≐ drop k y) := congrArgPR _ (Fin.cases h (fun _ => p))

private theorem pred0 : Prf PRAAx Γ (predT zero ≐ zero) := by
  have hh := PRA.precZero (Γ := Γ) PR.zero (.proj 0) (Fin.elim0 : Fin 0 → PTm n)
  apply Prf.eqTrans _ hh
  exact congrArgPR _ (Fin.cases (Prf.eqRefl _) (fun i => i.elim0))

private theorem predS (x : PTm n) : Prf PRAAx Γ (predT (succ x) ≐ x) := by
  let xs := (Fin.elim0 : Fin 0 → PTm n)
  have hh := PRA.precSucc (Γ := Γ) PR.zero (.proj 0) x xs
  apply Prf.eqTrans _ (Prf.eqTrans hh (PRA.proj 0 _))
  exact congrArgPR _ (Fin.cases (Prf.eqRefl _) (fun i => i.elim0))

theorem drop0 (x : PTm n) : Prf PRAAx Γ (drop zero x ≐ x) :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => x)) (PRA.proj 0 _)
private theorem dropS (j x : PTm n) : Prf PRAAx Γ (drop (succ j) x ≐ predT (drop j x)) := by
  apply Prf.eqTrans (PRA.precSucc _ _ j (fun _ => x))
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact congrArgPR _ (fun _ => PRA.proj 1 _)

theorem drop_at_zero (j : PTm n) : Prf PRAAx Γ (drop j zero ≐ zero) := by
  let P : Fm PTm (n+1) := drop (var 0) zero ≐ zero
  have allP : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simpa [P] using drop0 (Γ := Γ) (zero : PTm n)
    · simp only [P,Fm.subst_eq,substDrop,subst_var,repl_zero,PTm.subst_zero]
      exact Prf.eqTrans (dropS _ _) (Prf.eqTrans (congrPred (Prf.hyp0 (φ := P))) pred0)
  simpa [P] using Prf.allE j allP

theorem cancel_step (j x : PTm n) :
    Prf PRAAx Γ (drop (succ j) (succ x) ≐ drop j x) := by
  let X := Syn.shift x
  let P := drop (succ (var 0)) (succ X) ≐ drop (var 0) X
  have allP : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simp only [P,X,Fm.subst_eq,substDrop,PTm.subst_succ,subst_var,inst_zero,subst_inst_shift]
      exact Prf.eqTrans (dropS _ _) (Prf.eqTrans (congrPred (drop0 _))
        (Prf.eqTrans (predS _) (Prf.eqSymm (drop0 _))))
    · simp only [P,X,Fm.subst_eq,substDrop,PTm.subst_succ,subst_var,repl_zero,repl_shift]
      exact Prf.eqTrans (dropS _ _) (Prf.eqTrans (congrPred (Prf.hyp0 (φ := P)))
        (Prf.eqSymm (dropS _ _)))
  simpa [P,X] using Prf.allE j allP

private theorem last_tick (j : PTm n) : Prf PRAAx Γ (drop j (succ j) ≐ one) := by
  let P : Fm PTm (n+1) := drop (var 0) (succ (var 0)) ≐ succ zero
  have allP : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simpa [P] using drop0 (Γ := Γ) (one : PTm n)
    · simp only [P,Fm.subst_eq,substDrop,PTm.subst_succ,subst_var,repl_zero,PTm.subst_zero]
      exact Prf.eqTrans (cancel_step _ _) (Prf.hyp0 (φ := P))
  simpa [P] using Prf.allE j allP

private theorem split_size (x : PTm n) :
    Prf PRAAx Γ ((x ≐ zero) ⋎ (drop (predT x) x ≐ one)) := by
  let P : Fm PTm (n+1) := (var 0 ≐ zero) ⋎ (drop (predT (var 0)) (var 0) ≐ succ zero)
  have allP : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P ⟨trivial,trivial⟩
    · simp only [P,Fm.subst_or,Fm.subst_eq,subst_var,inst_zero,PTm.subst_zero,PTm.subst_succ,
        substPred,substDrop]
      exact Prf.orI₁ (Prf.eqRefl _)
    · simp only [P,Fm.subst_or,Fm.subst_eq,subst_var,repl_zero,PTm.subst_zero,PTm.subst_succ,
        substPred,substDrop]
      exact Prf.orI₂ (Prf.eqTrans (congrDrop (predS _) (Prf.eqRefl _)) (last_tick _))
  simpa [P] using Prf.allE x allP

inductive Mode | atPredecessor | everyStep

def test : Mode → PTm n → Fm PTm n
  | .atPredecessor, x => drop (predT x) x ≐ zero
  | .everyStep, x => .all ((drop (var 0) (Syn.shift x) ≐ succ zero) ⟶ .bot)

theorem point (m : Mode) (x : PTm n) : Prf PRAAx [] (Fm.iff (x ≐ zero) (test m x)) := by
  cases m with
  | atPredecessor =>
    apply Prf.iffI
    · apply Prf.impI
      exact Prf.eqTrans (congrDrop (Prf.eqRefl _) Prf.hyp0) (drop_at_zero _)
    · apply Prf.impI
      apply Prf.orE (split_size x)
      · exact Prf.hyp0
      · exact Prf.botE _ (Prf.impE (PRA.succNeZero zero) (Prf.eqTrans (Prf.eqSymm Prf.hyp0) Prf.hyp1))
  | everyStep =>
    apply Prf.iffI
    · apply Prf.impI
      apply Prf.allI
      apply Prf.impI
      have hz : Prf PRAAx [(x ≐ zero).shift] (Syn.shift x ≐ zero) := by
        simpa [Fm.shift,Syn.shift] using (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := x ≐ zero)).shift
      have clean := Prf.eqTrans (congrDrop (Prf.eqRefl (var 0)) hz) (drop_at_zero _)
      exact Prf.impE (PRA.succNeZero zero) (Prf.eqTrans (Prf.eqSymm Prf.hyp0) clean.wk)
    · apply Prf.impI
      have hnot := Prf.allE (predT x) (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := test .everyStep x))
      have hn : Prf PRAAx [test .everyStep x] ((drop (predT x) x ≐ one) ⟶ .bot) := by
        simpa [test] using hnot
      apply Prf.orE (split_size x)
      · exact Prf.hyp0
      · exact Prf.botE _ (Prf.impE hn.wk Prf.hyp0)

/-- Transform every terminal zero test in a universal block. -/
def transform (m : Mode) : {q : Nat} → Fm PTm q → Fm PTm q
  | _, .all A => .all (transform m A)
  | _, .eq z _ => test m z
  | _, A => A

theorem equivalence (m : Mode) {A : Fm PTm n} (ha : RHCounterexamples.UniversalZero A) :
    Prf PRAAx [] (Fm.iff A (transform m A)) := by
  induction ha with
  | matrix z => exact point m z
  | binder _ ih =>
    apply Prf.iffI
    · exact Prf.impI (Prf.allI (Prf.iffMp (Prf.ofNil ih) (Prf.allOpen Prf.hyp0)))
    · exact Prf.impI (Prf.allI (Prf.iffMpr (Prf.ofNil ih) (Prf.allOpen Prf.hyp0)))

theorem rh (m : Mode) : Prf PRAAx [] (Fm.iff RiemannIPRA.RH (transform m RiemannIPRA.RH)) :=
  equivalence m (.binder (.matrix _))
theorem grh (m : Mode) : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH (transform m RiemannIPRA.GRH)) :=
  equivalence m (.binder (.binder (.matrix _)))
theorem erh (m : Mode) : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH (transform m RiemannIPRA.ERH)) :=
  equivalence m (.binder (.binder (.binder (.binder (.binder (.matrix _))))))

end CountdownTests

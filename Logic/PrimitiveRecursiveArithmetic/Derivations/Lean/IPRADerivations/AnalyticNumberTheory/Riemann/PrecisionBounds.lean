import IPRADerivations.AnalyticNumberTheory.Riemann.CountdownTests
import IPRADerivations.AnalyticNumberTheory.Riemann.CompilerSemantics

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`PrecisionBounds.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Bounded multiples and finite removal of additive precision in object iPRA. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PrecisionBounds
open LeanProofs.ConciseIPRA Syn CountdownTests
open scoped Fm
open PTm (app zero succ)

variable {n m k : Nat} {Γ : List (Fm PTm n)}

private theorem congrPR (f : PR k) {xs ys : Fin k → PTm n} (h : ∀ i, Prf PRAAx Γ (xs i ≐ ys i)) :
    Prf PRAAx Γ (app f xs ≐ app f ys) := by simpa using Prf.eqCongr (app f Syn.var) h

private def addT (x y : PTm n) := app PacketLanguage.addR (Fin.cases x fun _ => y)
private theorem add0 (y : PTm n) : Prf PRAAx Γ (addT zero y ≐ y) :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => y)) (PRA.proj 0 _)

private theorem addS (x y : PTm n) : Prf PRAAx Γ (addT (succ x) y ≐ succ (addT x y)) := by
  apply Prf.eqTrans (PRA.precSucc _ _ x (fun _ => y))
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact congrPR _ (fun _ => PRA.proj 1 _)

private theorem succEq {x y : PTm n} (h : Prf PRAAx Γ (x ≐ y)) :
    Prf PRAAx Γ (succ x ≐ succ y) := congrPR _ (fun _ => h)

private theorem rightDrop (j : PTm n) {x y : PTm n} (h : Prf PRAAx Γ (x ≐ y)) :
    Prf PRAAx Γ (drop j x ≐ drop j y) := congrPR _ (Fin.cases (Prf.eqRefl _) (fun _ => h))

/-- Recurse on the first argument and prepend one copy of the second argument. -/
def scaleR : PR 2 := .prec PacketLanguage.zeroR
  (.comp PacketLanguage.addR (Fin.cases (.proj 2) fun _ => .proj 1))

def scale (z k : PTm n) := app scaleR (Fin.cases z fun _ => k)

private theorem scale0 (k : PTm n) : Prf PRAAx Γ (scale zero k ≐ zero) := by
  apply Prf.eqTrans (PRA.precZero _ _ (fun _ => k))
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact congrPR _ (fun i => i.elim0)

private theorem scaleS (z k : PTm n) : Prf PRAAx Γ (scale (succ z) k ≐ addT k (scale z k)) := by
  let xs := (Fin.cases z (Fin.cases (scale z k) (fun _ => k)) : Fin 3 → PTm n)
  apply Prf.eqTrans (PRA.precSucc _ _ z (fun _ => k))
  apply Prf.eqTrans (PRA.comp _ _ xs)
  exact congrPR _ (Fin.cases (PRA.proj 2 xs) (fun _ => PRA.proj 1 xs))

@[simp] private theorem subDrop (σ : Fin n → PTm m) (j x : PTm n) :
    subst σ (drop j x) = drop (subst σ j) (subst σ x) := by
  apply congrArg (app _); exact funext (Fin.cases rfl fun _ => rfl)
@[simp] private theorem subAdd (σ : Fin n → PTm m) (j x : PTm n) :
    subst σ (addT j x) = addT (subst σ j) (subst σ x) := by
  apply congrArg (app _); exact funext (Fin.cases rfl fun _ => rfl)
@[simp] private theorem subScale (σ : Fin n → PTm m) (j x : PTm n) :
    subst σ (scale j x) = scale (subst σ j) (subst σ x) := by
  apply congrArg (app _); exact funext (Fin.cases rfl fun _ => rfl)
@[simp] private theorem repl_shift (s : PTm (n+1)) (u : PTm n) :
    subst (repl s) (Syn.shift u) = Syn.shift u := by rw [Syn.subst_shift]; rfl

private theorem remaining (j y : PTm n) :
    Prf PRAAx Γ (drop j (addT (succ j) y) ≐ succ y) := by
  let Y := Syn.shift y
  let P := drop (var 0) (addT (succ (var 0)) Y) ≐ succ Y
  have hall : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P trivial
    · simp only [P,Y,Fm.subst_eq,subDrop,subAdd,PTm.subst_succ,subst_var,inst_zero,subst_inst_shift]
      exact Prf.eqTrans (drop0 _) (Prf.eqTrans (addS _ _) (succEq (add0 _)))
    · simp only [P,Y,Fm.subst_eq,subDrop,subAdd,PTm.subst_succ,subst_var,repl_zero,repl_shift]
      exact Prf.eqTrans (rightDrop _ (addS _ _)) (Prf.eqTrans (cancel_step _ _) (Prf.hyp0 (φ := P)))
  simpa [P,Y] using Prf.allE j hall

/-- A single multiplier J+1 detects strict positive excess against budget J. -/
theorem finite_recovery (J z : PTm n) :
    Prf PRAAx Γ ((drop J (scale z (succ J)) ≐ zero) ⟶ (z ≐ zero)) := by
  let B := Syn.shift J
  let P := (drop B (scale (var 0) (succ B)) ≐ zero) ⟶ (var 0 ≐ zero)
  have hall : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P ⟨trivial,trivial⟩
    · simp only [P,B,Fm.subst_imp,Fm.subst_eq,subDrop,subScale,PTm.subst_succ,
        PTm.subst_zero,subst_var,inst_zero,subst_inst_shift]
      exact Prf.impI (Prf.eqRefl _)
    · simp only [P,B,Fm.subst_imp,Fm.subst_eq,subDrop,subScale,PTm.subst_succ,
        PTm.subst_zero,subst_var,repl_zero,repl_shift]
      apply Prf.impI
      exact Prf.botE _ (Prf.impE (PRA.succNeZero _) (Prf.eqTrans (Prf.eqSymm
        (Prf.eqTrans (rightDrop B (scaleS (var 0) (succ B))) (remaining B _))) Prf.hyp0))
  simpa [P,B] using Prf.allE z hall

private theorem within_zero (J k : PTm n) {z : PTm n} (h : Prf PRAAx Γ (z ≐ zero)) :
    Prf PRAAx Γ (drop J (scale z k) ≐ zero) := by
  have hz : Prf PRAAx Γ (scale z k ≐ scale zero k) :=
    congrPR _ (Fin.cases h (fun _ => Prf.eqRefl _))
  exact Prf.eqTrans (rightDrop J (Prf.eqTrans hz (scale0 k))) (drop_at_zero _)

def allMultiples (J z : PTm n) : Fm PTm n :=
  .all (drop (Syn.shift J) (scale (Syn.shift z) (var 0)) ≐ zero)

theorem fixed_budget (J z : PTm n) :
    Prf PRAAx [] (Fm.iff (z ≐ zero) (allMultiples J z)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.allI
    apply within_zero
    simpa [Fm.shift,Syn.shift] using (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := z ≐ zero)).shift
  · apply Prf.impI
    apply Prf.impE (finite_recovery J z)
    have h := Prf.allE (succ J) (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := allMultiples J z))
    simpa [allMultiples] using h

def bounded (z : PTm n) : Fm PTm n := .ex (allMultiples (var 0) (Syn.shift z))

@[simp] private theorem substAllMultiples (σ : Fin n → PTm m) (J z : PTm n) :
    (allMultiples J z).subst σ = allMultiples (subst σ J) (subst σ z) := by
  simp only [allMultiples,Fm.subst_all,Fm.subst_eq,subDrop,subScale,PTm.subst_zero,subst_var,up_zero]
  congr 3 <;> simp [Syn.subst_shift,Syn.shift_subst]

theorem bounded_iff (z : PTm n) : Prf PRAAx [] (Fm.iff (z ≐ zero) (bounded z)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.exI zero
    simpa [bounded] using Prf.iffMp (Prf.ofNil (fixed_budget zero z)) (Prf.hyp0 (Γ := []))
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    have hz := Prf.iffMpr (Prf.ofNil (fixed_budget (var 0) (Syn.shift z)))
      (Prf.hyp0 (Γ := [(bounded z).shift]))
    simpa [Fm.shift,Syn.shift,bounded] using hz

def transform : {q : Nat} → Fm PTm q → Fm PTm q
  | _, .all A => .all (transform A)
  | _, .eq z _ => bounded z
  | _, A => A

theorem equivalence {A : Fm PTm n} (ha : RHCounterexamples.UniversalZero A) :
    Prf PRAAx [] (Fm.iff A (transform A)) := by
  induction ha with
  | matrix z => exact bounded_iff z
  | binder _ ih =>
    apply Prf.iffI
    · exact Prf.impI (Prf.allI (Prf.iffMp (Prf.ofNil ih) (Prf.allOpen Prf.hyp0)))
    · exact Prf.impI (Prf.allI (Prf.iffMpr (Prf.ofNil ih) (Prf.allOpen Prf.hyp0)))

theorem rh : Prf PRAAx [] (Fm.iff RiemannIPRA.RH (transform RiemannIPRA.RH)) :=
  equivalence (.binder (.matrix _))
theorem grh : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH (transform RiemannIPRA.GRH)) :=
  equivalence (.binder (.binder (.matrix _)))
theorem erh : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH (transform RiemannIPRA.ERH)) :=
  equivalence (.binder (.binder (.binder (.binder (.binder (.matrix _))))))

open PacketLanguage in
theorem numerical_scale (z k : Nat) : value scaleR (Fin.cases z fun _ => k) = z*k := by
  change Nat.rec (motive := fun _ => Nat) (value (zeroR (n := 1)) (fun _ => k)) (fun j y => value (.comp addR (Fin.cases (.proj (2 : Fin 3)) fun _ => .proj 1))
    (Fin.cases j (Fin.cases y (fun _ => k)))) z = _
  rw [value_zeroR]
  have hs : (fun j y : Nat => value (.comp addR (Fin.cases (.proj (2 : Fin 3)) fun _ => .proj 1))
      (Fin.cases j (Fin.cases y (fun _ => k)))) = (fun _ y => k+y) := by
    funext j y
    rw [value, value_addR]
    rfl
  rw [hs]
  induction z with
  | zero => simp
  | succ z ih => change k + _ = _; rw [ih,Nat.succ_mul,Nat.add_comm k]

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PrecisionBounds

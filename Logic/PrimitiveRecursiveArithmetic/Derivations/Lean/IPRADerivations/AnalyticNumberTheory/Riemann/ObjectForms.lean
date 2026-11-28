import IPRADerivations.AnalyticNumberTheory.Riemann.Hypotheses
import IPRADerivations.AnalyticNumberTheory.Riemann.RHCounterexamples

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`ObjectForms.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! A primitive-recursive running count of failed packets. All equivalences in
this module are derivations in the first-order object calculus. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketAudit
open LeanProofs.ConciseIPRA Syn
open scoped Fm
open PTm (app zero succ)

variable {n k m : Nat} {Γ : List (Fm PTm n)}

private theorem appCongr (f : PR k) {xs ys : Fin k → PTm n}
    (h : ∀ i, Prf PRAAx Γ (xs i ≐ ys i)) :
    Prf PRAAx Γ (app f xs ≐ app f ys) := by
  simpa using Prf.eqCongr (app f (Syn.var : Fin k → PTm k)) h

private def select (f : PR k) (s : Fin k → Fin m) : PR m :=
  .comp f (fun i => .proj (s i))

private theorem evalSelect (f : PR k) (s : Fin k → Fin m) (xs : Fin m → PTm n) :
    Prf PRAAx Γ (app (select f s) xs ≐ app f (fun i => xs (s i))) :=
  Prf.eqTrans (PRA.comp _ _ _) (appCongr f (fun i => PRA.proj (s i) xs))

/-- On a nonzero excess, increment the old count exactly once. -/
def bump : PR 2 := .prec (.proj 0) (select .succ (fun _ => 2))

def tick (x a : PTm n) : PTm n := app bump (Fin.cases x (fun _ => a))

private theorem tick0 (a : PTm n) : Prf PRAAx Γ (tick zero a ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => a)) (PRA.proj 0 _)

private theorem tickS (x a : PTm n) : Prf PRAAx Γ (tick (succ x) a ≐ succ a) :=
  Prf.eqTrans (PRA.precSucc _ _ x (fun _ => a)) (evalSelect _ _ _)

private theorem selfNeSucc (a : PTm n) :
    Prf PRAAx Γ ((succ a ≐ a) ⟶ Fm.bot) := by
  let P : Fm PTm (n+1) := (succ (var 0) ≐ var 0) ⟶ Fm.bot
  have hi : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨trivial,trivial⟩
    · simpa [P] using PRA.succNeZero (Γ := Γ) (zero : PTm n)
    · simp only [P, Fm.subst_imp, Fm.subst_eq, PTm.subst_succ, subst_var, repl_zero,
        Fm.subst_bot]
      apply Prf.impI
      apply Prf.impE Prf.hyp1
      have inj := Prf.ax (Γ := (succ (succ (var 0)) ≐ succ (var 0)) :: P :: Γ.map Fm.shift) PRAAx.succInj
        (Fin.cases (succ (var 0 : PTm (n+1))) (fun _ => var 0))
      exact Prf.impE (by simpa using inj) Prf.hyp0
  simpa [P] using Prf.allE a hi

private def specification (x a : PTm n) : Fm PTm n :=
  Fm.iff (tick x a ≐ a) (x ≐ zero) ⋏
    Fm.iff (tick x a ≐ zero) ((x ≐ zero) ⋏ (a ≐ zero))

@[simp] private theorem substTick (σ : Fin n → PTm m) (x a : PTm n) :
    subst σ (tick x a) = tick (subst σ x) (subst σ a) := by
  unfold tick
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))

@[simp] private theorem substSpec (σ : Fin n → PTm m) (x a : PTm n) :
    (specification x a).subst σ = specification (subst σ x) (subst σ a) := by
  simp [specification,Fm.iff]

private theorem spec0 (a : PTm n) : Prf PRAAx Γ (specification zero a) := by
  apply Prf.andI
  · exact Prf.iffI (Prf.impI (Prf.eqRefl _)) (Prf.impI (tick0 a))
  · apply Prf.iffI
    · exact Prf.impI (Prf.andI (Prf.eqRefl _) (Prf.eqTrans (Prf.eqSymm (tick0 a)) Prf.hyp0))
    · exact Prf.impI (Prf.eqTrans (tick0 a) (Prf.andE₂ Prf.hyp0))

private theorem specS (x a : PTm n) : Prf PRAAx Γ (specification (succ x) a) := by
  apply Prf.andI
  · apply Prf.iffI
    · exact Prf.impI (Prf.botE _ (Prf.impE (selfNeSucc a)
        (Prf.eqTrans (Prf.eqSymm (tickS x a)) Prf.hyp0)))
    · exact Prf.impI (Prf.botE _ (Prf.impE (PRA.succNeZero x) Prf.hyp0))
  · apply Prf.iffI
    · exact Prf.impI (Prf.botE _ (Prf.impE (PRA.succNeZero a)
        (Prf.eqTrans (Prf.eqSymm (tickS x a)) Prf.hyp0)))
    · exact Prf.impI (Prf.botE _ (Prf.impE (PRA.succNeZero x) (Prf.andE₁ Prf.hyp0)))

@[simp] private theorem replShift (s : PTm (n+1)) (a : PTm n) :
    subst (repl s) (Syn.shift a) = Syn.shift a := by
  rw [Syn.subst_shift]; rfl

private theorem specAt (x a : PTm n) : Prf PRAAx Γ (specification x a) := by
  let P := specification (var 0) (Syn.shift a)
  have hi : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨⟨⟨trivial,trivial⟩,⟨trivial,trivial⟩⟩,
        ⟨⟨trivial,⟨trivial,trivial⟩⟩,⟨⟨trivial,trivial⟩,trivial⟩⟩⟩
    · simpa [P] using spec0 (Γ := Γ) a
    · simpa [P] using
        specS (Γ := P :: Γ.map Fm.shift) (var 0) (Syn.shift a)
  simpa [P] using Prf.allE x hi

private def tuple5 {α : Type} (a b c d e : α) : Fin 5 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (fun _ => e))))

private def fields {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

/-- The original numerical test takes its cutoff last. -/
def sample (f : PR 5) (p : Fin 4 → PTm n) (j : PTm n) :=
  app f (tuple5 (p 0) (p 1) (p 2) (p 3) j)

private def atStep (f : PR 5) : PR 6 := select f (tuple5 2 3 4 5 0)

private def step (f : PR 5) : PR 6 :=
  .comp bump (Fin.cases (atStep f) (fun _ => .proj 1))

/-- With its cutoff first, this symbol counts the positive samples for j < N. -/
def counts (f : PR 5) : PR 5 := .prec PacketLanguage.zeroR (step f)

def countAt (f : PR 5) (p : Fin 4 → PTm n) (j : PTm n) :=
  app (counts f) (Fin.cases j p)

variable (f : PR 5)

private theorem count0 (p : Fin 4 → PTm n) :
    Prf PRAAx Γ (countAt f p zero ≐ zero) := by
  apply Prf.eqTrans (PRA.precZero _ _ p)
  apply Prf.eqTrans (PRA.comp _ _ p)
  exact appCongr .zero (fun i => i.elim0)

private theorem countS (p : Fin 4 → PTm n) (j : PTm n) :
    Prf PRAAx Γ (countAt f p (succ j) ≐ tick (sample f p j) (countAt f p j)) := by
  let xs : Fin 6 → PTm n := Fin.cases j (Fin.cases (countAt f p j) p)
  apply Prf.eqTrans (PRA.precSucc _ _ j p)
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply appCongr bump
  refine Fin.cases ?_ (fun _ => ?_)
  · apply Prf.eqTrans (evalSelect f _ xs)
    apply appCongr f
    exact Fin.cases (Prf.eqRefl _) (fun i => Fin.cases (Prf.eqRefl _) (fun j =>
      Fin.cases (Prf.eqRefl _) (fun k => Fin.cases (Prf.eqRefl _)
        (fun _ => Prf.eqRefl _) k) j) i)
  · exact PRA.proj 1 xs


private def raised (p : Fin 4 → PTm n) : Fin 4 → PTm (n+1) := fun i => Syn.shift (p i)

@[simp] private theorem substSample (σ : Fin n → PTm m) (p : Fin 4 → PTm n) (j : PTm n) :
    subst σ (sample f p j) = sample f (fun i => subst σ (p i)) (subst σ j) := by
  apply congrArg (app f)
  exact funext (Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.cases rfl
    (fun k => Fin.cases rfl (fun _ => rfl) k) j) i))

@[simp] private theorem substCount (σ : Fin n → PTm m) (p : Fin 4 → PTm n) (j : PTm n) :
    subst σ (countAt f p j) = countAt f (fun i => subst σ (p i)) (subst σ j) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))

private theorem atSuccessor (p : Fin 4 → PTm n) (j : PTm n) :
    Prf PRAAx Γ (Fm.iff (countAt f p (succ j) ≐ zero)
      ((sample f p j ≐ zero) ⋏ (countAt f p j ≐ zero))) := by
  have eqn := countS (Γ := Γ) f p j
  have spec := Prf.andE₂ (specAt (Γ := Γ) (sample f p j) (countAt f p j))
  apply Prf.iffI
  · exact Prf.impI (Prf.iffMp spec.wk (Prf.eqTrans (Prf.eqSymm eqn.wk) Prf.hyp0))
  · exact Prf.impI (Prf.eqTrans eqn.wk (Prf.iffMpr spec.wk Prf.hyp0))

private theorem stationaryAt (p : Fin 4 → PTm n) (j : PTm n) :
    Prf PRAAx Γ (Fm.iff (countAt f p (succ j) ≐ countAt f p j) (sample f p j ≐ zero)) := by
  have eqn := countS (Γ := Γ) f p j
  have spec := Prf.andE₁ (specAt (Γ := Γ) (sample f p j) (countAt f p j))
  apply Prf.iffI
  · exact Prf.impI (Prf.iffMp spec.wk (Prf.eqTrans (Prf.eqSymm eqn.wk) Prf.hyp0))
  · exact Prf.impI (Prf.eqTrans eqn.wk (Prf.iffMpr spec.wk Prf.hyp0))

/-- `advance k j` is the cutoff obtained by taking k successors from j. -/
def advance (k j : PTm n) := app PacketLanguage.addR (Fin.cases k (fun _ => j))

@[simp] private theorem substAdvance (σ : Fin n → PTm m) (k j : PTm n) :
    subst σ (advance k j) = advance (subst σ k) (subst σ j) := by
  unfold advance
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))

private theorem advance0 (j : PTm n) : Prf PRAAx Γ (advance zero j ≐ j) :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => j)) (PRA.proj 0 _)

private theorem advanceS (k j : PTm n) : Prf PRAAx Γ (advance (succ k) j ≐ succ (advance k j)) :=
  Prf.eqTrans (PRA.precSucc _ _ k (fun _ => j))
    (evalSelect .succ (fun _ : Fin 1 => (1 : Fin 3)) _)

private theorem countCongr (p : Fin 4 → PTm n) {a b : PTm n}
    (h : Prf PRAAx Γ (a ≐ b)) : Prf PRAAx Γ (countAt f p a ≐ countAt f p b) :=
  appCongr (counts f) (Fin.cases h (fun _ => Prf.eqRefl _))

/-- A larger clean prefix certifies every specified earlier sample. The
induction formula has one implication between two atomic equalities. -/
private theorem rollback (p : Fin 4 → PTm n) (j k : PTm n) :
    Prf PRAAx Γ ((countAt f p (advance k (succ j)) ≐ zero) ⟶ (sample f p j ≐ zero)) := by
  let P : Fm PTm (n+1) := (countAt f (raised p) (advance (var 0) (succ (Syn.shift j))) ≐ zero) ⟶
    (sample f (raised p) (Syn.shift j) ≐ zero)
  have hi : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨trivial,trivial⟩
    · simp only [P,raised,Fm.subst_imp,Fm.subst_eq,substCount,substSample,substAdvance,
        PTm.subst_zero,PTm.subst_succ,subst_var,inst_zero,subst_inst_shift]
      apply Prf.impI
      apply Prf.andE₁ (Prf.iffMp (atSuccessor f p j) _)
      exact Prf.eqTrans (Prf.eqSymm (countCongr f p (advance0 (succ j)))) Prf.hyp0
    · simp only [P,raised,Fm.subst_imp,Fm.subst_eq,substCount,substSample,substAdvance,
        PTm.subst_zero,PTm.subst_succ,subst_var,repl_zero,replShift]
      apply Prf.impI
      apply Prf.impE Prf.hyp1
      let t := advance (var 0) (succ (Syn.shift j))
      apply Prf.andE₂ (Prf.iffMp (atSuccessor f (raised p) t) _)
      exact Prf.eqTrans (Prf.eqSymm (countCongr f (raised p) (advanceS _ _))) Prf.hyp0
  simpa [P,raised] using Prf.allE k hi

/-- Equivalent presentations with the same polynomial parameters. -/
inductive Form where
  | pointwise | prefixZero | stationary | invariant | noFirst | cofinal | eventual
  | schedule (lag : PR 1)

def tests (form : Form) (p : Fin 4 → PTm n) : Fm PTm n :=
  let ps := raised p
  let j : PTm (n+1) := var 0
  let good := sample f ps j ≐ zero
  let clean := countAt f ps j ≐ zero
  let next := countAt f ps (succ j)
  match form with
  | .pointwise => .all good
  | .prefixZero => .all clean
  | .stationary => .all (next ≐ countAt f ps j)
  | .invariant => .all (clean ⟶ (next ≐ zero))
  | .noFirst => RHCounterexamples.neg (.ex (clean ⋏ RHCounterexamples.neg good))
  | .cofinal => .all (.ex (countAt f (raised ps) (advance (var 0) (succ (var 1))) ≐ zero))
  | .eventual => .ex (.all (countAt f (raised ps) (advance (var 1) (succ (var 0))) ≐ zero))
  | .schedule lag => .all (countAt f ps (advance (app lag (fun _ => j)) (succ j)) ≐ zero)

private theorem boundAt {form : Form} (p : Fin 4 → PTm n)
    (h : Prf PRAAx Γ (tests f form p)) (j : PTm n) :
    Prf PRAAx Γ (match form with
      | .pointwise => sample f p j ≐ zero
      | .prefixZero => countAt f p j ≐ zero
      | .stationary => countAt f p (succ j) ≐ countAt f p j
      | .invariant => (countAt f p j ≐ zero) ⟶ (countAt f p (succ j) ≐ zero)
      | .noFirst => tests f .noFirst p
      | .cofinal => tests f .cofinal p
      | .eventual => tests f .eventual p
      | .schedule lag => tests f (.schedule lag) p) := by
  cases form <;> first | exact h | simpa [tests,raised] using Prf.allE j h

private theorem allCongr {A B : Fm PTm (n+1)} (h : Prf PRAAx [] (Fm.iff A B)) :
    Prf PRAAx [] (Fm.iff (Fm.all A) (Fm.all B)) := by
  apply Prf.iffI
  · exact Prf.impI (Prf.allI (Prf.iffMp (Prf.ofNil h) (Prf.allOpen Prf.hyp0)))
  · exact Prf.impI (Prf.allI (Prf.iffMpr (Prf.ofNil h) (Prf.allOpen Prf.hyp0)))

private theorem pointToInvariant (p : Fin 4 → PTm n) :
    Prf PRAAx [] ((tests f .pointwise p) ⟶ tests f .invariant p) := by
  apply Prf.impI
  apply Prf.allI
  have good := Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (φ := tests f .pointwise p) (Γ := []))
  exact Prf.impI (Prf.iffMpr (atSuccessor f (raised p) (var 0)) (Prf.andI good.wk Prf.hyp0))

private theorem invariantToPrefix (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .invariant p ⟶ tests f .prefixZero p) := by
  apply Prf.impI
  let P := countAt f (raised p) (var 0) ≐ zero
  apply PRA.qfInd P trivial
  · simpa [P,raised] using count0 (Γ := [tests f .invariant p]) f p
  · have stepProof := Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .invariant p))
    simp only [P,Fm.subst_eq,substCount,subst_var,repl_zero,PTm.subst_zero,raised,replShift]
    exact Prf.impE stepProof.wk (Prf.hyp0 (φ := P))

theorem upShiftTerm (σ : Fin n → PTm m) (t : PTm n) :
    subst (up σ) (Syn.shift t) = Syn.shift (subst σ t) := by
  simp [Syn.subst_shift, Syn.shift_subst]

private theorem prefixToPoint (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .prefixZero p ⟶ tests f .pointwise p) := by
  apply Prf.impI
  apply Prf.allI
  have h := (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .prefixZero p)).shift
  have h' : Prf PRAAx [(tests f .prefixZero p).shift] (tests f .prefixZero (raised p)) := by
    unfold tests raised Fm.shift at h ⊢
    simp only [List.map_cons,List.map_nil,Fm.subst_all,Fm.subst_eq,substCount,
      subst_var, up_zero, PTm.subst_zero, upShiftTerm] at h ⊢
    exact h
  exact Prf.andE₁ (Prf.iffMp (atSuccessor f (raised p) (var 0))
    (boundAt f (raised p) h' (succ (var 0))))

private theorem pointToNoFirst (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .pointwise p ⟶ tests f .noFirst p) := by
  apply Prf.impI
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  exact Prf.impE (Prf.andE₂ Prf.hyp0) (Prf.allOpen (Prf.hyp1
    (Ax := PRAAx) (Γ := []) (φ := tests f .pointwise p))).wk

private theorem noFirstToInvariant (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .noFirst p ⟶ tests f .invariant p) := by
  apply Prf.impI
  apply Prf.allI
  apply Prf.impI
  apply Prf.iffMpr (atSuccessor f (raised p) (var 0))
  apply Prf.andI _ Prf.hyp0
  apply Prf.orE (RHCounterexamples.zero_decidable _)
  · exact Prf.hyp0
  · apply Prf.botE _
    let clean := countAt f (raised p) (var 0) ≐ zero
    let fails := RHCounterexamples.neg (sample f (raised p) (var 0) ≐ zero)
    have bad : Prf PRAAx [fails, clean, (tests f .noFirst p).shift] (clean ⋏ fails) :=
      Prf.andI Prf.hyp1 Prf.hyp0
    have noBad := (Prf.shift (Prf.hyp0 (Ax := PRAAx) (Γ := [])
      (φ := tests f .noFirst p))).wk (ψ := clean)
    have noBad := noBad.wk (ψ := fails)
    apply Prf.impE noBad
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    exact bad

private theorem prefixShift (p : Fin 4 → PTm n) :
    (tests f .prefixZero p).shift = tests f .prefixZero (raised p) := by
  unfold tests raised Fm.shift
  simp only [Fm.subst_all,Fm.subst_eq,substCount,subst_var,up_zero,PTm.subst_zero,upShiftTerm]
  rfl

private theorem pointShift (p : Fin 4 → PTm n) :
    (tests f .pointwise p).shift = tests f .pointwise (raised p) := by
  unfold tests raised Fm.shift
  simp only [Fm.subst_all,Fm.subst_eq,substSample,subst_var,up_zero,PTm.subst_zero,upShiftTerm]
  rfl

private theorem prefixToCofinal (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .prefixZero p ⟶ tests f .cofinal p) := by
  apply Prf.impI
  apply Prf.allI
  apply Prf.exI zero
  simp only [Fm.subst_eq,substCount,substAdvance,PTm.subst_succ,PTm.subst_zero,subst_var,
    inst_zero,inst_one,raised,subst_inst_shift]
  have h := (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .prefixZero p)).shift
  rw [prefixShift] at h
  exact boundAt f (raised p) h (advance zero (succ (var 0)))

private theorem cofinalToPoint (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .cofinal p ⟶ tests f .pointwise p) := by
  apply Prf.impI
  apply Prf.allI
  apply Prf.exE (Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .cofinal p)))
  simp only [Fm.shift,Fm.subst_eq,substSample,subst_var,PTm.subst_zero]
  exact Prf.impE (rollback f (raised (raised p)) (var 1) (var 0)) Prf.hyp0

private theorem prefixToEventual (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .prefixZero p ⟶ tests f .eventual p) := by
  apply Prf.impI
  apply Prf.exI zero
  apply Prf.allI
  simp only [Fm.subst_eq,substCount,substAdvance,PTm.subst_succ,PTm.subst_zero,subst_var,
    up_zero,up_one,inst_zero,PTm.shift_zero,raised,upShiftTerm,subst_inst_shift]
  have h := (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .prefixZero p)).shift
  rw [prefixShift] at h
  exact boundAt f (raised p) h (advance zero (succ (var 0)))

private theorem eventualToPoint (p : Fin 4 → PTm n) :
    Prf PRAAx [] (tests f .eventual p ⟶ tests f .pointwise p) := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  rw [pointShift]
  apply Prf.allI
  apply Prf.impE (rollback f (raised (raised p)) (var 0) (var 1))
  exact Prf.allOpen Prf.hyp0

private theorem prefixToSchedule (p : Fin 4 → PTm n) (lag : PR 1) :
    Prf PRAAx [] (tests f .prefixZero p ⟶ tests f (.schedule lag) p) := by
  apply Prf.impI
  apply Prf.allI
  have h := (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := tests f .prefixZero p)).shift
  rw [prefixShift] at h
  exact boundAt f (raised p) h (advance (app lag (fun _ => var 0)) (succ (var 0)))

private theorem scheduleToPoint (p : Fin 4 → PTm n) (lag : PR 1) :
    Prf PRAAx [] (tests f (.schedule lag) p ⟶ tests f .pointwise p) := by
  apply Prf.impI
  apply Prf.allI
  apply Prf.impE (rollback f (raised p) (var 0) (app lag (fun _ => var 0)))
  exact Prf.allOpen Prf.hyp0

/-- This lag samples the count at 1, 4, 9, 16, ... . -/
def squareLag : PR 1 :=
  PacketLanguage.program ["j"] <| PacketLanguage.v "j" * PacketLanguage.v "j" + PacketLanguage.v "j"

theorem equivalence (form : Form) (p : Fin 4 → PTm n) :
    Prf PRAAx [] (Fm.iff (tests f .pointwise p) (tests f form p)) := by
  have hi := pointToInvariant f p
  have hc := invariantToPrefix f p
  have hp := prefixToPoint f p
  cases form with
  | pointwise => exact Prf.iffRefl _
  | schedule lag =>
    exact Prf.iffI (Prf.impTrans hi (Prf.impTrans hc (prefixToSchedule f p lag)))
      (scheduleToPoint f p lag)
  | cofinal => exact Prf.iffI (Prf.impTrans hi (Prf.impTrans hc (prefixToCofinal f p))) (cofinalToPoint f p)
  | eventual => exact Prf.iffI (Prf.impTrans hi (Prf.impTrans hc (prefixToEventual f p))) (eventualToPoint f p)
  | prefixZero => exact Prf.iffI (Prf.impTrans hi hc) hp
  | invariant => exact Prf.iffI hi (Prf.impTrans hc hp)
  | stationary => exact Prf.iffSymm (allCongr (stationaryAt f (raised p) (var 0)))
  | noFirst => exact Prf.iffI (pointToNoFirst f p) (Prf.impTrans (noFirstToInvariant f p)
      (Prf.impTrans hc hp))


/-- RH, GRH and ERH are closed with zero, one and four additional parameters. -/
def RH (form : Form) : Fm PTm 0 := tests RiemannIPRA.excess form
  (fields zero zero zero (succ zero))

def GRH (form : Form) : Fm PTm 0 := .all (tests RiemannIPRA.excess form
  (fields (var 0) zero zero (succ zero)))

def ERH (form : Form) : Fm PTm 0 := .all (.all (.all (.all
  (tests RiemannIPRA.excess form (fields (var 3) (var 2) (var 1) (var 0))))))

private theorem pointRH : RH .pointwise = RiemannIPRA.RH := by
  simp [RH,tests,RiemannIPRA.RH,RHHierarchy.RHOf,RHHierarchy.atom,raised,sample,fields]
  rfl

private theorem pointGRH : GRH .pointwise = RiemannIPRA.GRH := by
  simp [GRH,tests,RiemannIPRA.GRH,RHHierarchy.GRHOf,RHHierarchy.atom,raised,sample,fields]
  rfl

private theorem pointERH : ERH .pointwise = RiemannIPRA.ERH := by
  simp [ERH,tests,RiemannIPRA.ERH,RHHierarchy.ERHOf,RHHierarchy.atom,raised,sample,fields]
  rfl

theorem rh_iff (form : Form) : Prf PRAAx [] (Fm.iff RiemannIPRA.RH (RH form)) := by
  rw [← pointRH]
  exact equivalence _ form _

theorem grh_iff (form : Form) : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH (GRH form)) := by
  rw [← pointGRH]
  exact allCongr (equivalence _ form _)

theorem erh_iff (form : Form) : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH (ERH form)) := by
  rw [← pointERH]
  exact allCongr (allCongr (allCongr (allCongr (equivalence _ form _))))

/-! ### Extracting an actual first failure -/

private def choose : PR 3 := .prec (.proj 0) (.proj 3)

private def chooseAt (z a b : PTm n) : PTm n := app choose (Fin.cases z (Fin.cases a (fun _ => b)))

@[simp] private theorem substChoose (σ : Fin n → PTm m) (z a b : PTm n) :
    subst σ (chooseAt z a b) = chooseAt (subst σ z) (subst σ a) (subst σ b) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i))

private theorem choose0 (a b : PTm n) : Prf PRAAx Γ (chooseAt zero a b ≐ a) :=
  Prf.eqTrans (PRA.precZero _ _ (Fin.cases a (fun _ => b))) (PRA.proj 0 _)

private theorem chooseS (z a b : PTm n) : Prf PRAAx Γ (chooseAt (succ z) a b ≐ b) :=
  Prf.eqTrans (PRA.precSucc _ _ z (Fin.cases a (fun _ => b))) (PRA.proj 3 _)

private theorem chooseNonzero (z a b : PTm n) :
    Prf PRAAx Γ (RHCounterexamples.neg (z ≐ zero) ⟶ (chooseAt z a b ≐ b)) := by
  let P : Fm PTm (n+1) :=
    RHCounterexamples.neg (var 0 ≐ zero) ⟶ (chooseAt (var 0) (Syn.shift a) (Syn.shift b) ≐ Syn.shift b)
  have hi : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨⟨trivial,trivial⟩,trivial⟩
    · simp [P,RHCounterexamples.neg]
      exact Prf.impI (Prf.botE _ (Prf.impE Prf.hyp0 (Prf.eqRefl zero)))
    · simp [P,RHCounterexamples.neg]
      exact Prf.impI (chooseS _ _ _)
  simpa [P,RHCounterexamples.neg] using Prf.allE z hi

private def firstStep (g : PR 5) : PR 6 :=
  .comp choose (Fin.cases (select (counts g) (tuple5 0 2 3 4 5))
    (Fin.cases (.proj 0) (fun _ => .proj 1)))

/-- Retain the last index whose incoming count is zero, initialized at zero. -/
def firstIndex (g : PR 5) : PR 5 := .prec PacketLanguage.zeroR (firstStep g)

def firstAt (p : Fin 4 → PTm n) (j : PTm n) : PTm n :=
  app (firstIndex f) (Fin.cases j p)

@[simp] private theorem substFirst (σ : Fin n → PTm m) (p : Fin 4 → PTm n) (j : PTm n) :
    subst σ (firstAt f p j) = firstAt f (fun i => subst σ (p i)) (subst σ j) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))

private theorem firstS (p : Fin 4 → PTm n) (j : PTm n) :
    Prf PRAAx Γ (firstAt f p (succ j) ≐ chooseAt (countAt f p j) j (firstAt f p j)) := by
  let xs : Fin 6 → PTm n := Fin.cases j (Fin.cases (firstAt f p j) p)
  apply Prf.eqTrans (PRA.precSucc _ _ j p)
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply appCongr choose
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i)
  · apply Prf.eqTrans (evalSelect (counts f) _ xs)
    apply appCongr (counts f)
    exact Fin.cases (Prf.eqRefl _) (fun i => Fin.cases (Prf.eqRefl _) (fun j =>
      Fin.cases (Prf.eqRefl _) (fun k => Fin.cases (Prf.eqRefl _)
        (fun a => Fin.cases (Prf.eqRefl _) (fun t => t.elim0) a) k) j) i)
  · exact PRA.proj 0 xs
  · exact PRA.proj 1 xs

private theorem firstClean (p : Fin 4 → PTm n) (j : PTm n)
    (h : Prf PRAAx Γ (countAt f p j ≐ zero)) : Prf PRAAx Γ (firstAt f p (succ j) ≐ j) := by
  apply Prf.eqTrans (firstS f p j)
  apply Prf.eqTrans _ (choose0 j (firstAt f p j))
  exact appCongr choose (Fin.cases h (fun _ => Prf.eqRefl _))

private theorem firstDirty (p : Fin 4 → PTm n) (j : PTm n)
    (h : Prf PRAAx Γ (RHCounterexamples.neg (countAt f p j ≐ zero))) :
    Prf PRAAx Γ (firstAt f p (succ j) ≐ firstAt f p j) :=
  Prf.eqTrans (firstS f p j) (Prf.impE (chooseNonzero _ _ _) h)

def firstFailure (p : Fin 4 → PTm n) (j : PTm n) :=
  (countAt f p j ≐ zero) ⋏ RHCounterexamples.neg (sample f p j ≐ zero)

@[simp] private theorem substFailure (σ : Fin n → PTm m) (p : Fin 4 → PTm n) (j : PTm n) :
    (firstFailure f p j).subst σ = firstFailure f (fun i => subst σ (p i)) (subst σ j) := by
  simp [firstFailure,RHCounterexamples.neg]

private theorem moveFailure (p : Fin 4 → PTm n) {j k : PTm n}
    (eq : Prf PRAAx Γ (j ≐ k)) (h : Prf PRAAx Γ (firstFailure f p j)) :
    Prf PRAAx Γ (firstFailure f p k) := by
  let P := firstFailure f (raised p) (var 0)
  have hj : Prf PRAAx Γ (P.subst (inst j)) := by simpa [P,raised] using h
  simpa [P,raised] using Prf.eqSubst1 P eq hj

private theorem extractStep (p : Fin 4 → PTm n) (j : PTm n)
    (ih : Prf PRAAx Γ (RHCounterexamples.neg (countAt f p j ≐ zero) ⟶
      firstFailure f p (firstAt f p j))) :
    Prf PRAAx Γ (RHCounterexamples.neg (countAt f p (succ j) ≐ zero) ⟶
      firstFailure f p (firstAt f p (succ j))) := by
  apply Prf.impI
  apply Prf.orE (RHCounterexamples.zero_decidable (countAt f p j))
  · apply moveFailure f p (Prf.eqSymm (firstClean f p j Prf.hyp0))
    apply Prf.andI Prf.hyp0
    apply Prf.impI
    apply Prf.impE (Prf.hyp (by simp) : Prf PRAAx _ (RHCounterexamples.neg (countAt f p (succ j) ≐ zero)))
    exact Prf.iffMpr (atSuccessor f p j) (Prf.andI Prf.hyp0 Prf.hyp1)
  · exact moveFailure f p (Prf.eqSymm (firstDirty f p j Prf.hyp0))
      (Prf.impE ih.wk.wk Prf.hyp0)

/-- A dirty prefix supplies an explicit primitive-recursively computed first
failure. Its defining correctness invariant is quantifier-free. -/
theorem extractFirst (p : Fin 4 → PTm n) (j : PTm n) :
    Prf PRAAx Γ (RHCounterexamples.neg (countAt f p j ≐ zero) ⟶
      firstFailure f p (firstAt f p j)) := by
  let P : Fm PTm (n+1) := RHCounterexamples.neg (countAt f (raised p) (var 0) ≐ zero) ⟶
    firstFailure f (raised p) (firstAt f (raised p) (var 0))
  have hi : Prf PRAAx Γ (.all P) := by
    apply PRA.qfInd P
    · exact ⟨⟨trivial,trivial⟩,⟨trivial,⟨trivial,trivial⟩⟩⟩
    · simp [P,raised,RHCounterexamples.neg]
      exact Prf.impI (Prf.botE _ (Prf.impE Prf.hyp0 (count0 f p)))
    · simp only [P,RHCounterexamples.neg,Fm.subst_imp,Fm.subst_bot,Fm.subst_eq,PTm.subst_zero,
        substFailure,substFirst,substCount,subst_var,repl_zero,raised,replShift]
      exact extractStep f (raised p) (var 0) Prf.hyp0
  simpa [P,raised,RHCounterexamples.neg] using Prf.allE j hi

def anyFailure (p : Fin 4 → PTm n) : Fm PTm n :=
  .ex (RHCounterexamples.neg (sample f (raised p) (var 0) ≐ zero))

def earliestFailure (p : Fin 4 → PTm n) : Fm PTm n :=
  .ex (firstFailure f (raised p) (var 0))

/-- Equivalence with witnesses in both directions, before taking any negation. -/
theorem failure_iff_first (p : Fin 4 → PTm n) :
    Prf PRAAx [] (Fm.iff (anyFailure f p) (earliestFailure f p)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (firstAt f (raised p) (succ (var 0)))
    simp only [substFailure,subst_var,up_zero,inst_zero,raised,
      upShiftTerm,subst_inst_shift]
    apply Prf.impE (extractFirst f (raised p) (succ (var 0)))
    apply Prf.impI
    exact Prf.impE Prf.hyp1 (Prf.andE₁ (Prf.iffMp (atSuccessor f (raised p) (var 0)) Prf.hyp0))
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    exact Prf.andE₂ Prf.hyp0


private theorem exCongr {A B : Fm PTm (n+1)} (h : Prf PRAAx [] (Fm.iff A B)) :
    Prf PRAAx [] (Fm.iff (Fm.ex A) (Fm.ex B)) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    exact Prf.iffMp (Prf.ofNil h) Prf.hyp0
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    apply Prf.exI (var 0)
    simp only [Fm.subst_up_succ_inst]
    exact Prf.iffMpr (Prf.ofNil h) Prf.hyp0

/-- For a counterexample to a family, keep its polynomial parameters and
extract the first failing cutoff for those parameters. -/
def rhFirst : Fm PTm 0 := earliestFailure RiemannIPRA.excess (fields zero zero zero (succ zero))
def grhFirst : Fm PTm 0 := .ex (earliestFailure RiemannIPRA.excess
  (fields (var 0) zero zero (succ zero)))
def erhFirst : Fm PTm 0 := .ex (.ex (.ex (.ex (earliestFailure RiemannIPRA.excess
  (fields (var 3) (var 2) (var 1) (var 0))))))

theorem rh_counter_iff_first :
    Prf PRAAx [] (Fm.iff (RHCounterexamples.counter RiemannIPRA.RH) rhFirst) := by
  rw [← pointRH]
  exact failure_iff_first _ _

theorem grh_counter_iff_first :
    Prf PRAAx [] (Fm.iff (RHCounterexamples.counter RiemannIPRA.GRH) grhFirst) := by
  rw [← pointGRH]
  exact exCongr (failure_iff_first _ _)

theorem erh_counter_iff_first :
    Prf PRAAx [] (Fm.iff (RHCounterexamples.counter RiemannIPRA.ERH) erhFirst) := by
  rw [← pointERH]
  exact exCongr (exCongr (exCongr (exCongr (failure_iff_first _ _))))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketAudit

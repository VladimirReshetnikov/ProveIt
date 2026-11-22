import IPRADerivations.AnalyticNumberTheory.Riemann.Hypotheses
import IPRADerivations.AnalyticNumberTheory.Riemann.RHCounterexamples

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`SlackForms.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Object-level arithmetic proof that a monus comparison admits a positive
additive slack, with a fixed PR term computing the witness. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketSlack
open LeanProofs.ConciseIPRA Syn PacketLanguage
open PTm (app zero succ)
open scoped Fm
variable {n m k : Nat} {Γ : List (Fm PTm n)}
private abbrev Eql (Γ : List (Fm PTm n)) (a b : PTm n) := Prf PRAAx Γ (a ≐ b)

private def args {α : Type} (a b : α) : Fin 2 → α := Fin.cases a (fun _ => b)
private def bin (f : PR 2) (a b : PTm n) := app f (args a b)
private def unary (f : PR 1) (a : PTm n) := app f (fun _ => a)

@[simp] private theorem subBin (σ : Fin n → PTm m) (f : PR 2) (a b : PTm n) :
    subst σ (bin f a b) = bin f (subst σ a) (subst σ b) := by
  apply congrArg (app _)
  exact funext (Fin.cases rfl (fun _ => rfl))
@[simp] private theorem subUnary (σ : Fin n → PTm m) (f : PR 1) (a : PTm n) :
    subst σ (unary f a) = unary f (subst σ a) := rfl
@[simp] private theorem replShift (u : PTm (n+1)) (t : PTm n) :
    subst (repl u) (Syn.shift t) = Syn.shift t := by rw [Syn.subst_shift]; rfl

private theorem appCongr (f : PR k) {xs ys : Fin k → PTm n}
    (h : ∀ i, Eql Γ (xs i) (ys i)) : Eql Γ (app f xs) (app f ys) := by
  simpa using Prf.eqCongr (app f (var : Fin k → PTm k)) h

private theorem both (f : PR 2) {a A b B : PTm n} (h : Eql Γ a A) (g : Eql Γ b B) :
    Eql Γ (bin f a b) (bin f A B) := appCongr f (Fin.cases h (fun _ => g))
private theorem one (f : PR 1) {a A : PTm n} (h : Eql Γ a A) :
    Eql Γ (unary f a) (unary f A) := appCongr f (fun _ => h)
private theorem sc {a b : PTm n} (h : Eql Γ a b) : Eql Γ (succ a) (succ b) :=
  appCongr .succ (fun _ => h)

local notation:65 a:66 " +ᵒ " b:66 => bin addR a b
local notation:65 a:66 " ⊖ " b:66 => bin reversedSub b a
local notation "pd" => unary predR

private theorem add0 (a : PTm n) : Eql Γ (zero +ᵒ a) a :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => a)) (PRA.proj 0 _)
private theorem addS (x a : PTm n) : Eql Γ (succ x +ᵒ a) (succ (x +ᵒ a)) :=
  Prf.eqTrans (PRA.precSucc _ _ x (fun _ => a)) (Prf.eqTrans (PRA.comp _ _ _)
    (sc (PRA.proj 1 _)))

private theorem sub0 (a : PTm n) : Eql Γ (a ⊖ zero) a :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => a)) (PRA.proj 0 _)
private theorem subS (x a : PTm n) : Eql Γ (a ⊖ succ x) (pd (a ⊖ x)) :=
  Prf.eqTrans (PRA.precSucc _ _ x (fun _ => a)) (Prf.eqTrans (PRA.comp _ _ _)
    (one predR (PRA.proj 1 _)))

private theorem pred0 : Eql Γ (pd zero) zero := by
  apply Prf.eqTrans _ (PRA.precZero .zero (.proj 0) Fin.elim0)
  exact appCongr predR (Fin.cases (Prf.eqRefl _) (fun i => i.elim0))

private theorem predS (x : PTm n) : Eql Γ (pd (succ x)) x := by
  apply Prf.eqTrans _ (Prf.eqTrans (PRA.precSucc .zero (.proj 0) x Fin.elim0) (PRA.proj 0 _))
  exact appCongr predR (Fin.cases (Prf.eqRefl _) (fun i => i.elim0))

-- A small tactic performs substitution into the explicitly displayed QF
-- induction formula. Its remaining goals are ordinary object derivations.
macro "qf_intro" P:term " using " t:term : tactic => `(tactic|
  (let predic := $P
   suffices hall : Prf PRAAx _ (.all predic) by simpa [predic] using Prf.allE $t hall
   apply PRA.qfInd predic
   · repeat' first | trivial | constructor
   all_goals simp only [predic,Fm.subst_eq,Fm.subst_imp,Fm.subst_and,Fm.subst_or,
      Fm.subst_bot,subBin,subUnary,subst_var,PTm.subst_zero,PTm.subst_succ,
      inst_zero,subst_inst_shift,repl_zero,replShift]))

private theorem addRight0 (t : PTm n) : Eql Γ (t +ᵒ zero) t := by
  qf_intro ((var 0 : PTm (n+1)) +ᵒ zero ≐ var 0) using t
  · exact add0 _
  · exact Prf.eqTrans (addS _ _) (sc Prf.hyp0)

private theorem addRightS (t a : PTm n) : Eql Γ (t +ᵒ succ a) (succ (t +ᵒ a)) := by
  qf_intro ((var 0 : PTm (n+1)) +ᵒ succ (Syn.shift a) ≐ succ (var 0 +ᵒ Syn.shift a)) using t
  · exact Prf.eqTrans (add0 _) (Prf.eqSymm (sc (add0 _)))
  · exact Prf.eqTrans (addS _ _) (sc (Prf.eqTrans Prf.hyp0 (Prf.eqSymm (addS _ _))))

private theorem subBothS (t a : PTm n) : Eql Γ (succ a ⊖ succ t) (a ⊖ t) := by
  qf_intro (succ (Syn.shift a) ⊖ succ (var 0 : PTm (n+1)) ≐ Syn.shift a ⊖ var 0) using t
  · exact Prf.eqTrans (subS _ _) (Prf.eqTrans (one predR (sub0 _))
      (Prf.eqTrans (predS _) (Prf.eqSymm (sub0 _))))
  · exact Prf.eqTrans (subS _ _) (Prf.eqTrans (one predR Prf.hyp0) (Prf.eqSymm (subS _ _)))

private theorem subSelf (t : PTm n) : Eql Γ (t ⊖ t) zero := by
  qf_intro ((var 0 : PTm (n+1)) ⊖ var 0 ≐ zero) using t
  · exact sub0 _
  · exact Prf.eqTrans (subBothS _ _) Prf.hyp0

private theorem subSlack (w a : PTm n) : Eql Γ (a ⊖ (w +ᵒ a)) zero := by
  qf_intro (Syn.shift a ⊖ ((var 0 : PTm (n+1)) +ᵒ Syn.shift a) ≐ zero) using w
  · exact Prf.eqTrans (both reversedSub (add0 _) (Prf.eqRefl _)) (subSelf _)
  · exact Prf.eqTrans (both reversedSub (addS _ _) (Prf.eqRefl _)) (Prf.eqTrans
      (subS _ _) (Prf.eqTrans (one predR Prf.hyp0) pred0))


private theorem splitPred (x : PTm n) :
    Prf PRAAx Γ ((x ≐ zero) ⋎ (x ≐ succ (pd x))) := by
  qf_intro (((var 0 : PTm (n+1)) ≐ zero) ⋎ (var 0 ≐ succ (pd (var 0)))) using x
  · exact Prf.orI₁ (Prf.eqRefl _)
  · exact Prf.orI₂ (Prf.eqSymm (sc (predS _)))

private def select₃ : PR 3 := .prec (.proj 0) (.proj 3)
private def tern {α} (a b c : α) : Fin 3 → α := Fin.cases a (Fin.cases b (fun _ => c))
private def pick (x a b : PTm n) := app select₃ (tern x a b)
private theorem pick0 (a b : PTm n) : Eql Γ (pick zero a b) a :=
  Prf.eqTrans (PRA.precZero _ _ (args a b)) (PRA.proj 0 _)
private theorem pickS (z a b : PTm n) : Eql Γ (pick (succ z) a b) b :=
  Prf.eqTrans (PRA.precSucc _ _ z (args a b)) (PRA.proj 3 _)
private theorem pickCongr {u v : PTm n} (a b : PTm n) (h : Eql Γ u v) :
    Eql Γ (pick u a b) (pick v a b) := appCongr _ (Fin.cases h (fun _ => Prf.eqRefl _))

private def residual : PR 3 := .comp reversedSub (args (.proj 0) (.proj 2))
private def update : PR 3 := .comp select₃ (tern residual (sucR (.proj 1)) (.proj 1))

/-- Counts steps after the residual has reached zero, with b first, a second. -/
def slack : PR 2 := .prec zeroR update

private theorem slack0 (a : PTm n) : Eql Γ (bin slack zero a) zero := by
  apply Prf.eqTrans (PRA.precZero _ _ (fun _ => a))
  apply Prf.eqTrans (PRA.comp _ _ _)
  exact appCongr PR.zero (fun i => i.elim0)

private theorem slackS (b a : PTm n) : Eql Γ (bin slack (succ b) a)
    (pick (a ⊖ b) (succ (bin slack b a)) (bin slack b a)) := by
  let xs := tern b (bin slack b a) a
  apply Prf.eqTrans (PRA.precSucc _ _ b (fun _ => a))
  apply Prf.eqTrans (PRA.comp _ _ xs)
  apply appCongr _
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i)
  · exact Prf.eqTrans (PRA.comp _ _ xs) (appCongr reversedSub (Fin.cases (PRA.proj 0 xs) (fun _ => PRA.proj 2 xs)))
  · exact Prf.eqTrans (PRA.comp _ _ xs) (sc (PRA.proj 1 xs))
  · exact PRA.proj 1 xs

private theorem invariantStep (b a : PTm n)
    (ih : Eql Γ ((a ⊖ b) +ᵒ b) (bin slack b a +ᵒ a)) :
    Eql Γ ((a ⊖ succ b) +ᵒ succ b) (bin slack (succ b) a +ᵒ a) := by
  let r := a ⊖ b
  let w := bin slack b a
  let w' := bin slack (succ b) a
  apply Prf.orE (splitPred r)
  · have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := r ≐ zero)
    have hrem : Eql _ (a ⊖ succ b) r :=
      Prf.eqTrans (subS _ _) (Prf.eqTrans (one predR h) (Prf.eqTrans pred0 (Prf.eqSymm h)))
    have hw : Eql _ w' (succ w) := Prf.eqTrans (slackS _ _)
      (Prf.eqTrans (pickCongr _ _ h) (pick0 _ _))
    exact Prf.eqTrans (both addR hrem (Prf.eqRefl _)) (Prf.eqTrans (addRightS r b) (Prf.eqTrans
      (sc ih.wk) (Prf.eqSymm (Prf.eqTrans (both addR hw (Prf.eqRefl _)) (addS _ _)))))
  · have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := r ≐ succ (pd r))
    have hw : Eql _ w' w := Prf.eqTrans (slackS _ _) (Prf.eqTrans (pickCongr _ _ h) (pickS _ _ _))
    have left : Eql _ ((a ⊖ succ b) +ᵒ succ b) (r +ᵒ b) :=
      Prf.eqTrans (both addR (subS _ _) (Prf.eqRefl _)) (Prf.eqTrans (addRightS _ _)
        (Prf.eqSymm (Prf.eqTrans (both addR h (Prf.eqRefl _)) (addS _ _))))
    exact Prf.eqTrans left (Prf.eqTrans ih.wk (Prf.eqSymm (both addR hw (Prf.eqRefl _))))

private theorem invariant (b a : PTm n) : Eql Γ ((a ⊖ b) +ᵒ b) (bin slack b a +ᵒ a) := by
  qf_intro (((Syn.shift a ⊖ (var 0 : PTm (n+1))) +ᵒ var 0) ≐
    (bin slack (var 0) (Syn.shift a) +ᵒ Syn.shift a)) using b
  · exact Prf.eqTrans (both addR (sub0 a) (Prf.eqRefl _)) (Prf.eqTrans (addRight0 _)
      (Prf.eqSymm (Prf.eqTrans (both addR (slack0 a) (Prf.eqRefl _)) (add0 a))))
  · exact invariantStep _ _ Prf.hyp0

private theorem swapSub (a b : PTm n) : Eql Γ (bin subR a b) (a ⊖ b) :=
  Prf.eqTrans (PRA.comp _ _ (args a b))
    (appCongr reversedSub (Fin.cases (PRA.proj 1 (args a b)) (fun _ => PRA.proj 0 (args a b))))

/-- Primitive-recursive subtraction vanishes iff there is a positive-form
additive certificate. Zero is allowed as the slack. -/
theorem monus_iff_slack (a b : PTm n) :
    Prf PRAAx Γ (Fm.iff (bin subR a b ≐ zero)
      (.ex (bin addR (var 0) (Syn.shift a) ≐ Syn.shift b))) := by
  apply Prf.iffI
  · apply Prf.impI
    apply Prf.exI (bin slack b a)
    simp only [Fm.subst_eq,subBin,subst_var,inst_zero,subst_inst_shift]
    have hr := Prf.eqTrans (Prf.eqSymm (swapSub a b)) (Prf.hyp0 (Ax := PRAAx) (Γ := Γ)
      (φ := bin subR a b ≐ zero))
    exact Prf.eqTrans (Prf.eqSymm (invariant b a))
      (Prf.eqTrans (both addR hr (Prf.eqRefl _)) (add0 b))
  · apply Prf.impI
    apply Prf.exE Prf.hyp0
    simp only [Fm.shift,Fm.subst_eq,subBin,PTm.subst_zero]
    apply Prf.eqTrans (swapSub _ _)
    apply Prf.eqTrans _ (subSlack (var 0) (Syn.shift a))
    exact both reversedSub (Prf.eqSymm Prf.hyp0) (Prf.eqRefl _)


private abbrev inputCtx := ["degreeOffset","H","u","v","start"]
private def components : E inputCtx × E inputCtx :=
  let d := v "degreeOffset"+1
  let n := v "start"+100
  (powE (call RiemannIPRA.dyadicGap [d,v "H",v "u",v "v",n]) 2,
    n * powE (call RiemannIPRA.allowance [d,v "H",n]) 2)

/-- The two sides of the square discrepancy first-order packet from Hypotheses. -/
def leftCode : PR 5 := program inputCtx components.1
def rightCode : PR 5 := program inputCtx components.2

private theorem readExcess (xs : Fin 5 → PTm n) : Eql Γ (app RiemannIPRA.excess xs)
    (bin subR (app leftCode xs) (app rightCode xs)) := by
  apply Prf.eqTrans (PRA.comp _ _ xs)
  exact appCongr subR (Fin.cases (Prf.eqRefl _) (fun i =>
    Fin.cases (Prf.eqRefl _) (fun j => j.elim0) i))

private def fields (d H u v t : PTm n) : Fin 5 → PTm n :=
  Fin.cases d (Fin.cases H (Fin.cases u (Fin.cases v (fun _ => t))))

def witnessAtom (d H u v t : PTm n) : Fm PTm n :=
  let xs := fields d H u v t
  .ex (bin addR (var 0) (Syn.shift (app leftCode xs)) ≐ Syn.shift (app rightCode xs))

theorem atom_iff_slack (d H u v t : PTm n) :
    Prf PRAAx Γ (Fm.iff (RHHierarchy.atom RiemannIPRA.excess d H u v t) (witnessAtom d H u v t)) := by
  let xs := fields d H u v t
  have he := readExcess (Γ := Γ) xs
  have hs := monus_iff_slack (Γ := Γ) (app leftCode xs) (app rightCode xs)
  exact Prf.iffI (Prf.impI (Prf.iffMp hs.wk (Prf.eqTrans (Prf.eqSymm he.wk) Prf.hyp0)))
    (Prf.impI (Prf.eqTrans he.wk (Prf.iffMpr hs.wk Prf.hyp0)))

private theorem allCongr {A B : Fm PTm (n+1)} (h : Prf PRAAx [] (Fm.iff A B)) :
    Prf PRAAx [] (Fm.iff (.all A) (.all B)) :=
  Prf.iffI (Prf.impI (Prf.allI (Prf.iffMp (Prf.ofNil h) (Prf.allOpen Prf.hyp0))))
    (Prf.impI (Prf.allI (Prf.iffMpr (Prf.ofNil h) (Prf.allOpen Prf.hyp0))))

def RH : Fm PTm 0 := .all (witnessAtom zero zero zero (succ zero) (var 0))
def GRH : Fm PTm 0 := .all (.all (witnessAtom (var 1) zero zero (succ zero) (var 0)))
def ERH : Fm PTm 0 := .all (.all (.all (.all (.all
  (witnessAtom (var 4) (var 3) (var 2) (var 1) (var 0))))))

theorem rh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.RH RH) :=
  allCongr (atom_iff_slack _ _ _ _ _)
theorem grh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH GRH) :=
  allCongr (allCongr (atom_iff_slack _ _ _ _ _))
theorem erh_iff : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH ERH) :=
  allCongr (allCongr (allCongr (allCongr (allCongr (atom_iff_slack _ _ _ _ _)))))


private theorem inject (x y : PTm n) (h : Eql Γ (succ x) (succ y)) : Eql Γ x y := by
  have hh := Prf.ax (Γ := Γ) PRAAx.succInj (args x y)
  exact Prf.impE (by simpa [args] using hh) h

private theorem cancel (z x y : PTm n) : Prf PRAAx Γ (((x +ᵒ z) ≐ (y +ᵒ z)) ⟶ (x ≐ y)) := by
  qf_intro (((Syn.shift x +ᵒ (var 0 : PTm (n+1))) ≐ (Syn.shift y +ᵒ var 0)) ⟶
    (Syn.shift x ≐ Syn.shift y)) using z
  · exact Prf.impI (Prf.eqTrans (Prf.eqSymm (addRight0 _)) (Prf.eqTrans Prf.hyp0 (addRight0 _)))
  · apply Prf.impI
    apply Prf.impE Prf.hyp1
    exact inject _ _ (Prf.eqTrans (Prf.eqSymm (addRightS _ _)) (Prf.eqTrans Prf.hyp0 (addRightS _ _)))

inductive Certificate where
  | calculated | unique

private def uniqueFor (a b w : PTm n) : Fm PTm n := .all
  (((var 0 +ᵒ Syn.shift a) ≐ Syn.shift b) ⟶ (var 0 ≐ Syn.shift w))

private theorem uniqueness (a b w : PTm n) (h : Eql Γ (w +ᵒ a) b) : Prf PRAAx Γ (uniqueFor a b w) := by
  apply Prf.allI
  apply Prf.impI
  apply Prf.impE (cancel (Syn.shift a) (var 0) (Syn.shift w))
  have hw := Prf.shift h
  simp only [Fm.shift,Fm.subst_eq,subBin] at hw
  exact Prf.eqTrans Prf.hyp0 (Prf.eqSymm hw.wk)

def claim (style : Certificate) (a b : PTm n) : Fm PTm n := match style with
  | .calculated => (bin slack b a +ᵒ a) ≐ b
  | .unique => .ex (((var 0 +ᵒ Syn.shift a) ≐ Syn.shift b) ⋏
      uniqueFor (Syn.shift a) (Syn.shift b) (var 0))

private theorem writeCanonical (a b : PTm n) (h : Eql Γ (bin subR a b) zero) :
    Eql Γ (bin slack b a +ᵒ a) b :=
  Prf.eqTrans (Prf.eqSymm (invariant b a)) (Prf.eqTrans
    (both addR (Prf.eqTrans (Prf.eqSymm (swapSub a b)) h) (Prf.eqRefl _)) (add0 b))

private theorem withUnique (a b w : PTm n) (h : Eql Γ (w +ᵒ a) b) : Prf PRAAx Γ (claim .unique a b) := by
  apply Prf.exI w
  apply Prf.andI
  · simpa only [Fm.subst_eq,subBin,subst_var,inst_zero,subst_inst_shift] using h
  · have sh (s : PTm n) : subst (up (inst w)) (Syn.shift (Syn.shift s)) = Syn.shift s := by
      simp [Syn.subst_shift]
      rfl
    simpa only [uniqueFor,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subBin,subst_var,
      Syn.up_zero,sh,Syn.shift_var,up_succ,inst_zero] using uniqueness a b w h

theorem monus_iff_certificate (style : Certificate) (a b : PTm n) :
    Prf PRAAx Γ (Fm.iff (bin subR a b ≐ zero) (claim style a b)) := by
  apply Prf.iffI
  · apply Prf.impI
    have h := writeCanonical a b (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := bin subR a b ≐ zero))
    cases style with
    | calculated => exact h
    | unique => exact withUnique a b _ h
  · apply Prf.impI
    apply Prf.iffMpr (monus_iff_slack a b)
    cases style with
    | calculated =>
      apply Prf.exI (bin slack b a)
      simp only [Fm.subst_eq,subBin,subst_var,inst_zero,subst_inst_shift]
      exact Prf.hyp0
    | unique =>
      apply Prf.exE Prf.hyp0
      apply Prf.exI (var 0)
      simp only [Fm.subst_up_succ_inst]
      exact Prf.andE₁ Prf.hyp0

def certAtom (style : Certificate) (d H u v t : PTm n) : Fm PTm n :=
  let xs := fields d H u v t
  claim style (app leftCode xs) (app rightCode xs)

private theorem atom_iff_cert (style : Certificate) (d H u v t : PTm n) :
    Prf PRAAx Γ (Fm.iff (RHHierarchy.atom RiemannIPRA.excess d H u v t) (certAtom style d H u v t)) := by
  let xs := fields d H u v t
  have he := readExcess (Γ := Γ) xs
  have hs := monus_iff_certificate (Γ := Γ) style (app leftCode xs) (app rightCode xs)
  exact Prf.iffI (Prf.impI (Prf.iffMp hs.wk (Prf.eqTrans (Prf.eqSymm he.wk) Prf.hyp0)))
    (Prf.impI (Prf.eqTrans he.wk (Prf.iffMpr hs.wk Prf.hyp0)))

def certRH (style : Certificate) : Fm PTm 0 := .all (certAtom style zero zero zero (succ zero) (var 0))
def certGRH (style : Certificate) : Fm PTm 0 := .all (.all (certAtom style (var 1) zero zero (succ zero) (var 0)))
def certERH (style : Certificate) : Fm PTm 0 := .all (.all (.all (.all (.all
  (certAtom style (var 4) (var 3) (var 2) (var 1) (var 0))))))

theorem rh_iff_cert (style : Certificate) : Prf PRAAx [] (Fm.iff RiemannIPRA.RH (certRH style)) :=
  allCongr (atom_iff_cert _ _ _ _ _ _)
theorem grh_iff_cert (style : Certificate) : Prf PRAAx [] (Fm.iff RiemannIPRA.GRH (certGRH style)) :=
  allCongr (allCongr (atom_iff_cert _ _ _ _ _ _))
theorem erh_iff_cert (style : Certificate) : Prf PRAAx [] (Fm.iff RiemannIPRA.ERH (certERH style)) :=
  allCongr (allCongr (allCongr (allCongr (allCongr (atom_iff_cert _ _ _ _ _ _)))))

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.PacketSlack

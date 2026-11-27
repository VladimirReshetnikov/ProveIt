import IPRADerivations.Foundations.FiniteObservations.MetricKernel

/-! Imported from the packet `foundations/finite_observations_ipra_2026-11-20`, `lean/UniformMinimum.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! One-sided minimum transfer with object-variable horizons. For fixed
numerical score programs f and g, the sentence quantifies over both last
indices, the two data parameters, and the allowed error. A match is opened
locally by existential elimination. No selector for the covering map is used. -/
namespace LeanProofs.IPRA.Foundations.FiniteObservations.UniformMinimum
open_ipra exports
variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- One scan step carries the smaller of the previous value and the new score. -/
def minStep (f : PR 2) : PTm 3 := meet (var 1) (ap2 f (succ (var 0)) (var 2))
abbrev minF (f : PR 2) := rec2 (ap2 f zero (var 0)) (minStep f)
/-- The minimum over 0,...,K of f(i,x). -/
abbrev Mn (f : PR 2) (K x : PTm n) := ap2 (minF f) K x

theorem min_zero (f : PR 2) (x : PTm n) :
    Γ ⊢[PRAAx] Mn f zero x ≐ ap2 f zero x := by
  simpa using rec2_zero (Γ := Γ) (ap2 f zero (var 0)) (minStep f) x

theorem min_succ (f : PR 2) (K x : PTm n) :
    Γ ⊢[PRAAx] Mn f (succ K) x ≐ meet (Mn f K x) (ap2 f (succ K) x) := by
  simpa [Mn, minF, minStep, meet] using rec2_succ (Γ := Γ) (ap2 f zero (var 0)) (minStep f) K x

private theorem keep_shift (s : PTm (n+1)) (t : PTm n) :
    Syn.subst (repl s) (Syn.shift t) = Syn.shift t := by
  rw [Syn.subst_shift]; simp only [Syn.repl_succ]; rfl

/-- Fix the candidate i before induction on the prefix endpoint. -/
theorem min_le (f : PR 2) (K x i : PTm n) (hi : Γ ⊢[PRAAx] le i K) :
    Γ ⊢[PRAAx] le (Mn f K x) (ap2 f i x) := by
  have all : Γ ⊢[PRAAx] Fm.all (le (Syn.shift i) (var 0) ⟶
      le (Mn f (var 0) (Syn.shift x)) (ap2 f (Syn.shift i) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero]
      apply Prf.impI
      have eq : (le i zero :: Γ) ⊢[PRAAx] i ≐ zero := le_antisymm Prf.hyp0 (zero_le _)
      exact le_congr (min_zero f x).eqSymm (congrAp2 f eq.eqSymm (.eqRefl _)) (le_refl _)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, keep_shift]
      apply Prf.impI
      let k : PTm (n+1) := var 0
      let a := Syn.shift i
      let u := Syn.shift x
      let ih := le a k ⟶ le (Mn f k u) (ap2 f a u)
      let Δ := le a (succ k) :: ih :: Γ.map Fm.shift
      have hab : Δ ⊢[PRAAx] le a (succ k) := Prf.hyp0
      refine le_congr (min_succ f k u).eqSymm (.eqRefl _) ?_
      refine .orE (lt_or_eq_of_le hab) ?_ ?_
      · have prior : (lt a (succ k) :: Δ) ⊢[PRAAx] le a k :=
          (succ_monus_succ a k).eqSymm.eqTrans Prf.hyp0
        have ih' : (lt a (succ k) :: Δ) ⊢[PRAAx] ih := Prf.hyp1.wk
        exact le_trans (meet_le_left _ _) (Prf.impE ih' prior)
      · exact le_congr (.eqRefl _) (congrAp2 f Prf.hyp0.eqSymm (.eqRefl _))
          (meet_le_right _ _)
  have h := Prf.allE K all
  simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h
  exact Prf.impE h hi

def Lower (f : PR 2) (H x z e : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift H) ⟶ le (Syn.shift z) (ap2 f (var 0) (Syn.shift x) + Syn.shift e))

theorem lower_at (f : PR 2) (H x z e j : PTm n) (h : Γ ⊢[PRAAx] Lower f H x z e)
    (hj : Γ ⊢[PRAAx] le j H) : Γ ⊢[PRAAx] le z (ap2 f j x + e) := by
  have v := Prf.allE j h
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, Syn.subst_inst_shift,
    Syn.subst_var, Syn.inst_zero] at v
  exact .impE v hj

private theorem up_shift {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  simp [Syn.subst_shift, Syn.shift_subst]

theorem subst_lower {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (H x z e : PTm n) :
    (Lower f H x z e).subst σ = Lower f (Syn.subst σ H) (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ e) := by
  simp only [Lower, Fm.subst_all, Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add,
    up_shift, Syn.subst_var, Syn.up_zero]

/-- The horizon H is frozen. The induction matrix is the quantifier-free
implication j ≤ H → z ≤ Mn(f,j,x) + e, with the quantified premise external
to the induction formula. -/
theorem lower_fold (f : PR 2) (H x z e : PTm n) (h : Γ ⊢[PRAAx] Lower f H x z e) :
    Γ ⊢[PRAAx] le z (Mn f H x + e) := by
  have all : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift H) ⟶
      le (Syn.shift z) (Mn f (var 0) (Syn.shift x) + Syn.shift e)) := by
    refine PRA.qfInd _ ⟨trivial, trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero]
      exact .impI (le_congr (.eqRefl _) (congrAdd (min_zero f x).eqSymm (.eqRefl _))
        (lower_at f H x z e zero h.wk Prf.hyp0))
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, keep_shift]
      apply Prf.impI
      let k : PTm (n+1) := var 0
      let H' := Syn.shift H
      let u := Syn.shift x
      let z' := Syn.shift z
      let e' := Syn.shift e
      let ih := le k H' ⟶ le z' (Mn f k u + e')
      let Δ := le (succ k) H' :: ih :: Γ.map Fm.shift
      have hH : Δ ⊢[PRAAx] le (succ k) H' := Prf.hyp0
      have lo : Δ ⊢[PRAAx] le z' (Mn f k u + e') :=
        .impE Prf.hyp1 (le_trans (le_succ_self k) hH)
      have h' : Δ ⊢[PRAAx] Lower f H' u z' e' := by
        simpa only [Fm.shift, subst_lower, Syn.shift, H', u, z', e', Δ] using h.shift.wk.wk
      have hi := lower_at f H' u z' e' (succ k) h' hH
      refine le_congr (.eqRefl _) (congrAdd (min_succ f k u).eqSymm (.eqRefl _)) ?_
      exact .orE (le_total (Mn f k u) (ap2 f (succ k) u))
        (le_congr (.eqRefl _) (congrAdd (meet_left Prf.hyp0).eqSymm (.eqRefl _)) lo.wk)
        (le_congr (.eqRefl _) (congrAdd (meet_right Prf.hyp0).eqSymm (.eqRefl _)) hi.wk)
  have v := Prf.allE H all
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at v
  exact Prf.impE v (le_refl _)

/-- An index i ≤ K whose score f(i,x) is at most z. -/
def someBelow (f : PR 2) (K x z : PTm n) : Fm PTm n :=
  .ex (le (var 0) (Syn.shift K) ⋏
    le (ap2 f (var 0) (Syn.shift x)) (Syn.shift z))

/-- Seal an attained upper cut into a numerical inequality. -/
theorem minimum_below (f : PR 2) (K x z : PTm n)
    (h : Γ ⊢[PRAAx] someBelow f K x z) :
    Γ ⊢[PRAAx] le (Mn f K x) z := by
  refine .exE h ?_
  let P := le (var 0) (Syn.shift K) ⋏
    le (ap2 f (var 0) (Syn.shift x)) (Syn.shift z)
  let Δ : List (Fm PTm (n+1)) := P :: Γ.map Fm.shift
  have hw : Δ ⊢[PRAAx] P := Prf.hyp0
  have low : Δ ⊢[PRAAx] le (Mn f (Syn.shift K) (Syn.shift x)) (Syn.shift z) :=
    le_trans (min_le f (Syn.shift K) (Syn.shift x) (var 0) (Prf.andE₁ hw)) (Prf.andE₂ hw)
  simpa only [Fm.shift, subst_le, subst_ap2, Syn.shift, P, Δ] using low

/-- For every j ≤ H, some i ≤ K satisfies f(i,x) ≤ g(j,y) + error. -/
def covers (f g : PR 2) (K H x y error : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift H) ⟶
    someBelow f (Syn.shift K) (Syn.shift x)
      (ap2 g (var 0) (Syn.shift y) + Syn.shift error))

theorem transfer (f g : PR 2) (K H x y error : PTm n)
    (cover : Γ ⊢[PRAAx] covers f g K H x y error) :
    Γ ⊢[PRAAx] le (Mn f K x) (Mn g H y + error) := by
  apply lower_fold
  refine .allI (.impI ?_)
  have matched := Prf.impE cover.allOpen.wk Prf.hyp0
  have low := minimum_below f (Syn.shift K) (Syn.shift x) _ matched
  simpa only [Syn.shift, subst_ap2] using low

/-- Variable slots 0 through 4 are K,H,x,y,error. -/
def sentenceBody (f g : PR 2) : Fm PTm 5 :=
  covers f g (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
    le (Mn f (var 0) (var 2)) (Mn g (var 1) (var 3) + var 4)

/-- The full closed arithmetic sentence, schematic only in the two programs. -/
theorem transfer_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (sentenceBody f g) :=
  closeUniv 5 (.impI (transfer f g _ _ _ _ _ Prf.hyp0))

/-- Two directed covers give both additive inequalities under one closure. -/
def symmetricBody (f g : PR 2) : Fm PTm 5 :=
  let K := var 0
  let H := var 1
  let x := var 2
  let y := var 3
  let e := var 4
  (covers f g K H x y e ⋏ covers g f H K y x e) ⟶
    (le (Mn f K x) (Mn g H y + e) ⋏ le (Mn g H y) (Mn f K x + e))

theorem symmetric_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (symmetricBody f g) :=
  closeUniv 5 (.impI (.andI (transfer f g _ _ _ _ _ (.andE₁ Prf.hyp0))
    (transfer g f _ _ _ _ _ (.andE₂ Prf.hyp0))))


end LeanProofs.IPRA.Foundations.FiniteObservations.UniformMinimum

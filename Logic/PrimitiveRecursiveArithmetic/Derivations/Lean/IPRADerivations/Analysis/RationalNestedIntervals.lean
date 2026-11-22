import IPRADerivations.Analysis.RationalConvexFiniteModulus
import IPRADerivations.Analysis.RationalCubeInfimumName
import IPRADerivations.Analysis.GapRemoval

/-!
# The nested rational interval presentation of the convexity packet

Every endpoint is read from the original primitive-recursive presentation.
Adjacent nesting implies arbitrary finite nesting. Midpoints form the
original sampler, and a finite positivity witness persists under refinement.
The center definition of order implies each exact cross-endpoint comparison,
by a computed precision that removes the possible rational gap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNestedIntervals

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters (midpoint)
open RationalArgmin (rationalLE reflexive transitive rationalLE_congr)
open RationalValueBounds (upper radius crossLeft)
open RationalCubeGrid (scale scale_positive)
open RationalConvexFiniteModulus (eps eps_nonnegative)
open RationalConvexSecants (nonnegative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def read (f : PR 3) (q p x : PTm n) : PTm n := ap3 f q p x
def center (L U : PR 3) (q p x : PTm n) : PTm n := midpoint (read L q p x) (read U q p x)
def centerF (L U : PR 3) : PR 3 := PTm.toPR (center L U (var 0) (var 1) (var 2))

def intervalStep (L U : PR 3) (q p x : PTm n) : Fm PTm n :=
  rationalLE (read L q p x) (read L q (succ p) x) ⋏
    (rationalLE (read L q (succ p) x) (read U q (succ p) x) ⋏
      (rationalLE (read U q (succ p) x) (read U q p x) ⋏
        upper (read U q p x) (read L q p x) one (scale p)))

def regular (L U : PR 3) (q x : PTm n) : Fm PTm n :=
  .all (intervalStep L U (Syn.shift q) (var 0) (Syn.shift x))

def positiveWitness (L : PR 3) (q p s x : PTm n) : Fm PTm n := rationalLE (eps s) (read L q p x)

def nested (L U : PR 3) (q p r x : PTm n) : Fm PTm n :=
  rationalLE (read L q p x) (read L q r x) ⋏ rationalLE (read U q r x) (read U q p x)

def centerOrder (L U J K : PR 3) (q z x : PTm n) : Fm PTm n :=
  .all (upper (center L U (Syn.shift q) (succ (succ (var 0))) (Syn.shift x))
    (center J K (Syn.shift z) (succ (succ (var 0))) (Syn.shift x)) one (scale (var 0)))

@[simp] theorem subst_read {m : ℕ} (σ : Fin n → PTm m) (f : PR 3) (q p x : PTm n) :
    Syn.subst σ (read f q p x) = read f (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ x) := by simp [read]
@[simp] theorem subst_center {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (q p x : PTm n) :
    Syn.subst σ (center L U q p x) = center L U (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ x) := by simp [center]
@[simp] theorem subst_intervalStep {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (q p x : PTm n) :
    (intervalStep L U q p x).subst σ = intervalStep L U (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ x) := by
  simp [intervalStep,scale]
@[simp] theorem subst_regular {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (q x : PTm n) :
    (regular L U q x).subst σ = regular L U (Syn.subst σ q) (Syn.subst σ x) := by
  simp [regular,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_nested {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (q p r x : PTm n) :
    (nested L U q p r x).subst σ = nested L U (Syn.subst σ q) (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ x) := by
  simp [nested]

theorem center_at (L U : PR 3) (q p x : PTm n) :
    Γ ⊢[PRAAx] RationalConvexEndpointBudget.sample (centerF L U) q p x ≐ center L U q p x := by
  simpa only [RationalConvexEndpointBudget.sample,centerF,ap3,subst_center,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (center L U (var 0) (var 1) (var 2) : PTm 3) ![q,p,x]

theorem step_at (L U : PR 3) (q p x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x) :
    Γ ⊢[PRAAx] intervalStep L U q p x := by
  simpa only [regular,subst_intervalStep,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem ordered (L U : PR 3) (q p x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x) :
    Γ ⊢[PRAAx] rationalLE (read L q p x) (read U q p x) := by
  have hs := step_at L U q p x h
  exact transitive hs.andE₁ (transitive hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁)

theorem nesting_by_offset (L U : PR 3) (q p r x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x) :
    Γ ⊢[PRAAx] nested L U q p (p+r) x := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] regular L U (Syn.shift q) (Syn.shift x) := by
    simpa only [Fm.shift,subst_regular,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (nested L U (Syn.shift q) (Syn.shift p) (Syn.shift p+var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (by unfold nested rationalLE; exact ⟨le_QF _ _,le_QF _ _⟩) ?_ ?_
    · simp only [subst_nested,PTm.subst_add,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero]
      exact .andI (rationalLE_congr (.eqRefl _) (congrAp3 L (.eqRefl _) (add_zero p).eqSymm (.eqRefl _))
        (reflexive _))
        (rationalLE_congr (congrAp3 U (.eqRefl _) (add_zero p).eqSymm (.eqRefl _)) (.eqRefl _)
          (reflexive _))
    · simp only [subst_nested,PTm.subst_add,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let t := Syn.shift p+var 0
      have hi : nested L U (Syn.shift q) (Syn.shift p) t (Syn.shift x) :: Γ.map Fm.shift ⊢[PRAAx]
          nested L U (Syn.shift q) (Syn.shift p) t (Syn.shift x) := Prf.hyp0
      let Δ := nested L U (Syn.shift q) (Syn.shift p) t (Syn.shift x) :: Γ.map Fm.shift
      have hstep : Δ ⊢[PRAAx] intervalStep L U (Syn.shift q) t (Syn.shift x) :=
        step_at L U (Syn.shift q) t (Syn.shift x) hs.wk
      have index := (add_succ (Γ := Δ) (Syn.shift p) (var 0)).eqSymm
      refine .andI (rationalLE_congr (.eqRefl _) (congrAp3 L (.eqRefl _) index (.eqRefl _))
        (transitive hi.andE₁ hstep.andE₁)) ?_
      exact rationalLE_congr (congrAp3 U (.eqRefl _) index (.eqRefl _)) (.eqRefl _)
        (transitive hstep.andE₂.andE₂.andE₁ hi.andE₂)
  simpa only [subst_nested,PTm.subst_add,Syn.subst_inst_shift,Syn.subst_var,Syn.inst_zero] using all.allE r

theorem nesting (L U : PR 3) (q p r x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x)
    (hp : Γ ⊢[PRAAx] le p r) : Γ ⊢[PRAAx] nested L U q p r x := by
  have result := nesting_by_offset L U q p (monus r p) x h
  have e := (eq_add_of_le hp).eqSymm
  exact .andI (rationalLE_congr (.eqRefl _) (congrAp3 L (.eqRefl _) e (.eqRefl _)) result.andE₁)
    (rationalLE_congr (congrAp3 U (.eqRefl _) e (.eqRefl _)) (.eqRefl _) result.andE₂)

theorem center_in_interval (L U : PR 3) (q p r x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] rationalLE (read L q p x) (center L U q r x) ⋏
      rationalLE (center L U q r x) (read U q p x) := by
  have hn := nesting L U q p r x h hp
  have ho := ordered L U q r x h
  exact .andI (transitive hn.andE₁ (RationalCubeInfimumName.midpoint_lower _ _ ho))
    (transitive (RationalCubeInfimumName.midpoint_upper _ _ ho) hn.andE₂)

theorem center_later_radius (L U : PR 3) (q p r x : PTm n)
    (h : Γ ⊢[PRAAx] regular L U q x) (hp : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] radius (center L U q p x) (center L U q r x) one (scale p) := by
  have c := center_in_interval L U q p p x h (le_refl p)
  have d := center_in_interval L U q p r x h hp
  have w := RationalValueBounds.radius_of_upper _ _ _ _
    (step_at L U q p x h).andE₂.andE₂.andE₂
    (RationalValueBounds.upper_of_order _ _ _ _ (ordered L U q p x h))
  exact RationalCubeInfimumName.interval_radius _ _ _ _ _ _ c.andE₁ c.andE₂ d.andE₁ d.andE₂ w

theorem endpoint_regular (L U : PR 3) (q p x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x) :
    Γ ⊢[PRAAx] RationalConvexFiniteModulus.endpointRegular (centerF L U) q p x := by
  have hr := center_later_radius L U q zero p x h (zero_le _)
  have hu := RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ hr)
  have hp : Γ ⊢[PRAAx] le (one*scale p) ((scale p+one)*scale zero) := by
    exact le_congr (one_mul _).eqSymm
      ((show Γ ⊢[PRAAx] (scale p+one) ≐ (scale p+one)*one by ipra_ring).eqTrans
        (congrMul (.eqRefl _) (pw_zero two).eqSymm)) (le_add_right _ _)
  exact RationalValueBounds.upper_congr (center_at L U q p x).eqSymm (center_at L U q zero x).eqSymm
    (.eqRefl _) (.eqRefl _) (RationalValueBounds.upper_mono _ _ _ _ _ _ (scale_positive zero) hu hp)

theorem center_of_positive (L U : PR 3) (q p r s x : PTm n) (h : Γ ⊢[PRAAx] regular L U q x)
    (hp : Γ ⊢[PRAAx] positiveWitness L q p s x) (hr : Γ ⊢[PRAAx] le p r) :
    Γ ⊢[PRAAx] nonnegative (center L U q r x) :=
  transitive (eps_nonnegative s) (transitive hp (center_in_interval L U q p r x h hr).andE₁)

theorem center_order_at (L U J K : PR 3) (q z x k : PTm n) (h : Γ ⊢[PRAAx] centerOrder L U J K q z x) :
    Γ ⊢[PRAAx] upper (center L U q (succ (succ k)) x) (center J K z (succ (succ k)) x) one (scale k) := by
  simpa [centerOrder,scale] using h.allE k

theorem order_reflects_endpoints (L U J K : PR 3) (q z p r x : PTm n)
    (hl : Γ ⊢[PRAAx] regular L U q x) (hr : Γ ⊢[PRAAx] regular J K z x)
    (h : Γ ⊢[PRAAx] centerOrder L U J K q z x) : Γ ⊢[PRAAx] rationalLE (read L q p x) (read K z r x) := by
  let a := read L q p x
  let b := read K z r x
  let C := RationalSupMetric.denominatorOf a*RationalSupMetric.denominatorOf b
  let k := C+p+r
  let j := succ (succ k)
  have hk : Γ ⊢[PRAAx] le C k := by dsimp [k]; ipra_le 𝔟 p+𝔟 r
  have hp : Γ ⊢[PRAAx] le p j := by dsimp [j,k]; ipra_le 𝔟 C+𝔟 r+2
  have hq : Γ ⊢[PRAAx] le r j := by dsimp [j,k]; ipra_le 𝔟 C+𝔟 p+2
  have ha := (center_in_interval L U q p j x hl hp).andE₁
  have hb := (center_in_interval J K z r j x hr hq).andE₂
  have hu := RationalValueBounds.upper_order_left _ _ _ _ _ ha
    (RationalValueBounds.upper_order_right _ _ _ _ _ (center_order_at L U J K q z x k h) hb)
  have hsmall : Γ ⊢[PRAAx] lt C (scale k) :=
    lt_of_le_of_lt hk (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) k)
  have raw : Γ ⊢[PRAAx] le (crossLeft a b*pw two k) (crossLeft b a*pw two k+C) :=
    le_congr (mul_comm _ _) (by dsimp [C,a,b,scale]; ipra_ring) hu
  exact GapRemoval.gap_of hsmall raw

theorem actual_nested_intervals_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (regular L U (var 0) (var 3) ⟶ le (var 1) (var 2) ⟶ nested L U (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (nesting L U _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_nested_center_sample_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalConvexEndpointBudget.sample (centerF L U) (var 0) (var 1) (var 2) ≐ center L U (var 0) (var 1) (var 2)) :=
  closeUniv 3 (center_at L U _ _ _)

theorem actual_nested_endpoint_regular_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (regular L U (var 0) (var 2) ⟶ RationalConvexFiniteModulus.endpointRegular (centerF L U) (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (endpoint_regular L U _ _ _ Prf.hyp0))

theorem actual_nested_center_positive_closed (L U : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (regular L U (var 0) (var 4) ⟶ positiveWitness L (var 0) (var 1) (var 2) (var 4) ⟶ le (var 1) (var 3) ⟶
      nonnegative (center L U (var 0) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (center_of_positive L U _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_center_order_reflects_endpoints_closed (L U J K : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((regular L U (var 0) (var 4) ⋏ regular J K (var 1) (var 4)) ⟶
      centerOrder L U J K (var 0) (var 1) (var 4) ⟶
      rationalLE (read L (var 0) (var 2) (var 4)) (read K (var 1) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (order_reflects_endpoints L U J K _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalNestedIntervals
